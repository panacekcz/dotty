package dotty.tools
package dotc
package core
package classfile

import dotty.tools.tasty.{ TastyReader, TastyHeaderUnpickler }

import Contexts._, Symbols._, Types._, Names._, StdNames._, NameOps._, Scopes._, Decorators._
import SymDenotations._, unpickleScala2.Scala2Unpickler._, Constants._, Annotations._, util.Spans._
import NameKinds.DefaultGetterName
import ast.tpd._, util._
import java.io.{ ByteArrayInputStream, ByteArrayOutputStream, DataInputStream, IOException }

import java.lang.Integer.toHexString
import java.net.URLClassLoader
import java.util.UUID

import scala.collection.immutable
import scala.collection.mutable.{ ListBuffer, ArrayBuffer }
import scala.annotation.switch
import typer.Checking.checkNonCyclic
import io.{AbstractFile, PlainFile, ZipArchive}
import scala.util.control.NonFatal

object ClassfileParser {
  /** Marker trait for unpicklers that can be embedded in classfiles. */
  trait Embedded

  /** Indicate that there is nothing to unpickle and the corresponding symbols can
    * be invalidated. */
  object NoEmbedded extends Embedded

  /** Replace raw types with wildcard applications */
  def cook(implicit ctx: Context): TypeMap = new TypeMap {
    def apply(tp: Type): Type = tp match {
      case tp: TypeRef if tp.symbol.typeParams.nonEmpty =>
        AppliedType(tp, tp.symbol.typeParams.map(Function.const(TypeBounds.empty)))
      case tp @ AppliedType(tycon, args) =>
        // disregard tycon itself, but map over it to visit the prefix
        tp.derivedAppliedType(mapOver(tycon), args.mapConserve(this))
      case tp @ TempPolyType(_, tpe) =>
        val tpe1 = this(tpe)
        if (tpe1 eq tpe) tp else tp.copy(tpe = tpe1)
      case tp @ TempClassInfoType(parents, _, _) =>
        val parents1 = parents.mapConserve(this)
        if (parents eq parents1) tp else tp.copy(parentTypes = parents1)
      case _ =>
        mapOver(tp)
    }
  }

  case class AnnotationPath(tag: Int, index1: Int, index2: Int, revPath: List[(Int, Int)]){
    def inType(kind: Int, param:Int = 0) = AnnotationPath(tag, index1, index2, (kind, param) :: revPath)
    def inTarget(tag: Int, index1: Int = 0, index2: Int = 0) = AnnotationPath(tag, index1, index2, Nil)
    def withRevPath(revPath: List[(Int, Int)]) = AnnotationPath(tag, index1, index2, revPath)
  }
  object TypeAnnotations {
    val empty = new TypeAnnotations
  }
  class TypeAnnotations {
    val map: scala.collection.mutable.HashMap[AnnotationPath, List[Annotation]] = scala.collection.mutable.HashMap.empty
    def root = AnnotationPath(0, 0, 0, Nil)
    def annotations(path: AnnotationPath): List[Annotation] = map.getOrElse(path, Nil)
    def add(path: AnnotationPath, annot: Annotation): Unit = map.update(path, annot :: annotations(path))
    def isEmpty = map.isEmpty
  }
}

class ClassfileParser(
    classfile: AbstractFile,
    classRoot: ClassDenotation,
    moduleRoot: ClassDenotation)(ictx: Context) {

  //println(s"parsing ${classRoot.name.debugString} ${moduleRoot.name.debugString}")

  import ClassfileConstants._
  import ClassfileParser._

  protected val in: AbstractFileReader = new AbstractFileReader(classfile)

  protected val staticModule: Symbol = moduleRoot.sourceModule(ictx)

  protected val instanceScope: MutableScope = newScope     // the scope of all instance definitions
  protected val staticScope: MutableScope = newScope       // the scope of all static definitions
  protected var pool: ConstantPool = _              // the classfile's constant pool

  protected var currentClassName: SimpleName = _      // JVM name of the current class
  protected var classTParams: Map[Name, Symbol] = Map()

  private var Scala2UnpicklingMode = Mode.Scala2Unpickling

  classRoot.info = NoLoader().withDecls(instanceScope)
  moduleRoot.info = NoLoader().withDecls(staticScope).withSourceModule(_ => staticModule)

  private def currentIsTopLevel(implicit ctx: Context) = classRoot.owner.is(Flags.PackageClass)

  private def mismatchError(className: SimpleName) =
    throw new IOException(s"class file '${in.file.canonicalPath}' has location not matching its contents: contains class $className")

  def run()(implicit ctx: Context): Option[Embedded] = try {
    ctx.debuglog("[class] >> " + classRoot.fullName)
    parseHeader()
    this.pool = new ConstantPool
    parseClass()
  }
  catch {
    case e: RuntimeException =>
      if (ctx.debug) e.printStackTrace()
      throw new IOException(
        i"""class file ${classfile.canonicalPath} is broken, reading aborted with ${e.getClass}
           |${Option(e.getMessage).getOrElse("")}""")
  }

  private def parseHeader(): Unit = {
    val magic = in.nextInt
    if (magic != JAVA_MAGIC)
      throw new IOException(s"class file '${in.file}' has wrong magic number 0x${toHexString(magic)}, should be 0x${toHexString(JAVA_MAGIC)}")
    val minorVersion = in.nextChar.toInt
    val majorVersion = in.nextChar.toInt
    if ((majorVersion < JAVA_MAJOR_VERSION) ||
        ((majorVersion == JAVA_MAJOR_VERSION) &&
         (minorVersion < JAVA_MINOR_VERSION)))
      throw new IOException(
        s"class file '${in.file}' has unknown version $majorVersion.$minorVersion, should be at least $JAVA_MAJOR_VERSION.$JAVA_MINOR_VERSION")
  }

  /** Return the class symbol of the given name. */
  def classNameToSymbol(name: Name)(implicit ctx: Context): Symbol = innerClasses.get(name) match {
    case Some(entry) => innerClasses.classSymbol(entry)
    case None => ctx.requiredClass(name)
  }

  var sawPrivateConstructor: Boolean = false

  /** Creates a TypeRef to sym, where the prefix is annotated with type annotations from typeAnnots starting at path.
    * Non-module-class prefixes are widened.
    * Returns the TypeRef and path to annotations that apply to the sym type.
    */
  def typeRefWithAnnotsOnPrefix(sym: Symbol, typeAnnots: TypeAnnotations, path: AnnotationPath)(implicit ctx: Context): (Type, AnnotationPath) = {
    if (sym.owner.flagsUNSAFE.is(Flags.Module))
      (sym.typeRef, path)
    else {
      val (ownerTypeRef, symAnnotPath) = typeRefWithAnnots(sym.owner, typeAnnots, path)
      (TypeRef(ownerTypeRef, sym), symAnnotPath)
    }
  }

  /** Creates a TypeRef to sym, annotated with type annotations from typeAnnots starting at path.
    * Non-module-class prefixes are widened.
    * Returns the TypeRef and path to annotations that apply to members of the type.
    */
  def typeRefWithAnnots(symbol: Symbol, typeAnnots: TypeAnnotations, path: AnnotationPath)(implicit ctx: Context): (Type, AnnotationPath) = {
    def annotateTypeRef(tr: TypeRef, original: Type): (Type, AnnotationPath) = {
      val sym = tr.symbol
      if (sym.flagsUNSAFE.is(Flags.Module)){
        // Prefix of module-owned classes refers to module, so should not be annotated and widened
        (original, path)// Prefix is not widened
      }
      else {
        // Prefix is a class, so should be annotated and widened
        val prefix = tr.prefix
        val (annotatedPrefix, pathFromPrefix) =  prefix.widen match {
          case widenedPrefix: TypeRef =>
            annotateTypeRef(widenedPrefix, prefix)
          case tp => // tp can be AppliedType when inheriting from a inner class of a generic class - in that case, signature is not generated
            (tp, path)
        }
        val refWithAnnotatedPrefix = TypeRef(annotatedPrefix, sym)
        val annotatedRef = AnnotatedType.make(refWithAnnotatedPrefix, typeAnnots.annotations(pathFromPrefix))
        (annotatedRef, pathFromPrefix.inType(TYPE_PATH_NESTED))
      }
    }
    val tr = symbol.typeRef
    annotateTypeRef(tr, tr)
  }

  def parseClass()(implicit ctx: Context): Option[Embedded] = {
    val jflags       = in.nextChar
    val isAnnotation = hasAnnotation(jflags)
    val sflags       = classTranslation.flags(jflags)
    val isEnum       = (jflags & JAVA_ACC_ENUM) != 0
    val nameIdx      = in.nextChar
    currentClassName = pool.getClassName(nameIdx)

    if (currentIsTopLevel &&
        currentClassName != classRoot.fullName.toSimpleName &&
        currentClassName != classRoot.fullName.encode.toSimpleName)
      mismatchError(currentClassName)

    addEnclosingTParams()

    /** Parse parents for Java classes. For Scala, return AnyRef, since the real type will be unpickled.
     *  Updates the read pointer of 'in'. */
    def parseParents(typeAnnots: TypeAnnotations): List[Type] = {
      def parseParent(parentTypeAnnotIndex: Int) = {
        val superClass = pool.getSuperClass(in.nextChar)
        val (tp, _) = typeRefWithAnnots(superClass, typeAnnots, typeAnnots.root.inTarget(TARGET_PARENT, parentTypeAnnotIndex))
        tp
      }

      val superType =
        if (isAnnotation) {
          in.nextChar
          defn.AnnotationClass.typeRef
        }
        else if (classRoot.symbol == defn.ComparableClass ||
                 classRoot.symbol == defn.JavaCloneableClass ||
                 classRoot.symbol == defn.JavaSerializableClass) {
          // Treat these interfaces as universal traits
          in.nextChar
          defn.AnyType
        }
        else {
          parseParent(65535)
        }
      val ifaceCount = in.nextChar
      var ifaces = for (i <- (0 until ifaceCount).toList) yield parseParent(i)
        // Dotty deviation: was
        //    var ifaces = for (i <- List.range(0, ifaceCount)) ...
        // This does not typecheck because the type parameter of List is now lower-bounded by Int | Char.
        // Consequently, no best implicit for the "Integral" evidence parameter of "range"
        // is found. Previously, this worked because of weak conformance, which has been dropped.

      if (isAnnotation) ifaces = defn.ClassfileAnnotationClass.typeRef :: ifaces
      superType :: ifaces
    }

    val result = unpickleOrParseInnerClasses()
    if (!result.isDefined) {
      val parentsBp = in.bp
      def parseClassType(typeAnnots: TypeAnnotations): Type =
        TempClassInfoType(parseParents(typeAnnots), instanceScope, classRoot.symbol)
      def reparseClassType(typeAnnots: TypeAnnotations): Type = {
        val oldBp = in.bp
        in.bp = parentsBp
        val result = parseClassType(typeAnnots)
        in.bp = oldBp
        result
      }

      var classInfo: Type = parseClassType(TypeAnnotations.empty)
      // might be reassigned by later parseAttributes
      val staticInfo = TempClassInfoType(List(), staticScope, moduleRoot.symbol)

      enterOwnInnerClasses()

      classRoot.setFlag(sflags)
      moduleRoot.setFlag(Flags.JavaDefined | Flags.ModuleClassCreationFlags)

      val privateWithin = getPrivateWithin(jflags)

      classRoot.setPrivateWithin(privateWithin)
      moduleRoot.setPrivateWithin(privateWithin)
      moduleRoot.sourceModule.setPrivateWithin(privateWithin)

      for (i <- 0 until in.nextChar) parseMember(method = false)
      for (i <- 0 until in.nextChar) parseMember(method = true)
      classInfo = parseAttributes(classRoot.symbol, classInfo, reparseClassType)
      if (isAnnotation)
        // classInfo must be a TempClassInfoType and not a TempPolyType,
        // because Java annotations cannot have type parameters.
        addAnnotationConstructor(classInfo.asInstanceOf[TempClassInfoType])

      classRoot.registerCompanion(moduleRoot.symbol)
      moduleRoot.registerCompanion(classRoot.symbol)

      setClassInfo(classRoot, classInfo, fromScala2 = false)
      setClassInfo(moduleRoot, staticInfo, fromScala2 = false)
    }
    else if (result == Some(NoEmbedded))
      for (sym <- List(moduleRoot.sourceModule, moduleRoot.symbol, classRoot.symbol)) {
        classRoot.owner.asClass.delete(sym)
        if (classRoot.owner == defn.ScalaShadowingPackage.moduleClass)
          // Symbols in scalaShadowing are also added to scala
          defn.ScalaPackageClass.delete(sym)
        sym.markAbsent()
      }

    // eager load enum definitions for exhaustivity check of pattern match
    if (isEnum) {
      instanceScope.toList.map(_.ensureCompleted())
      staticScope.toList.map(_.ensureCompleted())
    }

    result
  }

  /** Add type parameters of enclosing classes */
  def addEnclosingTParams()(implicit ctx: Context): Unit = {
    var sym = classRoot.owner
    while (sym.isClass && !sym.is(Flags.ModuleClass)) {
      for (tparam <- sym.typeParams)
        classTParams = classTParams.updated(tparam.name, tparam)
      sym = sym.owner
    }
  }

  def parseMember(method: Boolean)(implicit ctx: Context): Unit = {
    val start = indexCoord(in.bp)
    val jflags = in.nextChar
    val sflags =
      if (method) Flags.Method | methodTranslation.flags(jflags)
      else fieldTranslation.flags(jflags)
    val name = pool.getName(in.nextChar)
    if (!sflags.is(Flags.Private) || name == nme.CONSTRUCTOR) {
      val member = ctx.newSymbol(
        getOwner(jflags), name, sflags, memberCompleter,
        getPrivateWithin(jflags), coord = start)
      getScope(jflags).enter(member)
    }
    // skip rest of member for now
    in.nextChar // info
    skipAttributes()
  }

  val memberCompleter: LazyType = new LazyType {

    def complete(denot: SymDenotation)(implicit ctx: Context): Unit = {
      val oldbp = in.bp
      try {
        in.bp = denot.symbol.coord.toIndex
        val sym = denot.symbol
        val jflags = in.nextChar
        val isEnum = (jflags & JAVA_ACC_ENUM) != 0
        val name = pool.getName(in.nextChar)
        val isConstructor = name eq nme.CONSTRUCTOR

        /** Strip leading outer param from constructor and trailing access tag for
         *  private inner constructors.
         */
        def normalizeConstructorParams() = innerClasses.get(currentClassName) match {
          case Some(entry) if !isStatic(entry.jflags) =>
            val mt @ MethodTpe(paramNames, paramTypes, resultType) = denot.info
            var normalizedParamNames = paramNames.tail
            var normalizedParamTypes = paramTypes.tail
            if ((jflags & JAVA_ACC_SYNTHETIC) != 0) {
              // SI-7455 strip trailing dummy argument ("access constructor tag") from synthetic constructors which
              // are added when an inner class needs to access a private constructor.
              normalizedParamNames = paramNames.dropRight(1)
              normalizedParamTypes = paramTypes.dropRight(1)
            }
            denot.info = mt.derivedLambdaType(normalizedParamNames, normalizedParamTypes, resultType)
          case _ =>
        }

        /** Make return type of constructor be the enclosing class type,
         *  and make constructor type polymorphic in the type parameters of the class
         */
        def normalizeConstructorInfo() = {
          val rt = classRoot.typeRef appliedTo (classRoot.typeParams map (_.typeRef))

          def resultType(tpe: Type): Type = tpe match {
            case mt @ MethodType(paramNames) => mt.derivedLambdaType(paramNames, mt.paramInfos, rt)
            case pt : PolyType => pt.derivedLambdaType(pt.paramNames, pt.paramInfos, resultType(pt.resType))
          }

          denot.info = resultType(denot.info)
          addConstructorTypeParams(denot)
        }

        val typeIndex = in.nextChar
        denot.info = pool.getType(typeIndex, TypeAnnotations.empty)
        if (isEnum) denot.info = ConstantType(Constant(sym))
        if (isConstructor) normalizeConstructorParams()
        denot.info = translateTempPoly(parseAttributes(sym, denot.info, typeAnnots => pool.getType(typeIndex, typeAnnots)))
        if (isConstructor) normalizeConstructorInfo()

        if (denot.is(Flags.Method) && (jflags & JAVA_ACC_VARARGS) != 0)
          denot.info = arrayToRepeated(denot.info)

        if (ctx.explicitNulls) denot.info = JavaNullInterop.nullifyMember(denot.symbol, denot.info, isEnum)

        // seal java enums
        if (isEnum) {
          val enumClass = sym.owner.linkedClass
          if (!enumClass.exists)
            ctx.warning(s"no linked class for java enum $sym in ${sym.owner}. A referencing class file might be missing an InnerClasses entry.")
          else {
            if (!enumClass.is(Flags.Sealed)) enumClass.setFlag(Flags.AbstractSealed)
            enumClass.addAnnotation(Annotation.Child(sym, NoSpan))
          }
        }
      }
      finally
        in.bp = oldbp
    }
  }

  /** Map direct references to Object to references to Any */
  final def objToAny(tp: Type)(implicit ctx: Context): Type =
    if (tp.isDirectRef(defn.ObjectClass) && !ctx.phase.erasedTypes) defn.AnyType else tp

  private def sigToType(sig: SimpleName, typeAnnots: TypeAnnotations, owner: Symbol = null)(implicit ctx: Context): Type = {
    val annotPath = typeAnnots.root.inTarget(TARGET_FIELD)
    var index = 0
    val end = sig.length
    def accept(ch: Char): Unit = {
      assert(sig(index) == ch, (sig(index), ch))
      index += 1
    }
    def subName(isDelimiter: Char => Boolean): SimpleName = {
      val start = index
      while (!isDelimiter(sig(index))) { index += 1 }
      sig.slice(start, index)
    }

    // Warning: sigToType contains nested completers which might be forced in a later run!
    // So local methods need their own ctx parameters.
    def sig2type(tparams: immutable.Map[Name, Symbol], skiptvs: Boolean, annotPath: AnnotationPath)(implicit ctx: Context): Type = {
      val tag = sig(index); index += 1
      val tp = (tag: @switch) match {
        case BYTE_TAG   => defn.ByteType
        case CHAR_TAG   => defn.CharType
        case DOUBLE_TAG => defn.DoubleType
        case FLOAT_TAG  => defn.FloatType
        case INT_TAG    => defn.IntType
        case LONG_TAG   => defn.LongType
        case SHORT_TAG  => defn.ShortType
        case VOID_TAG   => defn.UnitType
        case BOOL_TAG   => defn.BooleanType
        case 'L' =>
          def processInner(tp: Type): Type = tp match {
            case tp: TypeRef if !tp.symbol.owner.is(Flags.ModuleClass) =>
              TypeRef(processInner(tp.prefix.widen), tp.symbol.asType)
            case _ =>
              tp
          }
          def processClassType(tp: Type, annotPath: AnnotationPath): Type = {
            val applied = tp match {
              case tp: TypeRef =>
                if (sig(index) == '<') {
                  accept('<')
                  val argsBuf = if (skiptvs) null else new ListBuffer[Type]
                  var argIndex = 0
                  while (sig(index) != '>') {
                    val argumentPath = annotPath.inType(TYPE_PATH_ARGUMENT, argIndex)
                    def paramType(path: AnnotationPath) = sig2type(tparams, skiptvs, path)

                    val arg = sig(index) match {
                      case variance @ ('+' | '-' | '*') =>
                        // TODO: how to handle annotation on wildcard?
                        // according to https://checkerframework.org/manual/#generics-instantiation,
                        // we can apply it to the other bound.
                        // However, it would not have the same behavior with respect to default (cf distinguishes explicit and implicit bound)
                        index += 1
                        variance match {
                          case '+' => objToAny(TypeBounds.upper(paramType(argumentPath.inType(TYPE_PATH_BOUND, argIndex))))
                          case '-' =>
                            val tp = paramType(argumentPath.inType(TYPE_PATH_BOUND, argIndex))
                            // sig2type seems to return AnyClass regardless of the situation:
                            // we don't want Any as a LOWER bound.
                            if (tp.isDirectRef(defn.AnyClass)) TypeBounds.empty
                            else TypeBounds.lower(tp)
                          case '*' => TypeBounds.empty
                        }
                      case _ => paramType(argumentPath)
                    }
                    if (argsBuf != null) argsBuf += arg
                    argIndex += 1
                  }
                  accept('>')
                  if (skiptvs) tp else tp.appliedTo(argsBuf.toList)
                }
                else tp
              case tp =>
                // TODO: does this ever happen?
                assert(sig(index) != '<', tp)
                tp
            }
            AnnotatedType.make(applied, typeAnnots.annotations(annotPath))
          }
          val classSym = classNameToSymbol(subName(c => c == ';' || c == '<'))
          var (tpe, classAnnotPath) = typeRefWithAnnotsOnPrefix(classSym, typeAnnots, annotPath)
          tpe = processClassType(processInner(tpe), classAnnotPath)
          while (sig(index) == '.') {
            accept('.')
            val name = subName(c => c == ';' || c == '<' || c == '.').toTypeName
            val clazz = tpe.member(name).symbol
            classAnnotPath = classAnnotPath.inType(TYPE_PATH_NESTED)
            tpe = processClassType(processInner(TypeRef(tpe, clazz)), classAnnotPath)
          }
          accept(';')
          tpe
        case ARRAY_TAG =>
          while ('0' <= sig(index) && sig(index) <= '9') index += 1
          var elemtp = sig2type(tparams, skiptvs, annotPath.inType(TYPE_PATH_ARRAY))
          // make unbounded Array[T] where T is a type variable into Array[T with Object]
          // (this is necessary because such arrays have a representation which is incompatible
          // with arrays of primitive types.
          // NOTE that the comparison to Object only works for abstract types bounded by classes that are strict subclasses of Object
          // if the bound is exactly Object, it will have been converted to Any, and the comparison will fail
          // see also RestrictJavaArraysMap (when compiling java sources directly)
          if (elemtp.typeSymbol.isAbstractOrParamType && !(elemtp.derivesFrom(defn.ObjectClass)))
            elemtp = AndType(elemtp, defn.ObjectType)
          defn.ArrayOf(elemtp)
        case '(' =>
          // we need a method symbol. given in line 486 by calling getType(methodSym, ..)
          val paramtypes = new ListBuffer[Type]()
          var paramnames = new ListBuffer[TermName]()
          var paramIndex = 0
          while (sig(index) != ')') {
            paramnames += nme.syntheticParamName(paramtypes.length)
            paramtypes += objToAny(sig2type(tparams, skiptvs, annotPath.inTarget(TARGET_METHOD_PARAM, paramIndex)))
            paramIndex += 1
          }
          index += 1
          val restype = sig2type(tparams, skiptvs, annotPath.inTarget(TARGET_RESULT))
          JavaMethodType(paramnames.toList, paramtypes.toList, restype)
        case 'T' =>
          val n = subName(';'.==).toTypeName
          index += 1
          //assert(tparams contains n, s"classTparams = $classTParams, tparams = $tparams, key = $n")
          if (skiptvs) defn.AnyType else tparams(n).typeRef
      }
      if (tag == 'L')
        tp // Class types are already annotated
      else
        AnnotatedType.make(tp, typeAnnots.annotations(annotPath))
    }
    // sig2type(tparams, skiptvs)

    def sig2typeBounds(tparams: immutable.Map[Name, Symbol], skiptvs: Boolean, paramIndex: Int, owner: Symbol)(implicit ctx: Context): Type = {
      val ts = new ListBuffer[Type]
      var boundIndex = 0
      while (sig(index) == ':') {
        index += 1
        if (sig(index) != ':') // guard against empty class bound
          ts += objToAny(sig2type(tparams, skiptvs, annotPath.inTarget(if (owner.isTerm) TARGET_METHOD_BOUND else TARGET_CLASS_BOUND, paramIndex, boundIndex)))
        boundIndex += 1
      }
      TypeBounds.upper(ts.foldLeft(NoType: Type)(_ & _) orElse defn.AnyType)
    }

    var tparams = classTParams

    def typeParamCompleter(start: Int, paramIndex: Int) = new LazyType {
      def complete(denot: SymDenotation)(implicit ctx: Context): Unit = {
        val savedIndex = index
        try {
          index = start
          denot.info =
            checkNonCyclic( // we need the checkNonCyclic call to insert LazyRefs for F-bounded cycles
                denot.symbol,
                sig2typeBounds(tparams, skiptvs = false, paramIndex, denot.owner),
                reportErrors = false)
        }
        finally
          index = savedIndex
      }
    }

    val newTParams = new ListBuffer[Symbol]()
    if (sig(index) == '<') {
      assert(owner != null)
      index += 1
      val start = index
      var paramIndex = 0
      while (sig(index) != '>') {
        val tpname = subName(':'.==).toTypeName
        val s = ctx.newSymbol(
          owner, tpname, owner.typeParamCreationFlags,
          typeParamCompleter(index, paramIndex), coord = indexCoord(index))
        if (owner.isClass) owner.asClass.enter(s)
        val paramPath = annotPath.inTarget(if (owner.isTerm) TARGET_METHOD_TYPE_PARAM else TARGET_CLASS_TYPE_PARAM, paramIndex)
        s.addAnnotations(typeAnnots.annotations(paramPath))
        tparams = tparams + (tpname -> s)
        sig2typeBounds(tparams, skiptvs = true, paramIndex, owner)
        newTParams += s
        paramIndex += 1
      }
      index += 1
    }
    val ownTypeParams = newTParams.toList.asInstanceOf[List[TypeSymbol]]
    val tpe =
      if ((owner == null) || !owner.isClass)
        sig2type(tparams, skiptvs = false, annotPath)
      else {
        classTParams = tparams
        val parents = new ListBuffer[Type]()
        var parentIndex = 0
        while (index < end) {
          val parentAnnotPath = annotPath.inTarget(TARGET_PARENT, if(parentIndex == 0) 65535 else parentIndex - 1)
          parents += sig2type(tparams, skiptvs = false, parentAnnotPath)  // here the variance doesnt'matter
          parentIndex += 1
        }
        TempClassInfoType(parents.toList, instanceScope, owner)
      }
    if (ownTypeParams.isEmpty) tpe else TempPolyType(ownTypeParams, tpe)
  }
  // sigToType

  def parseAnnotArg(skip: Boolean = false)(implicit ctx: Context): Option[Tree] = {
    val tag = in.nextByte.toChar
    val index = in.nextChar
    tag match {
      case STRING_TAG =>
        if (skip) None else Some(Literal(Constant(pool.getName(index).toString)))
      case BOOL_TAG | BYTE_TAG | CHAR_TAG | SHORT_TAG =>
        if (skip) None else Some(Literal(pool.getConstant(index, tag)))
      case INT_TAG | LONG_TAG | FLOAT_TAG | DOUBLE_TAG =>
        if (skip) None else Some(Literal(pool.getConstant(index)))
      case CLASS_TAG =>
        if (skip) None else Some(Literal(Constant(pool.getType(index, TypeAnnotations.empty))))
      case ENUM_TAG =>
        val t = pool.getType(index, TypeAnnotations.empty)
        val n = pool.getName(in.nextChar)
        val module = t.typeSymbol.companionModule
        val s = module.info.decls.lookup(n)
        if (skip)
          None
        else if (s != NoSymbol)
          Some(Literal(Constant(s)))
        else {
          ctx.warning(s"""While parsing annotations in ${in.file}, could not find $n in enum $module.\nThis is likely due to an implementation restriction: an annotation argument cannot refer to a member of the annotated class (SI-7014).""")
          None
        }
      case ARRAY_TAG =>
        val arr = new ArrayBuffer[Tree]()
        var hasError = false
        for (i <- 0 until index)
          parseAnnotArg(skip) match {
            case Some(c) => arr += c
            case None => hasError = true
          }
        if (hasError) None
        else if (skip) None
        else {
          val elems = arr.toList
          val elemType =
            if (elems.isEmpty) defn.ObjectType
            else ctx.typeComparer.lub(elems.tpes).widen
          Some(JavaSeqLiteral(elems, TypeTree(elemType)))
        }
      case ANNOTATION_TAG =>
        parseAnnotation(index, skip) map (_.tree)
    }
  }

  /** Parse and return a single annotation.  If it is malformed,
   *  return None.
   */
  def parseAnnotation(attrNameIndex: Char, skip: Boolean = false)(implicit ctx: Context): Option[Annotation] = try {
    val attrType = pool.getType(attrNameIndex, TypeAnnotations.empty)
    val nargs = in.nextChar
    val argbuf = new ListBuffer[Tree]
    var hasError = false
    for (i <- 0 until nargs) {
      val name = pool.getName(in.nextChar)
      parseAnnotArg(skip) match {
        case Some(arg) => argbuf += NamedArg(name, arg)
        case None => hasError = !skip
      }
    }
    if (hasError || skip) None
    else Some(Annotation.deferredResolve(attrType, argbuf.toList))
  }
  catch {
    case f: FatalError => throw f // don't eat fatal errors, they mean a class was not found
    case NonFatal(ex) =>
      // We want to be robust when annotations are unavailable, so the very least
      // we can do is warn the user about the exception
      // There was a reference to ticket 1135, but that is outdated: a reference to a class not on
      // the classpath would *not* end up here. A class not found is signaled
      // with a `FatalError` exception, handled above. Here you'd end up after a NPE (for example),
      // and that should never be swallowed silently.
      ctx.warning("Caught: " + ex + " while parsing annotations in " + in.file)
      if (ctx.debug) ex.printStackTrace()

      None // ignore malformed annotations
  }

  def parseAttributes(sym: Symbol, symtype: Type, parseTypeWithAnnots: TypeAnnotations => Type)(implicit ctx: Context): Type = {
    def convertTo(c: Constant, pt: Type): Constant =
      if (pt == defn.BooleanType && c.tag == IntTag)
        Constant(c.value != 0)
      else
        c convertTo pt
    var newType = symtype
    var newSig: SimpleName = null
    val typeAnnots: TypeAnnotations = new TypeAnnotations

    def parseAttribute(): Unit = {
      val attrName = pool.getName(in.nextChar).toTypeName
      val attrLen = in.nextInt
      val end = in.bp + attrLen
      attrName match {
        case tpnme.SignatureATTR =>
          val sig = pool.getExternalName(in.nextChar)
          newSig = sig
        case tpnme.SyntheticATTR =>
          sym.setFlag(Flags.SyntheticArtifact)
        case tpnme.BridgeATTR =>
          sym.setFlag(Flags.Bridge)
        case tpnme.DeprecatedATTR =>
          val msg = Literal(Constant("see corresponding Javadoc for more information."))
          val since = Literal(Constant(""))
          sym.addAnnotation(Annotation(defn.DeprecatedAnnot, msg, since))
        case tpnme.ConstantValueATTR =>
          val c = pool.getConstant(in.nextChar)
          val c1 = convertTo(c, symtype)
          if (c1 ne null) newType = ConstantType(c1)
          else println("failure to convert " + c + " to " + symtype); //debug
        case tpnme.AnnotationDefaultATTR =>
          sym.addAnnotation(Annotation(defn.AnnotationDefaultAnnot, Nil))
        // Java annotations on classes / methods / fields with RetentionPolicy.RUNTIME
        case tpnme.RuntimeVisibleAnnotationATTR
          | tpnme.RuntimeInvisibleAnnotationATTR =>
          parseAnnotations(attrLen)
        // TODO: method parameter annotations are not parsed, because there are no method parameter symbols
        case tpnme.RuntimeVisibleTypeAnnotationATTR
          | tpnme.RuntimeInvisibleTypeAnnotationATTR =>
          parseTypeAnnotations(attrLen)

        // TODO 1: parse runtime visible annotations on parameters
        // case tpnme.RuntimeParamAnnotationATTR

        // TODO 2: also parse RuntimeInvisibleParamAnnotation
        // i.e. java annotations with RetentionPolicy.CLASS?

        case tpnme.ExceptionsATTR =>
          parseExceptions(attrLen)

        case tpnme.CodeATTR =>
          if (sym.owner.isAllOf(Flags.JavaInterface)) {
            sym.resetFlag(Flags.Deferred)
            sym.owner.resetFlag(Flags.PureInterface)
            ctx.log(s"$sym in ${sym.owner} is a java8+ default method.")
          }
          in.skip(attrLen)

        case _ =>
      }
      in.bp = end
    }

    /**
     * Parse the "Exceptions" attribute which denotes the exceptions
     * thrown by a method.
     */
    def parseExceptions(len: Int): Unit = {
      val nClasses = in.nextChar
      for (n <- 0 until nClasses) {
        // FIXME: this performs an equivalent of getExceptionTypes instead of getGenericExceptionTypes (SI-7065)
        val cls = pool.getClassSymbol(in.nextChar.toInt)
        sym.addAnnotation(ThrowsAnnotation(cls.asClass))
      }
    }

    /** Parse a sequence of annotations and attaches them to the
     *  current symbol sym, except for the ScalaSignature annotation that it returns, if it is available. */
    def parseAnnotations(len: Int): Unit = {
      val nAttr = in.nextChar
      for (n <- 0 until nAttr)
        parseAnnotation(in.nextChar) match {
          case Some(annot) =>
            sym.addAnnotation(annot)
          case None =>
        }
    }

    def parseTypeAnnotationTypePath(root: AnnotationPath): AnnotationPath = {
      var pathLength = in.nextByte
      var path = root.revPath
      for(i <- 0.until(pathLength)) {
        var pathElement = (in.nextByte.toInt, in.nextByte.toInt)
        path = pathElement :: path
      }
      root.withRevPath(path)
    }
    def parseTypeAnnotationTargetPath(root: AnnotationPath): AnnotationPath = {
      val targetType = in.nextByte
      val targetPath = targetType match{
        case TARGET_CLASS_TYPE_PARAM | TARGET_METHOD_TYPE_PARAM | TARGET_METHOD_PARAM =>
          root.inTarget(targetType, in.nextByte)
        case TARGET_PARENT | TARGET_THROWS =>
          root.inTarget(targetType, in.nextChar)
        case TARGET_FIELD | TARGET_RESULT | TARGET_RECEIVER =>
          root.inTarget(targetType)
        case TARGET_CLASS_BOUND | TARGET_METHOD_BOUND =>
          root.inTarget(targetType, in.nextByte, in.nextByte)
      }
      parseTypeAnnotationTypePath(targetPath)
    }

    /** Parses a single type annotation and adds it to typeAnnots */
    def parseTypeAnnotation(): Unit = {
      val path = parseTypeAnnotationTargetPath(typeAnnots.root)
      parseAnnotation(in.nextChar) match {
        case Some(annot) =>
          typeAnnots.add (path, annot)
        case _ =>
      }
    }

    /** Parses all type annotations in the attribute */
    def parseTypeAnnotations(len: Int): Unit = {
      val nAttr = in.nextChar
      for (n <- 0 until nAttr)
        parseTypeAnnotation()
    }

    // begin parseAttributes
    for (i <- 0 until in.nextChar)
      parseAttribute()

    if (newSig ne null) {
      newType = sigToType(newSig, typeAnnots, sym)
      if (ctx.debug && ctx.verbose)
        println("" + sym + "; signature = " + newSig + " type = " + newType)
    }
    else if (!typeAnnots.isEmpty) {
      newType = parseTypeWithAnnots(typeAnnots)
    }

    cook.apply(newType)
  }

  /** Annotations in Scala are assumed to get all their arguments as constructor
   *  parameters. For Java annotations we need to fake it by making up the constructor.
   */
  def addAnnotationConstructor(classInfo: TempClassInfoType)(implicit ctx: Context): Unit =
    ctx.newSymbol(
      owner = classRoot.symbol,
      name = nme.CONSTRUCTOR,
      flags = Flags.Synthetic | Flags.JavaDefined | Flags.Method,
      info = new AnnotConstructorCompleter(classInfo)
    ).entered

  class AnnotConstructorCompleter(classInfo: TempClassInfoType) extends LazyType {
    def complete(denot: SymDenotation)(implicit ctx: Context): Unit = {
      val attrs = classInfo.decls.toList.filter(sym => sym.isTerm && sym != denot.symbol)
      val paramNames = attrs.map(_.name.asTermName)
      val paramTypes = attrs.map(_.info.resultType)
      denot.info = MethodType(paramNames, paramTypes, classRoot.typeRef)
    }
  }

  /** Enter own inner classes in the right scope. It needs the scopes to be set up,
   *  and implicitly current class' superclasses.
   */
  private def enterOwnInnerClasses()(implicit ctx: Context): Unit = {
    def className(name: Name): Name = {
      val name1 = name.toSimpleName
      name1.drop(name1.lastIndexOf('.') + 1)
    }

    def enterClassAndModule(entry: InnerClassEntry, file: AbstractFile, jflags: Int) =
      SymbolLoaders.enterClassAndModule(
          getOwner(jflags),
          entry.originalName,
          new ClassfileLoader(file),
          classTranslation.flags(jflags),
          getScope(jflags))

    for (entry <- innerClasses.values) {
      // create a new class member for immediate inner classes
      if (entry.outerName == currentClassName) {
        val file = ctx.platform.classPath.findClassFile(entry.externalName.toString) getOrElse {
          throw new AssertionError(entry.externalName)
        }
        enterClassAndModule(entry, file, entry.jflags)
      }
    }
  }

  // Nothing$ and Null$ were incorrectly emitted with a Scala attribute
  // instead of ScalaSignature before 2.13.0-M2, see https://github.com/scala/scala/pull/5952
  private val scalaUnpickleWhitelist = List(tpnme.nothingClass, tpnme.nullClass)

  /** Parse inner classes. Expects `in.bp` to point to the superclass entry.
   *  Restores the old `bp`.
   *  @return true iff classfile is from Scala, so no Java info needs to be read.
   */
  def unpickleOrParseInnerClasses()(implicit ctx: Context): Option[Embedded] = {
    val oldbp = in.bp
    try {
      skipSuperclasses()
      skipMembers() // fields
      skipMembers() // methods
      val attrs = in.nextChar
      val attrbp = in.bp

      def scan(target: TypeName): Boolean = {
        in.bp = attrbp
        var i = 0
        while (i < attrs && pool.getName(in.nextChar).toTypeName != target) {
          val attrLen = in.nextInt
          in.skip(attrLen)
          i += 1
        }
        i < attrs
      }

      def unpickleScala(bytes: Array[Byte]): Some[Embedded] = {
        val allowed = ctx.settings.Yscala2Unpickler.value

        def failUnless(cond: Boolean) =
          assert(cond,
            s"Unpickling ${classRoot.symbol.showLocated} from ${classRoot.symbol.associatedFile} is not allowed with -Yscala2-unpickler $allowed")

        if (allowed != "always") {
          failUnless(allowed != "never")
          val allowedList = allowed.split(java.io.File.pathSeparator).toList
          val file = classRoot.symbol.associatedFile
          // Using `.toString.contains` isn't great, but it's good enough for a debug flag.
          failUnless(file == null || allowedList.exists(path => file.toString.contains(path)))
        }

        val unpickler = new unpickleScala2.Scala2Unpickler(bytes, classRoot, moduleRoot)(ctx)
        unpickler.run()(ctx.addMode(Scala2UnpicklingMode))
        Some(unpickler)
      }

      def unpickleTASTY(bytes: Array[Byte]): Some[Embedded]  = {
        val unpickler = new tasty.DottyUnpickler(bytes)
        unpickler.enter(roots = Set(classRoot, moduleRoot, moduleRoot.sourceModule))(ctx.withSource(util.NoSource))
        Some(unpickler)
      }

      def parseScalaSigBytes: Array[Byte] = {
        val tag = in.nextByte.toChar
        assert(tag == STRING_TAG, tag)
        pool getBytes in.nextChar
      }

      def parseScalaLongSigBytes: Array[Byte] = {
        val tag = in.nextByte.toChar
        assert(tag == ARRAY_TAG, tag)
        val stringCount = in.nextChar
        val entries =
          for (i <- 0 until stringCount) yield {
            val stag = in.nextByte.toChar
            assert(stag == STRING_TAG, stag)
            in.nextChar.toInt
          }
        pool.getBytes(entries.toList)
      }

      if (scan(tpnme.TASTYATTR)) {
        val attrLen = in.nextInt
        val bytes = in.nextBytes(attrLen)
        if (attrLen == 16) { // A tasty attribute with that has only a UUID (16 bytes) implies the existence of the .tasty file
          val tastyBytes: Array[Byte] = classfile match { // TODO: simplify when #3552 is fixed
            case classfile: io.ZipArchive#Entry => // We are in a jar
              val path = classfile.parent.lookupName(
                classfile.name.stripSuffix(".class") + ".tasty", directory = false
              )
              if (path != null) {
                val stream = path.input
                try {
                  val tastyOutStream = new ByteArrayOutputStream()
                  val buffer = new Array[Byte](1024)
                  var read = stream.read(buffer, 0, buffer.length)
                  while (read != -1) {
                    tastyOutStream.write(buffer, 0, read)
                    read = stream.read(buffer, 0, buffer.length)
                  }
                  tastyOutStream.flush()
                  tastyOutStream.toByteArray
                } finally {
                  stream.close()
                }
              }
              else {
                ctx.error(s"Could not find $path in ${classfile.underlyingSource}")
                Array.empty
              }
            case _ =>
              if (classfile.jpath == null) {
                ctx.error("Could not load TASTY from .tasty for virtual file " + classfile)
                Array.empty
              } else {
                val plainFile = new PlainFile(io.File(classfile.jpath).changeExtension("tasty"))
                if (plainFile.exists) plainFile.toByteArray
                else {
                  ctx.error("Could not find " + plainFile)
                  Array.empty
                }
              }
          }
          if (tastyBytes.nonEmpty) {
            val reader = new TastyReader(bytes, 0, 16)
            val expectedUUID = new UUID(reader.readUncompressedLong(), reader.readUncompressedLong())
            val tastyUUID = new TastyHeaderUnpickler(tastyBytes).readHeader()
            if (expectedUUID != tastyUUID)
              ctx.error(s"Tasty UUID ($tastyUUID) file did not correspond the tasty UUID ($expectedUUID) declared in the classfile $classfile.")
            return unpickleTASTY(tastyBytes)
          }
        }
        else return unpickleTASTY(bytes)
      }

      if (scan(tpnme.ScalaATTR) && !scalaUnpickleWhitelist.contains(classRoot.name))
        // To understand the situation, it's helpful to know that:
        // - Scalac emits the `ScalaSig` attribute for classfiles with pickled information
        // and the `Scala` attribute for everything else.
        // - Dotty emits the `TASTY` attribute for classfiles with pickled information
        // and the `Scala` attribute for _every_ classfile.
        //
        // Therefore, if the `Scala` attribute is present but the `TASTY`
        // attribute isn't, this classfile is a compilation artifact.
        return Some(NoEmbedded)

      if (scan(tpnme.RuntimeVisibleAnnotationATTR) || scan(tpnme.RuntimeInvisibleAnnotationATTR)) {
        val attrLen = in.nextInt
        val nAnnots = in.nextChar
        var i = 0
        while (i < nAnnots) {
          val attrClass = pool.getType(in.nextChar, TypeAnnotations.empty).typeSymbol
          val nArgs = in.nextChar
          var j = 0
          while (j < nArgs) {
            val argName = pool.getName(in.nextChar)
            if (argName == nme.bytes) {
              if (attrClass == defn.ScalaSignatureAnnot)
                return unpickleScala(parseScalaSigBytes)
              else if (attrClass == defn.ScalaLongSignatureAnnot)
                return unpickleScala(parseScalaLongSigBytes)
              else if (attrClass == defn.TASTYSignatureAnnot)
                return unpickleTASTY(parseScalaSigBytes)
              else if (attrClass == defn.TASTYLongSignatureAnnot)
                return unpickleTASTY(parseScalaLongSigBytes)
            }
            parseAnnotArg(skip = true)
            j += 1
          }
          i += 1
        }
      }

      if (scan(tpnme.InnerClassesATTR)) {
        val attrLen = in.nextInt
        val entries = in.nextChar.toInt
        for (i <- 0 until entries) {
          val innerIndex = in.nextChar
          val outerIndex = in.nextChar
          val nameIndex = in.nextChar
          val jflags = in.nextChar
          if (innerIndex != 0 && outerIndex != 0 && nameIndex != 0) {
            val entry = InnerClassEntry(innerIndex, outerIndex, nameIndex, jflags)
            innerClasses(pool.getClassName(innerIndex)) = entry
          }
        }
      }
      None
    }
    finally in.bp = oldbp
  }

  /** An entry in the InnerClasses attribute of this class file. */
  case class InnerClassEntry(external: Int, outer: Int, name: Int, jflags: Int) {
    def externalName: SimpleName = pool.getClassName(external)
    def outerName: SimpleName    = pool.getClassName(outer)
    def originalName: SimpleName = pool.getName(name)

    override def toString: String =
      s"$originalName in $outerName($externalName)"
  }

  object innerClasses extends scala.collection.mutable.HashMap[Name, InnerClassEntry] {
    /** Return the Symbol of the top level class enclosing `name`,
     *  or 'name's symbol if no entry found for `name`.
     */
    def topLevelClass(name: Name)(implicit ctx: Context): Symbol = {
      val tlName = if (isDefinedAt(name)) {
        var entry = this(name)
        while (isDefinedAt(entry.outerName))
          entry = this(entry.outerName)
        entry.outerName
      }
      else
        name
      classNameToSymbol(tlName)
    }

    /** Return the class symbol for `entry`. It looks it up in its outer class.
     *  Forces all outer class symbols to be completed.
     */
    def classSymbol(entry: InnerClassEntry)(implicit ctx: Context): Symbol = {
      def getMember(sym: Symbol, name: Name)(implicit ctx: Context): Symbol =
        if (isStatic(entry.jflags))
          if (sym == classRoot.symbol)
            staticScope.lookup(name)
          else {
            var module = sym.companionModule
            if (!module.exists && sym.isAbsent())
              module = sym.scalacLinkedClass
            module.info.member(name).symbol
          }
        else if (sym == classRoot.symbol)
          instanceScope.lookup(name)
        else
          sym.info.member(name).symbol

      val outerName = entry.outerName.stripModuleClassSuffix
      val innerName = entry.originalName
      val owner = classNameToSymbol(outerName)
      val result = getMember(owner, innerName.toTypeName)(ctx.withPhase(ctx.typerPhase))
      assert(result ne NoSymbol,
        i"""failure to resolve inner class:
           |externalName = ${entry.externalName},
           |outerName = $outerName,
           |innerName = $innerName
           |owner.fullName = ${owner.showFullName}
           |while parsing ${classfile}""")
      result
    }
  }

  def skipAttributes(): Unit = {
    val attrCount = in.nextChar
    for (i <- 0 until attrCount) {
      in.skip(2); in.skip(in.nextInt)
    }
  }

  def skipMembers(): Unit = {
    val memberCount = in.nextChar
    for (i <- 0 until memberCount) {
      in.skip(6); skipAttributes()
    }
  }

  def skipSuperclasses(): Unit = {
    in.skip(2) // superclass
    val ifaces = in.nextChar
    in.skip(2 * ifaces)
  }

  protected def getOwner(flags: Int): Symbol =
    if (isStatic(flags)) moduleRoot.symbol else classRoot.symbol

  protected def getScope(flags: Int): MutableScope =
    if (isStatic(flags)) staticScope else instanceScope

  private def getPrivateWithin(jflags: Int)(implicit ctx: Context): Symbol =
    if ((jflags & (JAVA_ACC_PRIVATE | JAVA_ACC_PUBLIC)) == 0)
      classRoot.enclosingPackageClass
    else
      NoSymbol

  private def isPrivate(flags: Int)     = (flags & JAVA_ACC_PRIVATE) != 0
  private def isStatic(flags: Int)      = (flags & JAVA_ACC_STATIC) != 0
  private def hasAnnotation(flags: Int) = (flags & JAVA_ACC_ANNOTATION) != 0

  class ConstantPool {
    private val len = in.nextChar
    private val starts = new Array[Int](len)
    private val values = new Array[AnyRef](len)
    private val internalized = new Array[SimpleName](len)

    { var i = 1
      while (i < starts.length) {
        starts(i) = in.bp
        i += 1
        (in.nextByte.toInt: @switch) match {
          case CONSTANT_UTF8 | CONSTANT_UNICODE =>
            in.skip(in.nextChar)
          case CONSTANT_CLASS | CONSTANT_STRING | CONSTANT_METHODTYPE =>
            in.skip(2)
          case CONSTANT_METHODHANDLE =>
            in.skip(3)
          case CONSTANT_FIELDREF | CONSTANT_METHODREF | CONSTANT_INTFMETHODREF
             | CONSTANT_NAMEANDTYPE | CONSTANT_INTEGER | CONSTANT_FLOAT
             | CONSTANT_INVOKEDYNAMIC =>
            in.skip(4)
          case CONSTANT_LONG | CONSTANT_DOUBLE =>
            in.skip(8)
            i += 1
          case _ =>
            errorBadTag(in.bp - 1)
        }
      }
    }

    /** Return the name found at given index. */
    def getName(index: Int): SimpleName = {
      if (index <= 0 || len <= index)
        errorBadIndex(index)

      values(index) match {
        case name: SimpleName => name
        case null   =>
          val start = starts(index)
          if (in.buf(start).toInt != CONSTANT_UTF8) errorBadTag(start)
          val len   = in.getChar(start + 1).toInt
          val name = termName(fromMUTF8(in.buf, start + 1, len + 2))
          values(index) = name
          name
      }
    }

    private def fromMUTF8(bytes: Array[Byte], offset: Int, len: Int): String =
      new DataInputStream(new ByteArrayInputStream(bytes, offset, len)).readUTF

    /** Return the name found at given index in the constant pool, with '/' replaced by '.'. */
    def getExternalName(index: Int): SimpleName = {
      if (index <= 0 || len <= index)
        errorBadIndex(index)

      if (internalized(index) == null)
        internalized(index) = getName(index).replace('/', '.')

      internalized(index)
    }

    def getClassSymbol(index: Int)(implicit ctx: Context): Symbol = {
      if (index <= 0 || len <= index) errorBadIndex(index)
      var c = values(index).asInstanceOf[Symbol]
      if (c eq null) {
        val start = starts(index)
        if (in.buf(start).toInt != CONSTANT_CLASS) errorBadTag(start)
        val name = getExternalName(in.getChar(start + 1))
        if (name.endsWith("$") && (name ne nme.nothingRuntimeClass) && (name ne nme.nullRuntimeClass))
          // Null$ and Nothing$ ARE classes
          c = ctx.requiredModule(name.dropRight(1))
        else c = classNameToSymbol(name)
        values(index) = c
      }
      c
    }

    /** Return the external name of the class info structure found at 'index'.
     *  Use 'getClassSymbol' if the class is sure to be a top-level class.
     */
    def getClassName(index: Int): SimpleName = {
      val start = starts(index)
      if (in.buf(start).toInt != CONSTANT_CLASS) errorBadTag(start)
      getExternalName(in.getChar(start + 1))
    }

    /** Return the type of a class constant entry. Since
     *  arrays are considered to be class types, they might
     *  appear as entries in 'newarray' or 'cast' opcodes.
     */
    def getClassOrArrayType(index: Int)(implicit ctx: Context): Type = {
      if (index <= 0 || len <= index) errorBadIndex(index)
      val value = values(index)
      var c: Type = null
      if (value eq null) {
        val start = starts(index)
        if (in.buf(start).toInt != CONSTANT_CLASS) errorBadTag(start)
        val name = getExternalName(in.getChar(start + 1))
        if (name.firstPart(0) == ARRAY_TAG) {
          c = sigToType(name, TypeAnnotations.empty)
          values(index) = c
        }
        else {
          val sym = classNameToSymbol(name)
          values(index) = sym
          c = sym.typeRef
        }
      }
      else c = value match {
          case tp: Type => tp
          case cls: Symbol => cls.typeRef
      }
      c
    }

    def getType(index: Int, typeAnnots: TypeAnnotations)(implicit ctx: Context): Type =
      sigToType(getExternalName(index), typeAnnots)

    def getSuperClass(index: Int)(implicit ctx: Context): Symbol = {
      assert(index != 0, "attempt to parse java.lang.Object from classfile")
      getClassSymbol(index)
    }

    def getConstant(index: Int, tag: Int = -1)(implicit ctx: Context): Constant = {
      if (index <= 0 || len <= index) errorBadIndex(index)
      var value = values(index)
      if (value eq null) {
        val start = starts(index)
        value = (in.buf(start).toInt: @switch) match {
          case CONSTANT_STRING =>
            Constant(getName(in.getChar(start + 1).toInt).toString)
          case CONSTANT_INTEGER if tag != -1 =>
            val value = in.getInt(start + 1)
            (tag: @switch) match {
              case BOOL_TAG =>
                Constant(value != 0)
              case BYTE_TAG =>
                Constant(value.toByte)
              case CHAR_TAG =>
                Constant(value.toChar)
              case SHORT_TAG =>
                Constant(value.toShort)
              case _ =>
                errorBadTag(tag)
            }
          case CONSTANT_INTEGER =>
            Constant(in.getInt(start + 1))
          case CONSTANT_FLOAT =>
            Constant(in.getFloat(start + 1))
          case CONSTANT_LONG =>
            Constant(in.getLong(start + 1))
          case CONSTANT_DOUBLE =>
            Constant(in.getDouble(start + 1))
          case CONSTANT_CLASS =>
            getClassOrArrayType(index).typeSymbol
          case _ =>
            errorBadTag(start)
        }
        values(index) = value
      }
      value match {
        case  ct: Constant => ct
        case cls: Symbol   => Constant(cls.typeRef)
        case arr: Type     => Constant(arr)
      }
    }

    private def getSubArray(bytes: Array[Byte]): Array[Byte] = {
      val decodedLength = ByteCodecs.decode(bytes)
      val arr           = new Array[Byte](decodedLength)
      System.arraycopy(bytes, 0, arr, 0, decodedLength)
      arr
    }

    def getBytes(index: Int): Array[Byte] = {
      if (index <= 0 || len <= index) errorBadIndex(index)
      var value = values(index).asInstanceOf[Array[Byte]]
      if (value eq null) {
        val start = starts(index)
        if (in.buf(start).toInt != CONSTANT_UTF8) errorBadTag(start)
        val len   = in.getChar(start + 1)
        val bytes = new Array[Byte](len)
        System.arraycopy(in.buf, start + 3, bytes, 0, len)
        value = getSubArray(bytes)
        values(index) = value
      }
      value
    }

    def getBytes(indices: List[Int]): Array[Byte] = {
      assert(!indices.isEmpty, indices)
      var value = values(indices.head).asInstanceOf[Array[Byte]]
      if (value eq null) {
        val bytesBuffer = ArrayBuffer.empty[Byte]
        for (index <- indices) {
          if (index <= 0 || ConstantPool.this.len <= index) errorBadIndex(index)
          val start = starts(index)
          if (in.buf(start).toInt != CONSTANT_UTF8) errorBadTag(start)
          val len = in.getChar(start + 1)
          bytesBuffer ++= in.buf.view.slice(start + 3, start + 3 + len)
        }
        value = getSubArray(bytesBuffer.toArray)
        values(indices.head) = value
      }
      value
    }

    /** Throws an exception signaling a bad constant index. */
    private def errorBadIndex(index: Int) =
      throw new RuntimeException("bad constant pool index: " + index + " at pos: " + in.bp)

    /** Throws an exception signaling a bad tag at given address. */
    private def errorBadTag(start: Int) =
      throw new RuntimeException("bad constant pool tag " + in.buf(start) + " at byte " + start)
  }
}
