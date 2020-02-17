package dotty.tools.dotc.core.tasty

import dotty.tools.dotc.core.Contexts.Context
import dotty.tools.dotc.core.Denotations.Denotation
import dotty.tools.dotc.core.SymDenotations.SymDenotation
import dotty.tools.dotc.core.{ClassfileLoader, Flags, Names}
import dotty.tools.dotc.core.Types.{TypeRef, AnnotatedType, AppliedType, ClassInfo, MethodType, NoPrefix, PolyType, Type, TypeBounds}
import dotty.tools.dotc.core.Names.Name
import dotty.tools.dotc.core.Symbols.ClassSymbol
import dotty.tools.dotc.core.Annotations.Annotation
import dotty.tools.dotc.{Driver, Main}
import dotty.tools.io._
import dotty.tools.vulpix.TestConfiguration
import org.junit.Test

import scala.io.Source

class ClassfileAnnotationParsingTest {


  val parseOptions = TestConfiguration.defaultOptions

  private type CheckFn = (Seq[ClassSymbol], Context) => Unit

  @Test def exampleClassAnnots: Unit = {
    withJavaClasses("JavaAnnot", "Example") { (clss, wctx) =>
      implicit val ctx: Context = wctx
      val Seq(annot, example) = clss
      val exampleMod = example.companionModule.moduleClass.asClass

      def member(sym: ClassSymbol, names: Name*) = names.foldLeft[Denotation](sym.denot)((sym, name) => sym.findMember(name, NoPrefix, Flags.EmptyFlags, Flags.EmptyFlags))
      def memberTerm(name: String) = example.findMember(Names.termName(name), NoPrefix, Flags.EmptyFlags, Flags.EmptyFlags)
      def memberType(name: String) = member(example, Names.typeName(name))


      { // Parent class
        val child = memberType("InnerChild")
        val childType = child.info.asInstanceOf[ClassInfo]
        assert(hasOneJavaAnnotation(childType.parents(ctx)(0), 1, annot), "class parent")
      }
      { // Parent interfaces
        val child2 = memberType("InnerChild2")
        val child2Type = child2.info.asInstanceOf[ClassInfo]
        assert(hasOneJavaAnnotation(child2Type.parents(ctx)(0), 11, annot), "class parent")
        assert(hasOneJavaAnnotation(child2Type.parents(ctx)(1), 12, annot), "interface")
        assert(hasOneJavaAnnotation(child2Type.parents(ctx)(2), 13, annot), "interface")
      }
      { // Method parameter, result
        val m = memberTerm("m")
        val mType = m.info.asInstanceOf[MethodType]
        assert(hasOneJavaAnnotation(mType.resType, 2, annot), "method result type")
        assert(hasOneJavaAnnotation(mType.paramInfos(0), 3, annot), "method param type")
        assert(hasOneJavaAnnotation(mType.paramInfos(1), 4, annot), "method param type")
      }
      { // Field
        val f = memberTerm("f")
        val fType = f.info
        assert(hasOneJavaAnnotation(fType, 5, annot), "field type")
      }
      { // Parameter bounds
        val q = memberTerm("q")
        val qType = q.info.asInstanceOf[PolyType]
        assert(hasOneJavaAnnotation(qType.paramInfos(1).hiBound, 54, annot), "method type param bound")
      }
      { // Class type parameters
        val innerGen = memberType("InnerGeneric")
        val params = innerGen.symbol.typeParams
        assert(hasOneJavaAnnotation(params(0).denot, 14, annot))
        assert(hasOneJavaAnnotation(params(1).denot, 24, annot))
      }
      { // Class type parameter bounds
        val innerGen = memberType("InnerGeneric2")
        val params = innerGen.symbol.typeParams
        assert(hasOneJavaAnnotation(params(0).denot, 15, annot))
        assert(hasOneJavaAnnotation(params(1).denot, 55, annot))
        assert(hasOneJavaAnnotation(params(1).denot.info.hiBound, 56, annot))
      }
      { // Nested type applications
        //@17 InnerGeneric<@18 InnerGeneric<@19 String, @25 Object>.@69 InnerInnerGeneric<@57 String, @58 Object>, @26 Object>
        val nestedApp = memberType("GenericApplication")
        val nestedAppParent = nestedApp.info.asInstanceOf[ClassInfo].parents.head
        assert(hasOneJavaAnnotation(nestedAppParent, 17, annot))
        val nestedAppParentArgs = nestedAppParent.stripAnnots.asInstanceOf[AppliedType].args
        assert(hasOneJavaAnnotation(nestedAppParentArgs(0), 69, annot))
        assert(hasOneJavaAnnotation(nestedAppParentArgs(1), 26, annot))
        val nestedAppParentArgArgs = nestedAppParentArgs(0).stripAnnots.asInstanceOf[AppliedType].args
        assert(hasOneJavaAnnotation(nestedAppParentArgArgs(0), 57, annot))
        assert(hasOneJavaAnnotation(nestedAppParentArgArgs(1), 58, annot))
        val nestedAppParentArgPrefix = nestedAppParentArgs(0).stripAnnots.asInstanceOf[AppliedType].tycon.asInstanceOf[TypeRef].prefix
        assert(hasOneJavaAnnotation(nestedAppParentArgPrefix, 18, annot))
        val nestedAppParentArgPrefixArgs = nestedAppParentArgPrefix.stripAnnots.asInstanceOf[AppliedType].args
        assert(hasOneJavaAnnotation(nestedAppParentArgPrefixArgs(0), 19, annot))
        assert(hasOneJavaAnnotation(nestedAppParentArgPrefixArgs(1), 25, annot))
        val nestedAppParentPrefix = nestedAppParent.stripAnnots.asInstanceOf[AppliedType].tycon.asInstanceOf[TypeRef].prefix
        assert(hasOneJavaAnnotation(nestedAppParentPrefix, 62, annot))
      }
      { // Nested type applications with static classes
        // @61 NestedGeneric<NestedGeneric. @63 NestedNestedGeneric<@64 String> >
        val nestedApp = memberType("NestedGenericApplication")
        val nestedAppParent = nestedApp.info.asInstanceOf[ClassInfo].parents.head
        assert(hasOneJavaAnnotation(nestedAppParent, 61, annot))
        val nestedAppParentArgs = nestedAppParent.stripAnnots.asInstanceOf[AppliedType].args
        assert(hasOneJavaAnnotation(nestedAppParentArgs(0), 63, annot))
        val nestedAppParentArgArgs = nestedAppParentArgs(0).stripAnnots.asInstanceOf[AppliedType].args
        assert(hasOneJavaAnnotation(nestedAppParentArgArgs(0), 64, annot))
      }
      { // Arrays in parent
        // @20 InnerGeneric<@21 String @22[] @23[], @43 int @44[]>
        // @20 InnerGeneric[@22 Array[@23 Array[@21 String]], @44 Array[@43 Int]]
        val arrayApp = memberType("ArrayApplication")
        val arrayAppParent = arrayApp.info.asInstanceOf[ClassInfo].parents.head
        assert(hasOneJavaAnnotation(arrayAppParent, 20, annot))
        val arrayAppParentArgs = arrayAppParent.stripAnnots.asInstanceOf[AppliedType].args
        assert(hasOneJavaAnnotation(arrayAppParentArgs(0), 22, annot))
        assert(hasOneJavaAnnotation(arrayAppParentArgs(1), 44, annot))
        val arrayAppParentArgs0Element = arrayAppParentArgs(0).stripAnnots.asInstanceOf[AppliedType].args(0)
        assert(hasOneJavaAnnotation(arrayAppParentArgs0Element, 23, annot))
        val arrayAppParentArgs0ElementElement = arrayAppParentArgs0Element.stripAnnots.asInstanceOf[AppliedType].args(0)
        assert(hasOneJavaAnnotation(arrayAppParentArgs0ElementElement, 21, annot))
        val arrayAppParentArgs1Element = arrayAppParentArgs(1).stripAnnots.asInstanceOf[AppliedType].args(0)
        assert(hasOneJavaAnnotation(arrayAppParentArgs1Element, 43, annot))
      }
      { // Inner class parents
        val inner = member(example, Names.typeName("Inner"), Names.typeName("Inner2"), Names.typeName("InnerParents"))
        val innerParent = inner.info.asInstanceOf[ClassInfo].parents.head
        assert(hasOneJavaAnnotation(innerParent, 29, annot))
        val innerParentPrefix = innerParent.stripAnnots.asInstanceOf[TypeRef].prefix
        assert(hasOneJavaAnnotation(innerParentPrefix, 28, annot))
        val innerParentPrefixPrefix = innerParentPrefix.stripAnnots.asInstanceOf[TypeRef].prefix
        assert(hasOneJavaAnnotation(innerParentPrefixPrefix, 27, annot))
        val innerParentPrefixPrefixPrefix = innerParentPrefixPrefix.stripAnnots.asInstanceOf[TypeRef].prefix
        assert(hasOneJavaAnnotation(innerParentPrefixPrefixPrefix, 66, annot))
      }
      { // Nested class parents
        val nested = member(exampleMod, Names.termName("Nested"), Names.typeName("Nested2"), Names.typeName("NestedParents"))
        val nestedParent = nested.info.asInstanceOf[ClassInfo].parents.head
        assert(hasOneJavaAnnotation(nestedParent, 49, annot))
      }
      { // Nested and inner classes
        val nestedInner = member(exampleMod, Names.termName("N1"), Names.termName("N2"), Names.typeName("N3"), Names.typeName("I1"), Names.typeName("I2"), Names.typeName("NI"))
        val nestedInnerParent = nestedInner.info.asInstanceOf[ClassInfo].parents.head
        assert(hasOneJavaAnnotation(nestedInnerParent, 38, annot))
        val nestedInnerParentPrefix = nestedInnerParent.stripAnnots.asInstanceOf[TypeRef].prefix
        assert(hasOneJavaAnnotation(nestedInnerParentPrefix, 48, annot))
        val nestedInnerParentPrefixPrefix = nestedInnerParentPrefix.stripAnnots.asInstanceOf[TypeRef].prefix
        assert(hasOneJavaAnnotation(nestedInnerParentPrefixPrefix, 47, annot))
        val nestedInnerParentPrefixPrefixPrefix = nestedInnerParentPrefixPrefix.stripAnnots.asInstanceOf[TypeRef].prefix
        assert(hasOneJavaAnnotation(nestedInnerParentPrefixPrefixPrefix, 39, annot))
      }
      {
        val nestedInner2 = member(exampleMod, Names.termName("N1"), Names.termName("N2"), Names.typeName("N3"), Names.typeName("I1"), Names.typeName("I2"), Names.typeName("NI2"))
        val nestedInner2Parent = nestedInner2.info.asInstanceOf[ClassInfo].parents.head
        assert(hasOneJavaAnnotation(nestedInner2Parent, 52, annot))
      }
      { // Generic in method param
        val genericMeth = memberTerm("mGenericApplication")
        val genericMethParam = genericMeth.info.asInstanceOf[MethodType].paramInfos(0)
        assert(hasOneJavaAnnotation(genericMethParam, 70, annot))
        val genericMethParamArgs = genericMethParam.stripAnnots.asInstanceOf[AppliedType].args
        assert(hasOneJavaAnnotation(genericMethParamArgs(0), 30, annot))
        assert(hasOneJavaAnnotation(genericMethParamArgs(1), 33, annot))
        val genericMethParamArgArgs = genericMethParamArgs(0).stripAnnots.asInstanceOf[AppliedType].args
        assert(hasOneJavaAnnotation(genericMethParamArgArgs(0), 31, annot))
        assert(hasOneJavaAnnotation(genericMethParamArgArgs(1), 32, annot))
      }
      { // Array in method param
        val arrayMeth = memberTerm("mArrayApplication")
        val arrayMethParams = arrayMeth.info.asInstanceOf[MethodType].paramInfos
        assert(hasOneJavaAnnotation(arrayMethParams(0), 36, annot))
        assert(hasOneJavaAnnotation(arrayMethParams(1), 46, annot))
        val arrayMethParam0Element = arrayMethParams(0).stripAnnots.asInstanceOf[AppliedType].args(0)
        assert(hasOneJavaAnnotation(arrayMethParam0Element, 37, annot))
        val arrayMethParam0ElementElement = arrayMethParam0Element.stripAnnots.asInstanceOf[AppliedType].args(0)
        assert(hasOneJavaAnnotation(arrayMethParam0ElementElement, 35, annot))
        val arrayMethParam1Element = arrayMethParams(1).stripAnnots.asInstanceOf[AppliedType].args(0)
        assert(hasOneJavaAnnotation(arrayMethParam1Element, 45, annot))
      }
      { // Nested classes in method param
        val nestedMeth = memberTerm("mNestedApplication")
        val nestedMethParams = nestedMeth.info.asInstanceOf[MethodType].paramInfos
        assert(hasOneJavaAnnotation(nestedMethParams(0), 40, annot))
      }
      { // Inner classes in method param
        val innerMeth = memberTerm("mInnerApplication")
        val innerMethParams = innerMeth.info.asInstanceOf[MethodType].paramInfos
        assert(hasOneJavaAnnotation(innerMethParams(0), 42, annot))
        val innerMethParamPrefix = innerMethParams(0).stripAnnots.asInstanceOf[TypeRef].prefix
        assert(hasOneJavaAnnotation(innerMethParamPrefix, 51, annot))
        val innerMethParamPrefixPrefix = innerMethParamPrefix.stripAnnots.asInstanceOf[TypeRef].prefix
        assert(hasOneJavaAnnotation(innerMethParamPrefixPrefix, 50, annot))
        val innerMethParamPrefixPrefixPrefix = innerMethParamPrefixPrefix.stripAnnots.asInstanceOf[TypeRef].prefix
        assert(hasOneJavaAnnotation(innerMethParamPrefixPrefixPrefix, 71, annot))
      }
      { // Nested generic classes in method param
        val nestedGenMeth = memberTerm("mNestedGenericApplication")
        val nestedGenMethParam = nestedGenMeth.info.asInstanceOf[MethodType].paramInfos(0)
        assert(hasOneJavaAnnotation(nestedGenMethParam, 65, annot))
        val nestedGenMethParamArg = nestedGenMethParam.stripAnnots.asInstanceOf[AppliedType].args(0)
        assert(hasOneJavaAnnotation(nestedGenMethParamArg, 67, annot))
        val nestedGenMethParamArgArg = nestedGenMethParamArg.stripAnnots.asInstanceOf[AppliedType].args(0)
        assert(hasOneJavaAnnotation(nestedGenMethParamArgArg, 68, annot))
      }
      { // Wildcard bounds in method param
        val ubWildMeth = memberTerm("mUpperBoundWildcard")
        val ubWildMethParam = ubWildMeth.info.asInstanceOf[MethodType].paramInfos(0)
        val ubWildMethParamArg = ubWildMethParam.asInstanceOf[AppliedType].args(0)
        val ubWildMethParamBound = ubWildMethParamArg.asInstanceOf[TypeBounds].hi
        assert(hasOneJavaAnnotation(ubWildMethParamBound, 77, annot))
        val ubWildMethParamBoundArg = ubWildMethParamBound.stripAnnots.asInstanceOf[AppliedType].args(0)
        val ubWildMethParamBoundBound = ubWildMethParamBoundArg.asInstanceOf[TypeBounds].hi
        assert(hasOneJavaAnnotation(ubWildMethParamBoundBound, 73, annot))
      }
      { // Wildcard bounds in method param
        val lbWildMeth = memberTerm("mLowerBoundWildcard")
        val lbWildMethParam = lbWildMeth.info.asInstanceOf[MethodType].paramInfos(0)
        val lbWildMethParamArg = lbWildMethParam.asInstanceOf[AppliedType].args(0)
        val lbWildMethParamBound = lbWildMethParamArg.asInstanceOf[TypeBounds].lo
        assert(hasOneJavaAnnotation(lbWildMethParamBound, 79, annot))
        val lbWildMethParamBoundArg = lbWildMethParamBound.stripAnnots.asInstanceOf[AppliedType].args(0)
        val lbWildMethParamBoundBound = lbWildMethParamBoundArg.asInstanceOf[TypeBounds].lo
        assert(hasOneJavaAnnotation(lbWildMethParamBoundBound, 75, annot))
      }
      { // Inheritance in generic class (type application without signature)
        val inner = member(example, Names.typeName("InnerGeneric2"), Names.typeName("InnerInner2Generic2"))
        val innerParent = inner.info.asInstanceOf[ClassInfo].parents.head
        assert(hasOneJavaAnnotation(innerParent, 80, annot))
      }
      // Untested annotations:
      // 7 - throws annotations are ignored
      // 6 - receiver annotations are ignored
      // 8, 9, 53 - method type parameters not stored
      // 10, 42, 16, 41 - & operator drops annotations
      // 72, 74, 76, 78 - wildcard annotations are ignored
    }
  }

  private def isJavaAnnotation(annot: Annotation, expectedArg: Int, annotCls: ClassSymbol)(implicit ctx: Context): Boolean = {
    annot.matches(annotCls)
    val arg = annot.argumentConstant(0)
    arg.isDefined && arg.get.intValue == expectedArg
  }

  private def hasOneJavaAnnotation(tp: Type, expectedArg: Int, annotCls: ClassSymbol)(implicit ctx: Context): Boolean ={
    tp match {
      case AnnotatedType(parent, annot) => isJavaAnnotation(annot, expectedArg, annotCls) && !parent.isInstanceOf[AnnotatedType]
      case _ => false
    }
  }

  private def hasOneJavaAnnotation(sym: SymDenotation, expectedArg: Int, annotCls: ClassSymbol)(implicit ctx: Context): Boolean ={
    sym.annotations match {
      case List(annot) => isJavaAnnotation(annot, expectedArg, annotCls)
      case _ => false
    }
  }


  private def withJavaClasses(names: String*)(checkFn: CheckFn): Unit = {
    Directory.inTempDirectory { tmp =>

      val out = tmp./("out")
      out.createDirectory()

      val compResult = compileWithJavac(names.map(n => Path("tests/java-annotations")./(s"$n.java")), out)

      assert(compResult.isEmpty, compResult.get)

      val driver = new ParsingDriver

      val options = parseOptions
        .withClasspath(out.toAbsolute.toString)
        .and("dummy")

      driver.run(options.all, names, out)(checkFn)
    }
  }

  private class ParsingDriver extends Driver {
    def run(args: Array[String], classes: Seq[String], out: Path)(checkFn: CheckFn): Unit = {
      implicit val (_, ctx: Context) = setup(args, initCtx)
      ctx.initialize()
      val clss = classes.map(parseClassFile(out))
      checkFn(clss, ctx)
    }
  }

  // Code copied from compiler/test/dotty/tools/vulpix/ParallelTesting.scala
  private def compileWithJavac(fs: Seq[Path], out: Path) = if (fs.nonEmpty) {
    val fullArgs = Array(
      "javac",
      "-encoding", "UTF-8",
      "-d", out.toAbsolute.toString
    ) ++ fs.map(f => f.toAbsolute.toString)

    val process = Runtime.getRuntime.exec(fullArgs)
    val output = Source.fromInputStream(process.getErrorStream).mkString

    if (process.waitFor() != 0) Some(output)
    else None
  } else None

  private def parseClassFile(out:Path)(name: String)(implicit ctx: Context): ClassSymbol = {
    val rootClassSym = ctx.newClassSymbol(ctx.definitions.EmptyPackageClass, Names.typeName(name), Flags.EmptyFlags, loadClass(out, name + ".class"))
    rootClassSym.ensureCompleted()
    rootClassSym
  }

  private def loadClass(out:Path, name: String)(sym: ClassSymbol)(implicit ctx: Context): Type = {
    new ClassfileLoader(AbstractFile.getFile(out./(name)))
  }

}

