object ExtMethods:

  case class Circle(x: Double, y: Double, radius: Double)

  def (c: Circle).circumference: Double = c.radius * math.Pi * 2

  val circle = Circle(0, 0, 1)
  circle.circumference
  assert(circle.circumference == circumference(circle))

  trait StringSeqOps {
    def (xs: Seq[String]).longestStrings = {
      val maxLength = xs.map(_.length).max
      xs.filter(_.length == maxLength)
    }
  }
  given ops1 as StringSeqOps

  List("here", "is", "a", "list").longestStrings

  locally {
    object ops2 extends StringSeqOps
    import ops2.longestStrings
    List("here", "is", "a", "list").longestStrings
  }

  def (x: String) < (y: String) = x.compareTo(y) < 0
  def [Elem](x: Elem) #: (xs: Seq[Elem]) = x +: xs

  assert("a" < "bb")
  val xs = 1 #: Vector(2, 3)

  def [T](xs: List[T]) second =
    xs.tail.head

  def [T](xs: List[List[T]]) flattened =
    xs.foldLeft[List[T]](Nil)(_ ++ _)

  def [T: Numeric](x: T) + (y: T): T =
    summon[Numeric[T]].plus(x, y)

  List(1, 2, 3).second[Int]

  extension stringOps on (xs: Seq[String]) {
    def longestStrings: Seq[String] = {
      val maxLength = xs.map(_.length).max
      xs.filter(_.length == maxLength)
    }
  }

  extension listOps on [T](xs: List[T]):
    def second = xs.tail.head
    def third: T = xs.tail.tail.head


  extension on [T](xs: List[T])(using Ordering[T]):
    def largest(n: Int) = xs.sorted.takeRight(n)

  given stringOps1 as AnyRef {
    def (xs: Seq[String]).longestStrings: Seq[String] = {
      val maxLength = xs.map(_.length).max
      xs.filter(_.length == maxLength)
    }
  }

  given listOps1 as AnyRef {
    def [T](xs: List[T]) second = xs.tail.head
    def [T](xs: List[T]) third: T = xs.tail.tail.head
  }

  given AnyRef {
    def [T](xs: List[T]) largest (using Ordering[T])(n: Int) =
      xs.sorted.takeRight(n)
  }

end ExtMethods