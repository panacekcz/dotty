import scala.quoted._

def test(using QuoteContext) = {

  val x: Int = 0

  '{
    given QuoteContext = ???

    '{x + 1}  // error: wrong staging level

    '{(y: Expr[Int]) => $y }  // error: wrong staging level

  }

  '{x + 1}  // error: wrong staging level

  '{(y: Expr[Int]) => $y }  // error: wrong staging level

}
