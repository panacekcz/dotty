def myMacroImpl(a: quoted.Expr[_])(using qctx: quoted.QuoteContext) = {
  import qctx.tasty.{_, given _}
  def typed[A] = {
    implicit val t: quoted.Type[A] = a.unseal.tpe.widen.seal.asInstanceOf[quoted.Type[A]]
    '{
      type T = $t
      ${a.unseal.seal.cast[T]}
    }
  }

  typed
}


inline def myMacro(a: => Any) = ${
  myMacroImpl('a)
}
