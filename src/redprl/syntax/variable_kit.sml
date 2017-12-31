(* variable kit *)

structure VarKit =
struct
  fun ctxFromList l =
    List.foldl
      (fn ((tm, x), dict) => Var.Ctx.insert dict x tm)
      Var.Ctx.empty l

  structure Syn = SyntaxView
  fun toExp x = Syn.into (Syn.VAR (x, RedPrlSort.EXP))
  fun toDim x = Syn.into (Syn.VAR (x, RedPrlSort.DIM))
  
  fun fromTerm e = 
    let
      val Syn.VAR (x, _) = Syn.out e
    in
      x
    end

  val renameMany = RedPrlAbt.renameVars o ctxFromList
  fun rename r = renameMany [r]

  val substMany = RedPrlAbt.substVarenv o ctxFromList
  fun subst s = substMany [s]
end
