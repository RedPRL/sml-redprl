(* variable kit *)

structure VarKit =
struct
  fun ctxFromList l =
    List.foldl
      (fn ((tm, x), dict) => Var.Ctx.insert dict x tm)
      Var.Ctx.empty l

  fun toExp x = Syntax.into (Syntax.VAR (x, RedPrlSortData.EXP))

  val renameMany = RedPrlAbt.renameVars o ctxFromList
  fun rename r = renameMany [r]

  val substMany = RedPrlAbt.substVarenv o ctxFromList
  fun subst s = substMany [s]
end
