(* XXX impose a signature on `Assert`! *)
structure Assert =
struct
  structure AJ = AtomicJudgment
  structure E = RedPrlError
  structure L = RedPrlLevel
  structure K = RedPrlKind
  structure Abt = RedPrlAbt
  structure Syn = SyntaxView

  fun @@ (f, x) = f x
  infixr @@

  fun isInUsefulUnivOmega (k', k) =
    not (OptionUtil.eq K.eq (K.residual (k, k'), SOME k))
  
  fun sortEq (tau1, tau2) = 
    if tau1 = tau2 then 
      ()
    else
      raise E.error [Fpp.text "Expected sort", TermPrinter.ppSort tau1, Fpp.text "to be equal to", TermPrinter.ppSort tau2]

  fun alphaEq' msg (m, n) =
    if Abt.eq (m, n) then
      ()
    else
      raise E.error [Fpp.text msg, Fpp.text ":", Fpp.text "Expected", TermPrinter.ppTerm m, Fpp.text "to be alpha-equivalent to", TermPrinter.ppTerm n]

  fun alphaEq (m, n) =
    if Abt.eq (m, n) then
      ()
    else
      raise E.error [Fpp.text "Expected", TermPrinter.ppTerm m, Fpp.text "to be alpha-equivalent to", TermPrinter.ppTerm n]

  fun alphaEqEither ((m0, m1), n) =
    if Abt.eq (m0, n) orelse Abt.eq (m1, n) then
      ()
    else
      raise E.error [Fpp.text "Expected", TermPrinter.ppTerm m0, Fpp.text "or", TermPrinter.ppTerm m1, Fpp.text "to be alpha-equivalent to", TermPrinter.ppTerm n]

  fun levelLt (l1, l2) =
    if L.< (l1, l2) then
      ()
    else
      raise E.error [Fpp.text "Expected level", TermPrinter.ppTerm (L.into l1), Fpp.text "to be less than", TermPrinter.ppTerm (L.into l2)]

  fun levelLeq (l1, l2) =
    if L.<= (l1, l2) then
      ()
    else
      raise E.error [Fpp.text "Expected level", TermPrinter.ppTerm (L.into l1), Fpp.text "to be less than or equal to", TermPrinter.ppTerm (L.into l2)]

  fun levelEq (l1, l2) =
    if L.eq (l1, l2) then
      ()
    else
      raise E.error [Fpp.text "Expected level", TermPrinter.ppTerm (L.into l1), Fpp.text "to be equal to", TermPrinter.ppTerm (L.into l2)]

  fun kindLeq (k1, k2) =
    if K.<= (k1, k2) then
      ()
    else
      raise E.error [Fpp.text "Expected kind", TermPrinter.ppKind k1, Fpp.text "to be stronger than or equal to", TermPrinter.ppKind k2]

  fun kindEq (k1, k2) =
    if k1 = k2 then
      ()
    else
      raise E.error [Fpp.text "Expected kind", TermPrinter.ppKind k1, Fpp.text "to be equal to", TermPrinter.ppKind k2]

  fun inUsefulUnivOmega (k', k) =
    if isInUsefulUnivOmega (k', k) then
      ()
    else
      E.raiseError @@ E.GENERIC [Fpp.text "Expected kind", TermPrinter.ppKind k', Fpp.text "to be useful for kind", TermPrinter.ppKind k]

  fun dirEq msg ((r1, r1'), (r2, r2')) =
    if Abt.eq (r1, r2) andalso Abt.eq (r1', r2') then
      ()
    else
      raise E.error
        [Fpp.text (msg ^ ":"),
         Fpp.text "Expected direction",
         TermPrinter.ppTerm r1,
         Fpp.text "~>",
         TermPrinter.ppTerm r1',
         Fpp.text "to be equal to",
         TermPrinter.ppTerm r2,
         Fpp.text "~>",
         TermPrinter.ppTerm r2']

  fun equationEq msg ((r1, r1'), (r2, r2')) =
    if Abt.eq (r1, r2) andalso Abt.eq (r1', r2') then
      ()
    else
      raise E.error
        [Fpp.text (msg ^ ":"),
         Fpp.text "Expected equation",
         TermPrinter.ppTerm r1,
         Fpp.text "=",
         TermPrinter.ppTerm r1',
         Fpp.text "to be equal to",
         TermPrinter.ppTerm r2,
         Fpp.text "=",
         TermPrinter.ppTerm r2']

  fun equationsEq msg = ListPair.mapEq (equationEq msg)

  (* The following is a sufficient condition for tautology:
   * the list contains a true equation `r = r` or both `r = 0`
   * and `r = 1` for some r.
   *)
  structure SymSet = SplaySet (structure Elem = Sym.Ord)
  fun tautologicalEquations msg eqs =
    let
      fun goEqs _ [] = false
        | goEqs (state as (zeros, ones)) ((r1, r2) :: eqs) =
            case (Syn.out r1, Syn.out r2) of
              (Syn.DIM0, Syn.DIM0) => true
            | (Syn.DIM0, Syn.DIM1) => goEqs state eqs
            | (Syn.DIM0, Syn.VAR _) => goEqs state eqs
            | (Syn.DIM0, Syn.META _) => goEqs state eqs
            | (Syn.DIM1, Syn.DIM1) => true
            | (Syn.DIM1, Syn.DIM0) => goEqs state eqs
            | (Syn.DIM1, Syn.VAR _) => goEqs state eqs
            | (Syn.DIM1, Syn.META _) => goEqs state eqs
            | (Syn.VAR (u, _), Syn.DIM0) =>
                SymSet.member ones u orelse goEqs (SymSet.insert zeros u, ones) eqs
            | (Syn.META (u, _), Syn.DIM0) =>
                SymSet.member ones u orelse goEqs (SymSet.insert zeros u, ones) eqs
            | (Syn.VAR (u, _), Syn.DIM1) =>
                SymSet.member zeros u orelse goEqs (zeros, SymSet.insert ones u) eqs
            | (Syn.META (u, _), Syn.DIM1) =>
                SymSet.member zeros u orelse goEqs (zeros, SymSet.insert ones u) eqs
            | (Syn.VAR (u, _), Syn.VAR (v, _)) => Sym.eq (u, v) orelse goEqs state eqs
            | (Syn.META (u, _), Syn.META (v, _)) => Sym.eq (u, v) orelse goEqs state eqs
            | _ => raise E.error [Fpp.text "Expected equation but got ", TermPrinter.ppTerm r1, Fpp.text "=", TermPrinter.ppTerm r2]
      fun prettyEq (r1, r2) = [TermPrinter.ppTerm r1, Fpp.text "=", TermPrinter.ppTerm r2, Fpp.text ";"]
    in
      if goEqs (SymSet.empty, SymSet.empty) eqs then
        ()
      else
        (* todo: pretty printer for equation lists *)
        raise E.error
          (List.concat
            [ [Fpp.text (msg ^ ":"), Fpp.text "Expected shape"]
            , ListMonad.bind prettyEq eqs
            , [Fpp.text "to have true equation r = r or equation pair r = 0 and r = 1."]
            ])
    end

  fun varEq (x, y) =
    if Var.eq (x, y) then
      ()
    else
      raise E.error [Fpp.text "Expected variable", TermPrinter.ppVar x, Fpp.text "to be equal to variable", TermPrinter.ppVar y]

  fun labelEq msg (lbl0, lbl1) =
    if lbl0 = lbl1 then
      ()
    else
      raise E.error [Fpp.text msg, Fpp.char #":", Fpp.text "Expected label", TermPrinter.ppLabel lbl0, Fpp.text "to be equal to label", TermPrinter.ppLabel lbl1]

  fun labelsEq msg (l0, l1) =
    ListPair.appEq (labelEq msg) (l0, l1)

  structure View =
  struct
    val levelLeq =
      fn (_, AJ.View.OMEGA) => ()
       | (l0, AJ.View.FINITE l1) => levelLeq (l0, l1)
    val levelLt =
      fn (_, AJ.View.OMEGA) => ()
       | (l0, AJ.View.FINITE l1) => levelLt (l0, l1)
    fun univMem ((l0,k0), (l1,k1)) = (levelLt (l0,l1); kindLeq (k0,k1)) 
  end
end
