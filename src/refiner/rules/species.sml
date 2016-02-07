structure SpeciesRules : SPECIES_RULES =
struct
  open RefinerKit OperatorData CttOperatorData SortData
  infix @@ >> $ \

  fun destSpecies m =
    case out m of
         CTT (SPECIES tau) $ [_ \ a, (_, [x]) \ b] => (tau, a, x, b)
       | _ =>
           raise Fail
             @@ "Expected Species but got "
              ^ DebugShowAbt.toString m

  fun makeEq mctx (m,n,a) =
    check
      mctx
      (CTT (EQ (sort m)) $ [([],[]) \ m, ([],[]) \ n, ([],[]) \ a],
       EXP)

  fun makeEqSequent H args =
    H >> (makeEq (#metactx H) args, TRIV)


  fun TypeEq alpha (H >> (P, _)) =
    let
      val (tau,s1,s2,univ) = destEq P
      val (_, a1, x1, b1) = destSpecies s1
      val (_, a2, x2, b2) = destSpecies s2
      val _ = destUniv univ

      val goal1 =
        (newMeta "",
         makeEqSequent H (a1,a2,univ))

      val x = alpha 0
      val xtm = check' (`x, tau)
      val b1x = subst (xtm, x1) b1
      val b2x = subst (xtm, x2) b2

      val H' =
        {metactx = MetaCtx.insert (#metactx H) (#1 goal1) (([],[]), TRIV),
         symctx = #symctx H,
         hypctx = Ctx.snoc (#hypctx H) (x, (a1, tau))}

      val goal2 =
        (newMeta "",
         makeEqSequent H' (b1x, b2x, univ))

      val psi =
        T.snoc (T.snoc T.empty goal1) goal2
    in
      (psi, fn rho =>
        abtToAbs (check' (CTT AX $ [], TRIV)))
    end
end
