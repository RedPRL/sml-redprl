functor MlResolver (Ty : ML_TYPE) :> RESOLVER where type mltype = Ty.vty and type id = string =
struct
  structure E = RedPrlError

  fun @@ (f, x) = f x
  infixr @@

  type mltype = Ty.vty
  type id = string

  type env =
    {ids : Ty.vty StringListDict.dict,
     vars : (Tm.variable * Tm.sort) StringListDict.dict,
     metas : (Tm.metavariable * Tm.valence) StringListDict.dict}

  val init =
    {ids = StringListDict.empty,
     vars = StringListDict.empty,
     metas = StringListDict.empty}

  fun lookup dict pos x =
    case StringListDict.find dict x of
       SOME r => r
     | NONE => E.raiseAnnotatedError' (pos, E.GENERIC [Fpp.text "Could not resolve name", Fpp.text x])

  fun lookupId (env : env) =
    lookup (#ids env)

  fun lookupVar (env : env) =
    lookup (#vars env)

  fun lookupMeta (env : env) =
    lookup (#metas env)

  (* TODO: ensure that this name is not already used *)
  fun extendId {ids, vars, metas} nm vty =
    {ids = StringListDict.insert ids nm vty,
     vars = vars,
     metas = metas}

  fun extendVars {ids, vars, metas} (xs, taus) =
    let
      val (gamma, vars') =
        ListPair.foldrEq
          (fn (x, tau, (gamma, vars)) =>
            let
              val x' = Sym.named x
            in
              ((x',tau) :: gamma, StringListDict.insert vars x (x', tau))
            end)
          ([], vars)
          (xs, taus)
      val env = {ids = ids, vars = vars', metas = metas}
    in
      (gamma, env)
    end
    handle exn =>
      E.raiseError @@
        E.GENERIC [Fpp.text "extendVars: invalid arguments", Fpp.text @@ exnMessage exn]

  fun extendMetas {ids, vars, metas} (Xs, vls) =
    let
      val (psi, metas') =
        ListPair.foldrEq
          (fn (X, vl, (psi, metas)) =>
            let
              val X' = Metavar.named X
            in
              ((X',vl) :: psi, StringListDict.insert metas X (X', vl))
            end)
          ([], metas)
          (Xs, vls)
      val env = {ids = ids, vars = vars, metas = metas'}
    in
      (psi, env)
    end
    handle _ =>
      E.raiseError @@ 
        E.GENERIC [Fpp.text "extendMetas: invalid arguments"]
end


