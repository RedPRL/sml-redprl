structure MLElab : ML_ELAB = 
struct
  structure I = 
  struct
    datatype vtype = datatype SyntaxData.vtype
    datatype ctype = datatype SyntaxData.ctype
    datatype vpat = datatype SyntaxData.I.vpat
    datatype vterm = datatype SyntaxData.I.vterm
    datatype vneu = datatype SyntaxData.I.vneu
    datatype cterm = datatype SyntaxData.I.cterm
    datatype cneu = datatype SyntaxData.I.cneu
    datatype eff = datatype SyntaxData.I.eff
    type var = SyntaxData.Var.t
    type sym = SyntaxData.Sym.t
  end

  structure Var = SyntaxData.Var
  structure Ctx = SplayDict (structure Key = Var)
  structure Row = StringListDict
  datatype eterm = datatype SyntaxData.E.term
  datatype epat = datatype SyntaxData.E.pat
  datatype edecl = datatype SyntaxData.E.decl
  datatype ebranch = datatype SyntaxData.E.branch

  type name_env = I.var StringListDict.dict
  type ctx = I.vtype Ctx.dict
  type env = name_env * ctx

  exception todo fun ?e = raise e

  fun elabCterm env (e, c) =
    case (e, c) of
       (_, I.UP a) => I.RET (elabVterm env (e, a))
     | (LET ([], e'), _) => elabCterm env (e', c)

     | (RCD rs, I.OBJ crow) => 
       let
         fun go (lbl, e) =
           case Row.find crow lbl of
              SOME a => elabCterm env (e, Row.lookup crow lbl)
            | NONE =>
              let
                fun abort r = I.LET (I.PCON Row.empty, r, I.RECORD Row.empty)
                val raiseMatch = I.RAISE (I.MATCH lbl, I.TUPLE Row.empty)
              in
                abort raiseMatch
              end
       in
         I.RECORD (List.foldl (fn ((lbl, e), row) => Row.insert row lbl (go (lbl, e))) Row.empty rs)
       end

     | (FUN brs, I.ARR (a, b)) => ?todo

     | (APP _, _) => ?todo

  and elabVterm env (e, a) = 
    case (e, a) of
       (_, I.DOWN c) => I.THUNK (elabCterm env (e, c))
     | (VAR x, _) => I.VNEU (I.VAR (elabVar env (x, a)))
     | (RCD rs, I.TENSOR arow) => I.TUPLE (List.foldl (fn ((lbl,e), row) => Row.insert row lbl (elabVterm env (e, Row.lookup arow lbl))) Row.empty rs)
     | (CON (lbl, e), I.PLUS arow) => I.CON (lbl, elabVterm env (e, Row.lookup arow lbl))
     | _ => ?todo

  and elabBranches (env : env) (brs : ebranch list, a : I.vtype, c : I.ctype) : I.vpat * I.cterm =
    case a of
       I.TENSOR _ => ?todo
       (* Merge all patterns *)
     | I.PLUS arow =>
       let
         fun alg (BRANCH (p, e), (pats, ns, wild)) =
           case p of
              PCON (l, p) =>
              let
                val (pat, n) = elabBranches env ([BRANCH (p, e)], Row.lookup arow l, c)
                val pats' = Row.insertMerge pats l pat (fn pat' => mergePat (pat, pat'))
                val ns' = Row.insertMerge ns l n (fn n' => mergeRhs (n, n'))
              in
                (pats', ns', wild)
              end

            | PVAR x =>
              (case wild of 
                  SOME _ => raise Fail "wild!"
                | NONE => 
                  let
                    val x' = Var.named x
                    val env' = (StringListDict.insert (#1 env) x x', Ctx.insert (#2 env) x' a)
                    val n = elabCterm env' (e, c)
                  in
                    (pats, ns, SOME (x', n))
                  end)

         val (pats, ns, wild) = List.foldr alg (Row.empty, Row.empty, NONE) brs

         val (pats', ns') =
           Row.foldl
             (fn (l, a, (ps, ns)) =>
               let
                 val (p, n) =
                   (Row.lookup pats l, Row.lookup ns l)
                  handle Row.Absent => 
                    let
                      val (x, n) = Option.valOf wild
                    in
                      (I.PVAR x, n)
                    end
               in
                 (Row.insert ps l p, Row.insert ns l n)
               end)
             (Row.empty, Row.empty)
             arow
       in
         (I.PCON pats', I.RECORD ns')
       end

  and mergePat (pat1, pat2) = 
    case (pat1, pat2) of
       (I.PCON r1, I.PCON r2) => I.PCON (Row.union r1 r2 (fn (_, p1, p2) => mergePat (p1, p2)))
     | (I.PTUPLE r1, I.PTUPLE r2) => I.PTUPLE (Row.union r1 r2 (fn (_, p1, p2) => mergePat (p1, p2)))
     | (I.PVAR _, I.PVAR _) => raise Fail "mergePat: redundant (?)"
     | _ => raise Fail "mergePat: inconsistent (?)"

  and mergeRhs (n1, n2) =
    case (n1, n2) of 
       (I.RECORD r1, I.RECORD r2) => I.RECORD (Row.union r1 r2 (fn (_, n1, n2) => mergeRhs (n1, n2)))
     | _ => raise Fail "mergeRhs: ???"

  and elabVar (names, _) (x, _) =
    StringListDict.lookup names x
end