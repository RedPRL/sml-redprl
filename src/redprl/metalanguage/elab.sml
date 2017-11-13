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

  type name_env = I.var StringListDict.dict
  type ctx = I.vtype Ctx.dict
  type env = name_env * ctx

  exception todo fun ?e = raise e

  fun elabCterm env (e, c) =
    case (e, c) of
       (_, I.UP a) => I.RET (elabVterm env (e, a))
     | (LET _, _) => ?todo

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

  and elabVterm env (e, a) = 
    case (e, a) of
       (_, I.DOWN c) => I.THUNK (elabCterm env (e, c))
     | (VAR x, _) => I.VNEU (I.VAR (elabVar env (x, a)))
     | (RCD rs, I.TENSOR arow) => I.TUPLE (List.foldl (fn ((lbl,e), row) => Row.insert row lbl (elabVterm env (e, Row.lookup arow lbl))) Row.empty rs)
     | _ => ?todo

  and elabVar (names, _) (x, _) =
    StringListDict.lookup names x
end