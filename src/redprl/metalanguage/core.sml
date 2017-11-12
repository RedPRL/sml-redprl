structure MLCore : ML_CORE = 
struct

  structure Row = StringListDict
  structure Var = SyntaxData.Var

  datatype vtype = datatype SyntaxData.vtype
  datatype ctype = datatype SyntaxData.ctype
  datatype vpat = datatype SyntaxData.I.vpat
  datatype vterm = datatype SyntaxData.I.vterm
  datatype vneu = datatype SyntaxData.I.vneu
  datatype cterm = datatype SyntaxData.I.cterm
  datatype cneu = datatype SyntaxData.I.cneu
  type var = Var.t

  type ctx = (var * vtype) list
  type ictx = (vpat * vtype) list

  exception todo fun ?e = raise e

  fun eqCtype (c1, c2) = ?todo
  fun eqVtype (c1, c2) = ?todo

  fun assert b = 
    if b then () else raise Fail "assert"

  fun rinv (G, W, m, c) =
    case (m, c) of 
       (CNEU r, _) => linv (G, W, m, c)
     | (RET v, UP a) => linv (G, W, m, c)
     | (FUN (p, m'), ARR (a, b)) => rinv (G, (p, a) :: W, m', b)
     | (RECORD mrow, OBJ crow) => Row.app (fn (lbl, d) => rinv (G, W, Row.lookup mrow lbl, d)) crow

  and linv (G, W, m, c) =
    case (W, m, c) of 
       ([], CNEU r, c) => assert (eqCtype (lfoc (G, r), c))
     | ([], RET v, UP a) => rfoc (G, v, a)
     | ([], _, _) => raise Fail "Impossible?"
     | (p :: W', m, c) => linvPat (G, W, p, m, c)

  and linvPat (G, W, (p, a), m, c) =
    case (p, a, m) of
       (PTUPLE prow, TENSOR brow, _) =>
       let
         val W' = Row.foldl (fn (lbl, q, W) => (q, Row.lookup brow lbl) :: W) W prow
       in
         linv (G, W', m, c)
       end
     | (PCON prow, PLUS brow, RECORD mrow) =>
       let
         fun chkCase (lbl, b) =
           let
             val q = Row.lookup prow lbl
             val n = Row.lookup mrow lbl
           in
             linv (G, (q, b) :: W, n, c)
           end
       in
         Row.app chkCase brow
       end
     | (PNULL, UNIT, _) => linv (G, W, m, c)
     | (PVAR x, _, _) => linv ((x, a) :: G, W, m, c)

  and rfoc (G, v, a) =
    case (v, a) of
       (VNEU r, _) => assert (eqVtype (rfocNeu (G, r), a))
     | (TUPLE vrow, TENSOR brow) => Row.app (fn (lbl, b) => rfoc (G, Row.lookup vrow lbl, b)) brow
     | (CON (lbl, v), PLUS brow) => rfoc (G, v, Row.lookup brow lbl)
     | (THUNK m, DOWN c) => rinv (G, [], m, c)
     | (VNULL, UNIT) => ()

  and rfocNeu (G, r) =
    case r of 
       VAR x => lookupVar (G, x)
     | VTERM (v, a) => (rfoc (G, v, a); a)

  and lookupVar (G, x) = 
    let
      fun fib (y, _) = Var.eq (x, y)
      val SOME (_, a) = List.find fib G
    in
      a
    end

  and lfoc (G, r) =
    case r of
       FORCE r =>
       let
         val DOWN c = rfocNeu (G, r)
       in
         c
       end
     | PROJ (r, lbl) => 
       let
         val OBJ crow = lfoc (G, r)
       in
         Row.lookup crow lbl
       end
     | APP (r, v) =>
       let
         val ARR (a, c) = lfoc (G, r)
       in
         rfoc (G, v, a);
         c
       end
     | CTERM (m, c) =>
       (rinv (G, [], m, c);
        c)
       

end
