structure MLCore : ML_CORE = 
struct

  structure Row = StringListDict
  structure Var = SyntaxData.Var and Sym = SyntaxData.Sym

  datatype vtype = datatype SyntaxData.vtype
  datatype ctype = datatype SyntaxData.ctype
  datatype vpat = datatype SyntaxData.I.vpat
  datatype vterm = datatype SyntaxData.I.vterm
  datatype vneu = datatype SyntaxData.I.vneu
  datatype cterm = datatype SyntaxData.I.cterm
  datatype cneu = datatype SyntaxData.I.cneu
  datatype eff = datatype SyntaxData.I.eff

  type var = Var.t
  type sym = Sym.t

  type sign = (sym * vtype * vtype) list
  type ctx = (var * vtype) list
  type ictx = (vpat * vtype) list

  exception todo fun ?e = raise e

  fun eqCtype (c1, c2) = ?todo
  fun eqVtype (c1, c2) = ?todo

  fun assert b = 
    if b then () else raise Fail "assert"

  fun inv (S, G, W, m, c) = 
    case (W, m, c) of
       (_, CNEU r, _) => inv (S, G, W, m, c)
     | (_, RET v, UP a) => inv (S, G, W, m, c)
     | (_, FUN (p, m'), ARR (a, b)) => inv (S, G, (p, a) :: W, m', b)
     | (_, RECORD mrow, OBJ crow) => Row.app (fn (lbl, d) => inv (S, G, W, Row.lookup mrow lbl, d)) crow
     | ([], _, _) => invEmpty (S, G, m, c)
     | (p :: W', _, _) => invPat (S, G, W, p, m, c)

  and invEmpty (S, G, m, c) = 
    case (m, c) of 
       (CNEU r, _) => assert (eqCtype (lfoc (S, G, r), c))
     | (FORCE r, _) => let val DOWN d = rfocNeu (S, G, r) in assert (eqCtype (d, c)) end
     | (RET v, UP a) => rfoc (S, G, v, a)
     | (LET (p, r, n), _) =>
       let
         val UP a = lfoc (S, G, r)
       in
         inv (S, G, [(p, a)], n, c)
       end

  and invPat (S, G, W, (p, a), m, c) =
    case (p, a, m) of
       (PTUPLE prow, TENSOR brow, _) =>
       let
         val W' = Row.foldl (fn (lbl, q, W) => (q, Row.lookup brow lbl) :: W) W prow
       in
         inv (S, G, W', m, c)
       end
     | (PCON prow, PLUS brow, RECORD mrow) =>
       let
         fun chkCase (lbl, b) =
           let
             val q = Row.lookup prow lbl
             val n = Row.lookup mrow lbl
           in
             inv (S, G, (q, b) :: W, n, c)
           end
       in
         Row.app chkCase brow
       end
     | (PVAR x, _, _) => inv (S, (x, a) :: G, W, m, c)

  and rfoc (S, G, v, a) =
    case (v, a) of
       (VNEU r, _) => assert (eqVtype (rfocNeu (S, G, r), a))
     | (TUPLE vrow, TENSOR brow) => Row.app (fn (lbl, b) => rfoc (S, G, Row.lookup vrow lbl, b)) brow
     | (CON (lbl, v), PLUS brow) => rfoc (S, G, v, Row.lookup brow lbl)
     | (THUNK m, DOWN c) => inv (S, G, [], m, c)

  and rfocNeu (S, G, r) =
    case r of 
       VAR x => lookupVar (G, x)
     | VTERM (v, a) => (rfoc (S, G, v, a); a)

  and lookupVar (G, x) = 
    let
      fun fib (y, _) = Var.eq (x, y)
      val SOME (_, a) = List.find fib G
    in
      a
    end

  and lfoc (S, G, r) =
    case r of
       PROJ (r, lbl) => let val OBJ crow = lfoc (S, G, r) in Row.lookup crow lbl end
     | APP (r, v) => let val ARR (a, c) = lfoc (S, G, r) in rfoc (S, G, v, a); c end
     | CTERM (m, c) => (inv (S, G, [], m, c); c)
     | RAISE (eff, v) =>
       let
         val (a, b) = lookupEff (S, eff)
       in
         rfoc (S, G, v, a);
         UP b
       end

  and lookupEff (S : sign, eff) = 
    case eff of 
       OP th =>
       let
         fun fib (y, _, _) = Sym.eq (th, y)
         val SOME (_, a, b) = List.find fib S
       in
         (a, b)
       end
     | MATCH lbl => (TENSOR Row.empty, PLUS Row.empty)

end
