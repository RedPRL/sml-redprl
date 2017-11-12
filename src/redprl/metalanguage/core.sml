structure MLCore : ML_CORE = 
struct

  structure Row = StringListDict

  datatype vtype = datatype SyntaxData.vtype
  datatype ctype = datatype SyntaxData.ctype
  datatype vpat = datatype SyntaxData.I.vpat
  datatype vterm = datatype SyntaxData.I.vterm
  datatype vneu = datatype SyntaxData.I.vneu
  datatype cterm = datatype SyntaxData.I.cterm
  datatype cneu = datatype SyntaxData.I.cneu
  type var = SyntaxData.Var.t

  type ctx = (var * vtype) list
  type ictx = (vpat * vtype) list

  exception todo fun ?e = raise e

  fun eq_ctype (c1, c2) = ?todo

  fun chk_cr (G, W, m, c) =
    case m of
       CNEU r => chk_cl (G, W, m, c)
     | FUN (p, m') =>
       let
         val ARR (a, b) = c
       in
         chk_cr (G, (p, a) :: W, m', c)
       end

  and chk_cl (G, W, m, c) =
    case (W, m) of 
       ([], CNEU r) => eq_ctype (inf_c (G, r), c)
     | ([], _) => raise Fail "Impossible?"
     | (p :: W', _) => chk_cl_pat (G, W, p, m, c)

  and chk_cl_pat (G, W, (p, a), m, c) =
    case (p, a, m) of
       (PTUPLE prow, TENSOR brow, _) =>
       let
         val W' = Row.foldl (fn (lbl, q, W) => (q, Row.lookup brow lbl) :: W) W prow
       in
         chk_cl (G, W', m, c)
       end
     | (PCON prow, PLUS brow, RECORD mrow) =>
       let
         fun chk_case (lbl, b) =
           let
             val q = Row.lookup prow lbl
             val n = Row.lookup mrow lbl
           in
             chk_cl (G, (q, b) :: W, n, c)
           end
       in
         Row.app chk_case brow
       end
     | (PNULL, UNIT, _) => chk_cl (G, W, m, c)
     | (PVAR x, _, _) => chk_cl ((x, a) :: G, W, m, c)

  and chk_v _ = ?todo
  and inf_c _ = ?todo
  and inf_v _ = ?todo

end
