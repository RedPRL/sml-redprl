structure MLCore : ML_CORE = 
struct

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

  fun chk_cr (G, W, m, c) =
    case m of
       CNEU r => chk_cl (G, W, m, c)
     | FUN (p, m') =>
       let
         val ARR (a, b) = c
       in
         chk_cr (G, (p, a) :: W, m', c)
       end

  and chk_cl _ = ?todo
  and chk_v _ = ?todo
  and inf_c _ = ?todo
  and inf_v _ = ?todo

end
