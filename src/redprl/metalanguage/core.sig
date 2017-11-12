signature ML_CORE = 
sig
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

  (* check a computation (right inversion) *)
  val chk_cr : ctx * ictx * cterm * ctype -> unit

  (* check a computation (left inversion *)
  val chk_cl : ctx * ictx * cterm * ctype -> unit

  (* check a value (right focus) *)
  val chk_v : ctx * vterm * vtype -> unit

  (* infer a computation (left focus) *)
  val inf_c : ctx * cneu -> ctype

  (* infer a value *)
  val inf_v : ctx * vneu -> vtype
end