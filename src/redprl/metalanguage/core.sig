signature ML_DATA = 
sig
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

signature ML_CORE = 
sig
  include ML_DATA

  (* effect signature *)
  type sign = (sym * vtype * vtype) list

  (* variable context *)
  type ctx = (var * vtype) list

  (* inversion context *)
  type ictx = (vpat * vtype) list

  (* check computations (inversion) *)
  val inv : sign * ctx * ictx * cterm * ctype -> unit

  (* check values (right focus) *)
  val rfoc : sign * ctx * vterm * vtype -> unit

  (* infer neutral values (right focus) *)
  val rfocNeu : sign * ctx * vneu -> vtype

  (* infer neutral computations (left focus) *)
  val lfoc : sign * ctx * cneu -> ctype
end