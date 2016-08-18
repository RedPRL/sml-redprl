structure AbtSignature : ABT_SIGNATURE =
struct
  structure Abt = RedPrlAbt

  type opid = Abt.symbol
  structure Telescope = SymbolTelescope

  structure Arity = RedPrlAtomicArity
  structure Valence = Arity.Vl
  structure Sort = Valence.S
  structure Symbol = Abt.Sym
  structure MCtx = Abt.Metavar.Ctx

  type term = Abt.abt
  type symbol = Abt.symbol
  type sort = Sort.t
  type metavariable = Abt.metavariable
  type valence = Valence.t
  type arguments = (metavariable * valence) list
  type symbols = (symbol * sort) list

  type def =
    {parameters : symbols,
     arguments : arguments,
     sort : sort,
     definiens : term}

  structure Decl =
  struct
    datatype decl = DEF of def | SYM_DECL of sort
  end

  open Decl

  type sign = (decl * Pos.t option) Telescope.telescope

  local
    structure J = Json and AJ = RedPrlAbtJson and AS = RedPrlAtomicSortJson
    structure NE = AJ.NameEnv
    open Telescope.ConsView

    val encodeSym = J.String o Abt.Sym.toString
    val encodeMetavar = J.String o Abt.Metavar.toString

    fun encodeValence ((ssorts, vsorts), tau) =
      J.Obj
        [("syms", J.Array (List.map AS.encode ssorts)),
         ("vars", J.Array (List.map AS.encode vsorts)),
         ("sort", AS.encode tau)]

    fun encodeParam (u, tau) =
      J.Obj [("sym", encodeSym u), ("sort", AS.encode tau)]

    fun encodeArg (x, vl) =
      J.Obj [("metavar", encodeMetavar x), ("valence", encodeValence vl)]

    fun encodeDef {parameters, arguments, sort, definiens} =
      J.Obj
        [("parameters", J.Array (List.map encodeParam parameters)),
         ("arguments", J.Array (List.map encodeArg arguments)),
         ("sort", AS.encode sort),
         ("definiens", AJ.encode definiens)]

    val encodeDecl =
      fn DEF def => encodeDef def
       | SYM_DECL tau => J.Obj [("sym_decl", AS.encode tau)]

    fun encode' sign =
      case out sign of
         EMPTY => []
       | CONS (sym, (decl, pos), sign') =>
         let
           val lbl = Symbol.toString sym
           val obj = encodeDecl decl
         in
           (lbl, obj) :: encode' sign'
         end

    structure RS = RedPrlOperator.S

    fun liftValence ((ssorts, vsorts), tau) =
      ((List.map RS.EXP ssorts, List.map RS.EXP vsorts), RS.EXP tau)

    fun decodeDecl env ctx sign =
      fn J.Obj [("sym_decl", tau)] => SYM_DECL (Option.valOf (AS.decode tau))
       | J.Obj [("parameters", J.Array params), ("arguments", J.Array args), ("sort", sort), ("definiens", definiens)] =>
         let
           val decodeParamBinding =
             fn J.Obj [("sym", J.String u), ("sort", tau)] =>
                (Abt.Sym.named u, Option.valOf (AS.decode tau))
              | _ => raise Match

           val decodeArgBinding =
             fn J.Obj [("metavar", x), ("valence", vl)] => raise Match
              | _ => raise Match

           val params' = List.map decodeParamBinding params
           val args' = List.map decodeArgBinding args
           val sort' = Option.valOf (AS.decode sort)

           val (menv, senv, venv) = env
           val (mctx, sctx, vctx) = ctx

           val (menv', mctx') = List.foldl (fn ((x, vl), (e, c)) => (NE.insert e (Abt.Metavar.toString x) x, Abt.Metavar.Ctx.insert c x (liftValence vl))) (menv, mctx) args'
           val (senv', sctx') = List.foldl (fn ((u, tau), (e, c)) => (NE.insert e (Abt.Sym.toString u) u, Abt.Sym.Ctx.insert c u (RS.EXP tau))) (senv, sctx) params'

           val env' = (menv', senv', venv)
           val ctx' = (mctx', sctx', vctx)

           val definiens' = AJ.decode env' ctx' definiens
         in
           DEF {parameters = params', arguments = args', sort = sort', definiens = definiens'}
         end
       | m => raise Fail ("Failed to decode decl, " ^ J.toString m)

    fun decode' env ctx sign =
      fn [] => sign
       | (lbl, obj) :: xs =>
         let
           val decl = decodeDecl env ctx sign obj

           val sym = Abt.Sym.named lbl
           val (menv, senv, venv) = env
           val (mctx, sctx, vctx) = ctx

           val sign' = Telescope.snoc sign sym decl

           val senv' = NE.insert senv lbl sym
           val env' = (menv, senv', venv)

           val tau = case decl of SYM_DECL tau => tau | _ => SortData.OPID
           val sctx' = Abt.Sym.Ctx.insert sctx sym (RS.EXP tau)

           val ctx' = (mctx, sctx', vctx)
         in
           decode' env' ctx' sign' xs
         end
  in
    fun encode sign =
      J.Obj (encode' sign)

    val decode =
      fn J.Obj xs => decode' (NE.empty, NE.empty, NE.empty) (Abt.Metavar.Ctx.empty, Abt.Sym.Ctx.empty, Abt.Var.Ctx.empty) Telescope.empty xs
       | _ => raise Fail "Decode failed!"
  end

  exception NotFound

  fun subarguments (Th1, Th2) =
    let
      fun lookup x =
        case List.find (fn (y, v) => Abt.Metavar.eq (x, y)) Th2 of
             SOME (_, ((us, xs), tau)) => ((List.map RedPrlOperator.S.EXP us, List.map RedPrlOperator.S.EXP xs), RedPrlOperator.S.EXP tau)
           | NONE => raise NotFound
      fun go [] = true
        | go ((x, vl) :: xs) =
            (Abt.O.Ar.Vl.eq (vl, lookup x) handle _ => false)
              andalso go xs
    in
      go Th1
    end

  fun subsymbols sign (Y1, Y2) =
    let
      fun lookup u =
        case List.find (fn (v, _) => Symbol.eq (u, v)) Y2 of
             SOME (v, tau) => tau
           | NONE =>
               (case Telescope.find sign u of
                    SOME (DEF _, _) => SortData.OPID
                  | SOME (SYM_DECL tau, _) => tau
                  | NONE => raise NotFound)
      fun go [] = true
        | go ((u, tau) :: us) =
            (Abt.O.Ar.Vl.S.eq (tau, RedPrlOperator.S.EXP (lookup u)) handle _ => false)
              andalso go us
    in
      go Y1
    end

  fun guard pos msg x =
    if x then () else raise RedPrlExn.RedPrlExn (pos, msg)

  (* def is *almost* an identity, but it also does all the checking
   * necessary to make sure that everything is well-sorted and well-scoped
   * before hand
   *)
  fun def sign ({parameters, arguments, sort, definiens}, pos : Pos.t option) =
    let
      val Y' = Abt.Sym.Ctx.toList (Abt.symctx definiens)
      val G = Abt.Var.Ctx.toList (Abt.varctx definiens)
      val Th' = Abt.Metavar.Ctx.toList (Abt.metactx definiens)
      val (_, tau') = Abt.infer definiens

      val _ =
        (guard pos "Metavariable not in scope" (subarguments (Th', arguments));
         guard pos "Symbols not in scope" (subsymbols sign (Y', parameters));
         guard pos "Variables not in scope" (List.length G = 0);
         guard pos "Sort mismatch" (Abt.O.Ar.Vl.S.eq (tau', RedPrlOperator.S.EXP sort)))
    in
      DEF {parameters = parameters, arguments = arguments, sort = sort, definiens = definiens}
    end

  fun symDecl sign (sort, pos) =
    SYM_DECL sort

  fun viewDecl d = d
end
