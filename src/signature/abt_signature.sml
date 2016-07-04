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

  type sign = decl Telescope.telescope

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

    fun go sign =
      case out sign of
         EMPTY => []
       | CONS (sym, decl, sign') =>
         let
           val lbl = Symbol.toString sym
           val obj = encodeDecl decl
         in
           (lbl, obj) :: go sign'
         end
  in
    fun encode sign = J.Obj (go sign)
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
                    SOME (DEF _) => SortData.OPID
                  | SOME (SYM_DECL tau) => tau
                  | NONE => raise NotFound)
      fun go [] = true
        | go ((u, tau) :: us) =
            (Abt.O.Ar.Vl.S.eq (tau, RedPrlOperator.S.EXP (lookup u)) handle _ => false)
              andalso go us
    in
      go Y1
    end

  fun guard msg x =
    if x then () else raise Fail msg

  (* def is *almost* an identity, but it also does all the checking
   * necessary to make sure that everything is well-sorted and well-scoped
   * before hand
   *)
  fun def sign {parameters, arguments, sort, definiens} =
    let
      val Y' = Abt.Sym.Ctx.toList (Abt.symctx definiens)
      val G = Abt.Var.Ctx.toList (Abt.varctx definiens)
      val Th' = Abt.Metavar.Ctx.toList (Abt.metactx definiens)
      val (_, tau') = Abt.infer definiens

      val _ =
        (guard "Metavariable not in scope" (subarguments (Th', arguments));
         guard "Symbols not in scope" (subsymbols sign (Y', parameters));
         guard "Variables not in scope" (List.length G = 0);
         guard "Sort mismatch" (Abt.O.Ar.Vl.S.eq (tau', RedPrlOperator.S.EXP sort)))
    in
      DEF {parameters = parameters, arguments = arguments, sort = sort, definiens = definiens}
    end

  fun symDecl sign sort =
    SYM_DECL sort

  fun viewDecl d = d
end
