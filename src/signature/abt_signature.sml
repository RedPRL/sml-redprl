structure AbtSignature : ABT_SIGNATURE =
struct
  type opid = Abt.symbol
  structure Telescope = SymbolTelescope

  structure Arity = Abt.Operator.Arity
  structure Valence = Arity.Valence
  structure Sort = Arity.Sort
  structure Symbol = Abt.Symbol
  structure MCtx = Abt.Metacontext

  type term = Abt.abt
  type symbol = Abt.symbol
  type sort = Abt.sort
  type metavariable = Abt.metavariable
  type valence = Abt.valence
  type arguments = (metavariable * valence) list
  type symbols = (symbol * sort) list

  type def =
    {parameters : symbols,
     arguments : arguments,
     sort : sort,
     definiens : term}

  datatype decl = DEF of def

  type sign = decl Telescope.telescope

  exception InvalidDef
  exception NotFound

  fun subarguments (Th1, Th2) =
    let
      fun lookup x =
        case List.find (fn (y, v) => Abt.Metavariable.Eq.eq (x, y)) Th2 of
             SOME (_, v) => v
           | NONE => raise NotFound
      fun go [] = true
        | go ((x, vl) :: xs) =
            (Valence.Eq.eq (vl, lookup x) handle _ => false)
              andalso go xs
    in
      go Th1
    end

  fun subsymbols (Y1, Y2) =
    let
      fun lookup u =
        case List.find (fn (v, _) => Symbol.Eq.eq (u, v)) Y2 of
             SOME (v, tau) => tau
           | NONE => raise NotFound
      fun go [] = true
        | go ((u, tau) :: us) =
            (Sort.Eq.eq (tau, lookup u) handle _ => false)
              andalso go us
    in
      go Y1
    end

  (* def is *almost* an identity, but it also does all the checking
   * necessary to make sure that everything is well-sorted and well-scoped
   * before hand
   *)
  fun def {parameters, arguments, sort, definiens} =
    let
      val Y' = Abt.freeSymbols definiens
      val Th' = MCtx.toList (Abt.metacontext definiens)
      val (_, tau') = Abt.infer definiens
    in
      if subarguments (Th', arguments) andalso subsymbols (Y', parameters) andalso Sort.Eq.eq (tau', sort) then
        DEF {parameters = parameters, arguments = arguments, sort = sort, definiens = definiens}
      else
        raise InvalidDef
    end

  fun undef (DEF d) = d
end
