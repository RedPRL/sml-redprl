structure AbtSignature : ABT_SIGNATURE =
struct
  type opid = Abt.symbol
  structure Telescope = SymbolTelescope

  structure Arity = Abt.Operator.Arity
  structure Valence = Arity.Valence
  structure Sort = Valence.Sort
  structure Symbol = Abt.Symbol
  structure MCtx = Abt.MetaCtx

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

  exception NotFound

  fun subarguments (Th1, Th2) =
    let
      fun lookup x =
        case List.find (fn (y, v) => Abt.Metavariable.eq (x, y)) Th2 of
             SOME (_, v) => v
           | NONE => raise NotFound
      fun go [] = true
        | go ((x, vl) :: xs) =
            (Valence.eq (vl, lookup x) handle _ => false)
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
                    SOME _ => SortData.OPID
                  | NONE => raise NotFound)
      fun go [] = true
        | go ((u, tau) :: us) =
            (Sort.eq (tau, lookup u) handle _ => false)
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
      val Y' = Abt.SymCtx.toList (Abt.symctx definiens)
      val G = Abt.VarCtx.toList (Abt.varctx definiens)
      val Th' = Abt.MetaCtx.toList (Abt.metactx definiens)
      val (_, tau') = Abt.infer definiens

      val _ =
        (guard "Metavariable not in scope" (subarguments (Th', arguments));
         guard "Symbols not in scope" (subsymbols sign (Y', parameters));
         guard "Variables not in scope" (List.length G = 0);
         guard "Sort mismatch" (Sort.eq (tau', sort)))
    in
      DEF {parameters = parameters, arguments = arguments, sort = sort, definiens = definiens}
    end

  fun undef (DEF d) = d
end
