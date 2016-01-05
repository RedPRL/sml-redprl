structure StringLabel : LABEL =
struct
  open StringOrdered
  fun prime x = x ^ "'"
  fun toString x = x
end

functor Development (Abt : ABT) : DEVELOPMENT =
struct
  type opid = string
  structure Abt = Abt
  structure Arity = Abt.Operator.Arity
  structure Valence = Arity.Valence
  structure Sort = Arity.Sort
  structure Symbol = Abt.Symbol
  structure MCtx = Abt.Metacontext

  structure Telescope = Telescope (StringLabel)

  type symctx = (Abt.symbol * Abt.sort) list
  datatype decl = DECL of symctx * Abt.metacontext * Abt.abt
  datatype view = datatype decl

  type development = decl Telescope.telescope

  exception InvalidDecl

  fun submetacontext (Th1, Th2) =
    let
      fun go [] = true
        | go ((x, vl) :: xs) =
            (Valence.Eq.eq (vl, MCtx.lookup Th2 x) handle _ => false)
              andalso go xs
    in
      go (MCtx.toList Th1)
    end

  fun subsymctx (Y1, Y2) =
    let
      exception NotFound
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

  fun decl (DECL (Y, Th, m)) =
    let
      val Y' = Abt.freeSymbols m
      val Th' = Abt.metacontext m
    in
      if submetacontext (Th', Th) andalso subsymctx (Y', Y) then
        DECL (Y, Th, m)
      else
        raise InvalidDecl
    end

  fun view d = d
end
