structure StringLabel : LABEL =
struct
  open StringOrdered
  fun prime x = x ^ "'"
  fun toString x = x
end

functor Signature (Abt : ABT) : SIGNATURE  =
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

  type notation = unit

  datatype def = DEF of symctx * Abt.metacontext * Abt.abt
  datatype def_view = datatype def

  type decl =
    {def : def,
     notation : notation option}

  type sign = decl Telescope.telescope

  exception InvalidDef

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

  fun def (DEF (Y, Th, m)) =
    let
      val Y' = Abt.freeSymbols m
      val Th' = Abt.metacontext m
    in
      if submetacontext (Th', Th) andalso subsymctx (Y', Y) then
        DEF (Y, Th, m)
      else
        raise InvalidDef
    end

  fun view d = d
end
