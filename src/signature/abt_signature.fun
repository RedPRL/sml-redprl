functor AbtSignature (Abt : ABT)
  :> SIGNATURE
      where type term = Abt.abt
      where type symbol = Abt.symbol
      where type sort = Abt.sort
      where type metavariable = Abt.metavariable
      where type valence = Abt.valence
  =
struct
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

  type notation = unit

  datatype def = DEF of symbols * arguments * sort * term
  datatype def_view = datatype def

  type decl =
    {def : def,
     notation : notation option}

  type sign = decl StringTelescope.telescope

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

  fun def (DEF (Y, Th, tau, m)) =
    let
      val Y' = Abt.freeSymbols m
      val Th' = MCtx.toList (Abt.metacontext m)
      val (_, tau') = Abt.infer m
    in
      if subarguments (Th', Th) andalso subsymbols (Y', Y) andalso Sort.Eq.eq (tau, tau') then
        DEF (Y, Th, tau, m)
      else
        raise InvalidDef
    end

  fun view d = d
end
