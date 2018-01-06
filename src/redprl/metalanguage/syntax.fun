functor MlSyntax
  (type metavariable
   type jdg
   type term
   type vty
   val metaToString : metavariable -> string) : ML_SYNTAX = 
struct
  type id = MlId.t
  type metavariable = metavariable
  type jdg = jdg
  type term = term
  type vty = vty

  type metas = (metavariable * Tm.valence) list

  datatype value =
     THUNK of cmd
   | VAR of id
   | NIL
   | ABS of value * value
   | METAS of metas
   | TERM of term

  and cmd =
     BIND of cmd * id * cmd
   | RET of value
   | FORCE of value
   | FN of id * vty * cmd
   | AP of cmd * value
   | PRINT of Pos.t option * value
   | REFINE of jdg * term
   | FRESH of (string option * Tm.valence) list
   | MATCH_METAS of value * metavariable list * cmd
   | MATCH_ABS of value * id * id * cmd
   | MATCH_THM of value * id * id * cmd
   | ABORT

  fun nu (psi, cmd) =
    let
      val (Xs, vls) = ListPair.unzip psi
      val hintedVls = ListPair.mapEq (fn (X, vl) => (SOME (metaToString X), vl)) (Xs, vls)
      val xpsi = MlId.new ()
    in
      BIND (FRESH hintedVls, xpsi, MATCH_METAS (VAR xpsi, Xs, cmd))
    end

  fun termAbs (psi, term) =
    nu (psi, RET (ABS (METAS psi, TERM term)))

  fun theoremAbs (psi, jdg, script) =
    let
      val x = MlId.new ()
    in 
      nu (psi, BIND (REFINE (jdg, script), x, RET (ABS (METAS psi, VAR x))))
    end

  fun extract v = 
    let
      val xjdg = MlId.new ()
      val xtm = MlId.new ()
    in
      MATCH_THM (v, xjdg, xtm, RET (VAR xtm))
    end

  fun printExtractAbs (pos, v) = 
    let
      val xpsi = MlId.new ()
      val xthm = MlId.new ()
      val xjdg = MlId.new ()
      val xtm = MlId.new ()
    in
      MATCH_ABS (v, xpsi, xthm, MATCH_THM (VAR xthm, xjdg, xtm, PRINT (pos, ABS (VAR xpsi, VAR xtm))))
    end
    
end
