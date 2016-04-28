structure Sequent :> SEQUENT
  where type prop = Abt.abt
  where type sort = Abt.sort
  where type var = Abt.variable
  where type metactx = Abt.metactx
  where type symctx = Abt.symctx
  where type hypctx = (Abt.abt * Abt.sort) SymbolTelescope.telescope =
struct
  type prop = Abt.abt
  type sort = Abt.sort
  type var = Abt.variable

  type metactx = Abt.metactx
  type symctx = Abt.symctx
  type hypctx = (prop * sort) SymbolTelescope.telescope

  datatype context =
    CONTEXT of
      {metactx : metactx,
       symctx : symctx,
       hypctx : hypctx}

   val emptyContext =
     CONTEXT
       {metactx = Abt.MetaCtx.empty,
        symctx = Abt.SymCtx.empty,
        hypctx = SymbolTelescope.empty}

   fun getHyps (CONTEXT {hypctx,...}) =
     hypctx

   fun getSyms (CONTEXT {symctx,...}) =
     symctx

   fun getMetas (CONTEXT {metactx,...}) =
     metactx

    fun updateHyps f (CONTEXT {metactx, symctx, hypctx}) =
      CONTEXT
        {metactx = metactx,
         symctx = symctx,
         hypctx = f hypctx}

    fun updateSyms f (CONTEXT {metactx, symctx, hypctx}) =
      CONTEXT
        {metactx = metactx,
         symctx = f symctx,
         hypctx = hypctx}

    fun updateMetas f (CONTEXT {metactx, symctx, hypctx}) =
      CONTEXT
        {metactx = f metactx,
         symctx = symctx,
         hypctx = hypctx}

  (* A sequent consists in a context (of metavariables, symbols and hypotheses)
   * and a conclusion [(P,tau)], where [tau] is the sort of the evidence to be
   * produced, and [P] is a type that refines [tau] which shall classify the
   * evidence. *)

  datatype concl =
      TRUE of prop * sort
    | TYPE of prop * sort

  (* The meaning of the sequent with respect to its context of metavariables is
   * essentially the following: If the metavariables are replaced by closed abstractions
   * that respect computation, then the sequent is evident. *)
  datatype sequent =
      >> of context * concl

  datatype generic =
      |> of (var * sort) list * sequent

  infix 4 >>
  infix 3 |>

  val conclToString =
    fn TRUE (P, tau) => ShowAbt.toString P ^ " true"
     | TYPE (P, tau) => ShowAbt.toString P ^ " type"

  fun hypothesesToString H =
    let
      open SymbolTelescope open ConsView
      val rec go =
        fn EMPTY => ""
         | CONS (x, (a, tau), tl) =>
             let
               val hyp = Symbol.toString x ^ " : " ^ ShowAbt.toString a
             in
               hyp ^ "\n" ^ go (out tl)
             end
    in
      go (out H)
    end

  fun toString (G |> H >> concl) =
        hypothesesToString (getHyps H)
          ^ "\226\138\162 "
          ^ conclToString concl
end
