structure Sequent :> SEQUENT
  where type expr = Abt.abt
  where type prop = Abt.abt
  where type sort = Abt.sort
  where type var = Abt.variable
  where type metactx = Abt.metactx
  where type hypctx = (Abt.abt * Abt.sort) SymbolTelescope.telescope =
struct
  type prop = Abt.abt
  type expr = Abt.abt
  type sort = Abt.sort
  type var = Abt.variable

  type metactx = Abt.metactx
  type hypctx = (prop * sort) SymbolTelescope.telescope

  datatype context =
    CONTEXT of
      {metactx : metactx,
       hypctx : hypctx}

  val emptyContext =
    CONTEXT
      {metactx = Abt.MetaCtx.empty,
       hypctx = SymbolTelescope.empty}

  fun getHyps (CONTEXT {hypctx,...}) =
    hypctx

  fun getMetas (CONTEXT {metactx,...}) =
    metactx

  fun updateHyps f (CONTEXT {metactx, hypctx}) =
    CONTEXT
      {metactx = metactx,
       hypctx = f hypctx}

  fun updateMetas f (CONTEXT {metactx, hypctx}) =
    CONTEXT
      {metactx = f metactx,
       hypctx = hypctx}

  (* A sequent consists in a context (of metavariables, symbols and hypotheses)
   * and a conclusion [(P,tau)], where [tau] is the sort of the evidence to be
   * produced, and [P] is a type that refines [tau] which shall classify the
   * evidence. *)

  datatype concl =
      TRUE of prop * sort
    | TYPE of prop * sort
    | EQ_MEM of expr * expr * prop
    | MEM of expr * prop
    | EQ_SYN of expr * expr
    | SYN of expr

  datatype judgment =
      >> of context * concl (* categorical sequent *)
    | |> of (var * sort) list * judgment (* generic sequent *)

  infix 4 >>
  infix 3 |>

  val conclToString =
    fn TRUE (a, tau) => ShowAbt.toString a ^ " true"
     | TYPE (a, tau) => ShowAbt.toString a ^ " type"
     | EQ_MEM (m, n, a) => ShowAbt.toString m ^ " = " ^ ShowAbt.toString n ^ " : " ^ ShowAbt.toString a
     | MEM (m, a) => ShowAbt.toString m ^ " : " ^ ShowAbt.toString a
     | EQ_SYN (r, s) => ShowAbt.toString r ^ " = " ^ ShowAbt.toString s ^ " synth"
     | SYN r => ShowAbt.toString r ^ " synth"

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

  fun toString (G |> jdg) =
        "[" ^ ListSpine.pretty (fn (x, _) => Variable.toString x) "," G ^ "] |\n"
          ^ toString jdg
    | toString (H >> concl) =
        hypothesesToString (getHyps H)
          ^ "\226\138\162 "
          ^ conclToString concl
end
