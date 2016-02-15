structure Sequent : SEQUENT =
struct
  type prop = Abt.abt
  type sort = Abt.sort
  type expr = Abt.abt
  type operator = Abt.operator

  type context =
    {metactx : Abt.metactx,
     symctx : Abt.symctx,
     hypctx : (prop * sort) SymbolTelescope.telescope}

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
    | GENERAL of (Abt.variable * sort) list * sequent
  infix >>

  val conclToString =
    fn TRUE (P, tau) => ShowAbt.toString P ^ " true"
     | TYPE (P, tau) => ShowAbt.toString P ^ " type"

  fun hypothesesToString H =
    let
      open SymbolTelescope open ConsView
      val rec go =
        fn Empty => ""
         | Cons (x, (a, tau), tl) =>
             let
               val hyp = Symbol.toString x ^ " : " ^ ShowAbt.toString a
             in
               hyp ^ "\n" ^ go (out tl)
             end
    in
      go (out H)
    end

  fun toString (H >> concl) =
        hypothesesToString (#hypctx H)
          ^ "\226\138\162 "
          ^ conclToString concl
    | toString (GENERAL (xs, seq)) =
        "...| " ^ toString seq
end
