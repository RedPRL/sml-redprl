structure ScriptOperatorData =
struct
  type metadata = TacticMetadata.t

  type then_params =
    {bindings : int}

  type thenf_params =
    {focus : int,
     bindings : int}

  type thenl_params =
    {bindings : int}

  (* We use symbols/atoms to index into the context. *)
  type 'i hyp_params =
    {target : 'i}

  type 'i elim_params =
    {target : 'i,
     hasTerm : bool}

  type intro_params =
    {rule : int option,
     hasTerm : bool}

  type bind_params =
    { bindings : int }

  type focus_params =
    { focus : int }

  datatype 'i script_operator =
      BIND of bind_params
    | FOCUS of focus_params
    | PAR
    | INTRO of intro_params * metadata
    | ELIM of 'i elim_params * metadata
    | HYP of 'i hyp_params * metadata

  (* The syntax of tactic scripts is arranged such that the sequencing
   * tactical BIND may bind any number of symbols. For instance,
   *
   *     p, q <- elim h;
   *     hyp p
   *
   * is the concrete syntax for
   *
   *     bind{2}(elim[h]; {p,q}. hyp[p])
   *
   * In the _dynamics_ for tactic scripts, we will unbind our nominal
   * abstractions and compile the above to the following ML code:
   *
   *     let
   *       val (p, q) = (fresh "p", fresh "q")
   *     in
   *       THEN (ELIM (h, [p, q]), HYP p)
   *     end
   *)
end
