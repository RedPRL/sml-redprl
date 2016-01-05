structure ScriptOperatorData =
struct
  type metadata = TacticMetadata.t

  type intro_params =
    {rule : int option}

  type thenf_params =
    {focus : int}

  type thenl_params =
    {length : int}

  (* We use symbols/atoms to index into the context. *)
  type 'i hyp_params =
    {target : 'i}

  (* In the old system, tactics like [ELIM] would take
   * a list of fresh names to use, but not we need only take a
   * number from which we can compute a valence, since we have a
   * proper treatment of nominal binding. *)
  type 'i elim_params =
    {target : 'i,
     bindings : int}

  datatype 'i script_operator =
      THEN
    | THENF of thenf_params
    | THENL of thenl_params
    | INTRO of intro_params * metadata
    | ELIM of 'i elim_params * metadata
    | HYP of 'i hyp_params * metadata
end
