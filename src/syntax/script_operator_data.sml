structure ScriptOperatorData =
struct
  type metadata = TacticMetadata.t

  type then_params =
    {bindings : int}

  type thenf_params =
    {focus : int,
     bindings : int}

  type thenl_params =
    {length : int}

  (* We use symbols/atoms to index into the context. *)
  type 'i hyp_params =
    {target : 'i}

  type 'i elim_params =
    {target : 'i,
     term : bool}

  type intro_params =
    {rule : int option,
     term : bool}

  datatype 'i script_operator =
      THEN of then_params
    | THENF of thenf_params
    | THENL of thenl_params
    | INTRO of intro_params * metadata
    | ELIM of 'i elim_params * metadata
    | HYP of 'i hyp_params * metadata
end
