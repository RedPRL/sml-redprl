structure ScriptOperatorData =
struct
  (* We use symbols/atoms to index into the context. *)
  type 'i hyp_params =
    {target : 'i}

  type 'i elim_params =
    {target : 'i}

  type intro_params =
    {rule : int option}

  datatype 'i script_operator =
      SEQ of int
    | ALL | EACH | FOCUS of int
    | REC
    | INTRO of intro_params
    | ELIM of 'i elim_params
    | HYP of 'i hyp_params
    | ID
end
