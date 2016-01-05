structure ScriptOperatorData =
struct
  (* TODO: add metadata *)

  type intro_params =
    {rule : int option}

  type thenf_params =
    {focus : int}

  type thenl_params =
    {length : int}

  datatype 'i script_operator =
      THEN
    | THENF of thenf_params
    | THENL of thenl_params
    | INTRO of intro_params
end
