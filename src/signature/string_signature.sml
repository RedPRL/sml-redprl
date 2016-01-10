structure StringSignature
  :> SIGNATURE
       where type term = string
       where type symbol = string
       where type sort = string
       where type metavariable = string
       where type valence = string
   =
struct
  type term = string
  type symbol = string
  type sort = string
  type metavariable = string
  type valence = string
  type symbols = (symbol * sort) list
  type arguments = (metavariable * valence) list
  type notation = unit (* TODO *)

  datatype def = DEF of symbols * arguments * sort * term
  datatype def_view = datatype def

  type decl =
    {def : def,
     notation : notation option}

  type sign = decl StringTelescope.telescope

  exception InvalidDef

  fun def x = x
  fun view x = x
end
