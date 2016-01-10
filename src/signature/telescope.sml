structure StringLabel : LABEL =
struct
  open StringOrdered
  fun prime x = x ^ "'"
  fun toString x = x
end

structure SymbolLabel : LABEL =
struct
  open Symbol Symbol.Eq Symbol.Show
  fun prime x =
    named (toString x ^ "'")
end

structure StringTelescope = Telescope (StringLabel)
structure SymbolTelescope = Telescope (SymbolLabel)
