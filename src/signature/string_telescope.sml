structure StringLabel : LABEL =
struct
  open StringOrdered
  fun prime x = x ^ "'"
  fun toString x = x
end

structure StringTelescope = Telescope (StringLabel)
