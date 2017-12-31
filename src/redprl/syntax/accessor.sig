signature ACCESSOR = 
sig
  datatype t = WHOLE | PART_TYPE | PART_LEFT | PART_RIGHT
  val pretty : t -> Fpp.doc
end