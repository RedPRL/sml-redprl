structure Accessor :> ACCESSOR = 
struct
  datatype t = WHOLE | PART_TYPE | PART_LEFT | PART_RIGHT

  val toString =
    fn WHOLE => "whole"
     | PART_TYPE => "type"
     | PART_LEFT => "left"
     | PART_RIGHT => "right"

  val pretty = Fpp.text o toString
end