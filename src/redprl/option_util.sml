structure OptionUtil =
struct
  fun eq f =
    fn (NONE, NONE) => true
     | (SOME a, SOME b) => f (a, b)
     | _ => false

  fun concat f =
    fn NONE => []
     | SOME a => f a
end
