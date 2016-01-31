structure SmallStep :> SMALL_STEP =
struct
  datatype 'a t =
      STEP of 'a
    | FINAL

  val ret = STEP

  fun map f =
    fn STEP a => STEP (f a)
     | FINAL => FINAL

  fun bind f =
    fn STEP a => f a
     | FINAL => FINAL
end
