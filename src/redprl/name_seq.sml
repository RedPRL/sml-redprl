structure NameSeq : NAME_SEQ =
struct
  type 'a seq = int -> 'a

  fun at alpha i =
    alpha i

  fun prepend us =
    let
      val n = List.length us
    in
      fn alpha => fn i =>
        if i < n then
          List.nth (us, i)
        else
          alpha (i - n)
    end

  fun bite n alpha =
    fn i =>
      alpha (i + n)

  fun probe alpha  =
    let
      val mref = ref 0
      fun updateModulus i = if !mref < i then mref := i else ()
      fun beta i = (updateModulus (i + 1); alpha i)
    in
      (beta, mref)
    end
end
