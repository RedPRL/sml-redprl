structure ListUtil =
struct
  local
    fun findIndex' p i : 'a list -> (int * 'a) option =
      fn [] => NONE
       | x :: l =>
           if p x then SOME (i, x)
           else findIndex' p (i+1) l
  in
    fun findIndex p l = findIndex' p 0 l

    fun findEqIndex x l = findIndex (fn y => x = y) l
  end
  
  fun mapWithIndex f = 
    let
      fun go i [] = []
        | go i (x :: xs) = f (i, x) :: go (i + 1) xs
    in
      go 0
    end
end
