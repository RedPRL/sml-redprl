structure ListUtil =
struct
  local
    fun find_index' p i : 'a list -> (int * 'a) option =
      fn [] => NONE
       | x :: l =>
           if p x then SOME (i, x)
           else find_index' p (i+1) l
  in
    fun find_index p l = find_index' p 0 l

    fun find_eq_index x l = find_index (fn y => x = y) l
  end
end
