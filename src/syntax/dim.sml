structure Dim :> DIM =
struct
  datatype 'i dim =
     NAME of 'i
   | DIM0
   | DIM1

  type 'i t = 'i dim

  val support =
    fn NAME u => [(u, SortData.DIM)]
     | _ => []

  fun eq f =
    fn (NAME u, NAME v) => f (u, v)
     | (DIM0, DIM0) => true
     | (DIM1, DIM1) => true
     | _ => false

  fun toString f =
    fn NAME u => "dim[" ^ f u ^ "]"
     | DIM0 => "dim0"
     | DIM1 => "dim1"

  fun map f =
    fn NAME u => NAME (f u)
     | DIM0 => DIM0
     | DIM1 => DIM1

  fun subst eq (r, u) =
    fn r' as NAME v => if eq (u, v) then (true, r) else (false, r')
     | r' => (false, r')

  local
    structure J = Json
  in
    fun encode f =
      fn NAME u => J.Obj [("dim", f u)]
       | DIM0 => J.String "dim0"
       | DIM1 => J.String "dim1"

    fun decode f =
      fn J.Obj [("dim", u)] => Option.map NAME (f u)
       | J.String "dim0" => SOME DIM0
       | J.String "dim1" => SOME DIM1
       | _ => NONE
  end
end

functor DimSpan (Dim : DIM) : DIM_SPAN =
struct
  type 'i dim = 'i Dim.t

  type 'i dim_span =
    {starting : 'i Dim.t,
     ending : 'i Dim.t}

  type 'i t = 'i dim_span

  fun new (r, r') =
    {starting = r,
     ending = r'}

  fun support {starting, ending} =
    Dim.support starting @ Dim.support ending

  fun eq f (s1 : 'i t, s2 : 'i t) =
    Dim.eq f (#starting s1, #starting s2)
      andalso Dim.eq f (#ending s1, #ending s2)

  fun toString f {starting, ending} =
    Dim.toString f starting
      ^ " ~> "
      ^ Dim.toString f ending

  fun map f {starting, ending} =
    {starting = Dim.map f starting,
     ending = Dim.map f ending}

  fun subst eq (r, u) {starting, ending} =
    let
      val (didSubst1, starting') = Dim.subst eq (r, u) starting
      val (didSubst2, ending') = Dim.subst eq (r, u) ending
    in
      (didSubst1 orelse didSubst2, new (starting', ending'))
    end

  local
    structure J = Json
  in
    fun encode f {starting, ending} =
      J.Obj
        [("starting", Dim.encode f starting),
         ("ending", Dim.encode f ending)]

    fun decode f =
      fn J.Obj [("starting", starting), ("ending", ending)] =>
         (case (Dim.decode f starting, Dim.decode f ending) of
             (SOME r, SOME r') => SOME {starting = r, ending = r'}
           | _ => NONE)
       | _ => NONE
  end
end

functor DimVec (Dim : DIM) : DIM_VEC =
struct
  type 'i dim = 'i Dim.t
  type 'i dim_vec = 'i dim list
  type 'i t = 'i dim_vec

  fun support rs =
    List.foldl (fn (r, xs) => Dim.support r @ xs) [] rs

  fun eq f =
    ListPair.allEq (Dim.eq f)

  fun toString f =
    ListSpine.pretty (Dim.toString f) ","

  fun map f = List.map (Dim.map f)

  local
    structure J = Json

    (* TODO: remove copy-pasta and make OptionUtil public *)
    fun traverseOpt f xs =
      SOME (List.map (Option.valOf o f) xs)
        handle _ => NONE
  in
    fun encode f =
      J.Array o List.map (Dim.encode f)

    fun decode f =
      fn J.Array rs => traverseOpt (Dim.decode f) rs
       | _ => NONE
  end

  fun subst eq (r, u) =
    fn [] => (false, [])
     | r' :: rs =>
         let
           val (didSubst, r'') = Dim.subst eq (r, u) r'
           val (didSubst', rs') = subst eq (r, u) rs
         in
           (didSubst orelse didSubst', r'' :: rs')
         end
end

structure DimSpan = DimSpan (Dim)
structure DimVec = DimVec (Dim)
