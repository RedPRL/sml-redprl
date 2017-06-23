structure ElabMonad :> ELAB_MONAD =
struct
  type 'a ann = Pos.t option * 'a

  structure DList =
  struct
    type 'a t = 'a list -> 'a list

    fun empty xs = xs

    fun fromList xs =
      fn ys => xs @ ys

    fun toList xs =
      xs []

  end

  datatype msg =
     DUMP of Fpp.doc ann
   | INFO of Fpp.doc ann
   | WARN of Fpp.doc ann

  datatype 'a res =
     SUCCESS of 'a
   | FAILURE of Fpp.doc ann

  type 'a state =
    {result : 'a res,
     messages : msg DList.t}

  type 'a t = 'a state Susp.susp

  fun force susp =
    Debug.wrap (fn _ => Susp.force susp)
    handle exn =>
      {result = FAILURE (RedPrlError.annotation exn, RedPrlError.format exn),
       messages = DList.empty}

  structure Monad =
  struct
    type 'a t = 'a t
    fun ret a =
      Susp.delay (fn () =>
        {result = SUCCESS a,
         messages = DList.empty})

    fun bind (f : 'a -> 'b t) (x : 'a t) =
      Susp.delay (fn () =>
        let
          val st = force x
        in
          case #result st of
             SUCCESS a =>
               let
                 val st' = force (f a)
               in
                 {result = #result st',
                  messages = #messages st' o #messages st}
               end
           | FAILURE msg =>
               {result = FAILURE msg,
                messages = #messages st}
        end)
  end

  structure MonadUtil = MonadUtil (Monad)
  open MonadUtil

  fun hush m =
    Susp.delay (fn () =>
      let
        val {result, messages = _} = Susp.force m
      in
        {result = result, messages = DList.empty}
      end)


  fun warn msg =
    Susp.delay (fn () =>
      {result = SUCCESS (),
       messages = DList.fromList [WARN msg]})

  fun dump msg =
    Susp.delay (fn () =>
      {result = SUCCESS (),
       messages = DList.fromList [DUMP msg]})

  fun info msg =
    Susp.delay (fn () =>
      {result = SUCCESS (),
       messages = DList.fromList [INFO msg]})

  fun fail msg =
    Susp.delay (fn () =>
      {result = FAILURE msg,
       messages = DList.empty})

  fun wrap (pos, f) =
    Debug.wrap (fn _ => ret (f ()))
    handle exn => fail (case RedPrlError.annotation exn of
                          NONE => pos
                        | SOME pos' => SOME pos',
                        RedPrlError.format exn)

  fun delay f =
    bind f (ret ())

  type ('a, 'b) alg =
    {warn : Fpp.doc ann * 'b -> 'b,
     dump : Fpp.doc ann * 'b -> 'b,
     info : Fpp.doc ann * 'b -> 'b,
     fail : Fpp.doc ann * 'b -> 'b,
     init : 'b,
     succeed : 'a * 'b -> 'b}

  fun fold (alg : ('a, 'b) alg) susp =
    let
      val st = force susp
      val messages = DList.toList (#messages st)
      val b =
        List.foldl
          (fn (INFO msg, b) => #info alg (msg, b)
            | (DUMP msg, b) => #dump alg (msg, b)
            | (WARN msg, b) => #warn alg (msg, b))
          (#init alg)
          messages
    in
      case #result st of
         SUCCESS r => #succeed alg (r, b)
       | FAILURE msg => #fail alg (msg, b)
    end
end

functor ElabMonadUtil (M : ELAB_MONAD) : ELAB_MONAD_UTIL =
struct
  open M

  val runAlg : ('a, 'a option) alg =
    {warn = fn _ => NONE,
     info = fn _ => NONE,
     dump = fn _ => NONE,
     init = NONE,
     fail = fn _ => NONE,
     succeed = fn (r, _) => SOME r}

   fun run e = fold runAlg e
end
