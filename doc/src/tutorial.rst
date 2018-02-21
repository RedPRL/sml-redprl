Tutorial
==================================

We will walk through parts of ``examples/tutorial.prl``, which was the live demo
of RedPRL in our `POPL 2018 tutorial`_ on Computational (Higher) Type Theory.
For further guidance, we recommend that new users consult the many other proofs
in the ``examples/`` subdirectory.

.. _POPL 2018 tutorial: https://existentialtype.wordpress.com/2018/01/15/popl-2018-tutorial/

.. todo::
  Write the tutorial.

::

  Thm Not : [
    (-> bool bool)
  ] by [
    lam b =>
    if b then `ff else `tt
  ].

  Print Not.

  // (not(not(b)) == b) because it holds for every closed boolean.
  Thm NotNot : [
    (->
     [b : bool]
     (= bool ($ Not ($ Not b)) b))
  ] by [
    lam b =>
    // The next four lines can be replaced by auto.
    unfold Not;
    if b
    then (reduce at left; refine bool/eq/tt)
    else (reduce at left; refine bool/eq/ff)
  ].

  Print NotNot.

  // Type families respect equality proofs.
  Thm RespectEquality : [
    (->
     [family : (-> [b : bool] (U 0))]
     [b : bool]
     ($ family b)
     ($ family ($ Not ($ Not b))))
  ] by [
    lam family b pf =>
    rewrite ($ NotNot b);
    [ with b' => `($ family b')
    , use pf
    ];
    auto
  ].


  // Extract does not mention the equality proof!
  // (No need to ``transport'' at runtime.)
  Print RespectEquality.

  // In fact, all proofs of (not(not(b)) == b) are equal.
  Thm EqualityIrrelevant : [
    (=
      (-> [b : bool] (= bool ($ Not ($ Not b)) b))
      NotNot
      (lam [b] ax))
  ] by [
    auto
  ].

  Print EqualityIrrelevant.

  // Paths (cf equalities), like those arising from
  // equivalences via univalence, do induce computation.
  Thm FunToPair : [
    (->
     [ty : (U 0 kan)]
     (-> bool ty)
     (* ty ty))
  ] by [
    lam ty fun =>
    {`($ fun tt), `($ fun ff)}
  ].

  // ---------------------------------------------------------
  // Part Two
  // ---------------------------------------------------------

  // A constant path does not depend on its dimension.
  Thm Refl : [
    (->
     [ty : (U 0)]
     [a : ty]
     (path [_] ty a a))
  ] by [
    lam ty a =>
    abs _ => `a
  ].

  // The path structure of each type is defined in terms of
  // its constituent types.
  Thm FunPath : [
    (->
     [a b : (U 0)]
     [f g : (-> a b)]
     (path [_] (-> a b) f g)
     [arg : a]
     (path [_] b ($ f arg) ($ g arg)))
  ] by [
    lam a b f g p =>
    lam arg => abs x =>
      `($ (@ p x) arg)
  ].


  Print FunPath.

  Thm PathInv : [
    (->
     [ty : (U 0 kan)]
     [a b : ty]
     [p : (path [_] ty a b)]
     (path [_] ty b a))
  ] by [
  //        a          -- x
  //     -------      |
  //    |      |      y
  //  p |      | a
  //    |      |
  //    b .... a

    lam ty a b p =>
    abs x =>
    `(hcom 0~>1 ty a [x=0 [y] (@ p y)] [x=1 [_] a])
  ].

  Thm PathConcat : [
    (->
     [ty : (U 0 kan)]
     [a b c : ty]
     [p : (path [_] ty a b)]
     [q : (path [_] ty b c)]
     (path [_] ty a c))
  ] by [
  //        p          -- x
  //     -------      |
  //    |      |      y
  //  a |      | q
  //    |      |
  //    a .... c

    lam ty a b c p q =>
    abs x =>
    `(hcom 0~>1 ty (@ p x) [x=0 [_] a] [x=1 [y] (@ q y)])
  ].

  Thm InvRefl : [
    (->
     [ty : (U 0 kan)]
     [a : ty]
     (path
       [_] (path [_] ty a a)
       ($ PathInv ty a a (abs [_] a))
       (abs [_] a)))
  ] by [
    // See diagram!
    lam ty a =>
    abs x y =>
    `(hcom 0~>1 ty a
      [x=0 [z] (hcom 0~>z ty a [y=0 [_] a] [y=1 [_] a])]
      [x=1 [_] a]
      [y=0 [_] a]
      [y=1 [_] a])
  ].

  // Although the path type is not defined by refl and J
  // (as in HoTT), we can still define J using hcom + coe.
  // The #l is an example of a parametrized definition.
  Thm J(#l:lvl) : [
    (->
     [ty : (U #l kan)]
     [a : ty]
     [fam : (-> [x : ty] (path [_] ty a x) (U #l kan))]
     [d : ($ fam a (abs [_] a))]
     [x : ty]
     [p : (path [_] ty a x)]
     ($ fam x p))
  ] by [
    lam ty a fam d x p =>
    `(coe 0~>1
      [i] ($ fam
             (hcom 0~>1 ty a [i=0 [_] a] [i=1 [j] (@ p j)])
             (abs [j] (hcom 0~>j ty a [i=0 [_] a] [i=1 [j] (@ p j)]))) d)
  ].

  Thm JInv : [
    (->
     [ty : (U 0 kan)]
     [a b : ty]
     [p : (path [_] ty a b)]
     (path [_] ty b a))
  ] by [
    lam ty a b p =>
    exact
      ($ (J #lvl{0})
         ty
         a
         (lam [b _] (path [_] ty b a))
         (abs [_] a)
         b
         p)
    ; auto
    //; unfold J; reduce at left right; ?
  ].

  Print JInv.
