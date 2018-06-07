Tutorial
==================================

We will walk through parts of ``examples/tutorial.prl``, which was the live demo
of |RedPRL| in our `POPL 2018 tutorial`_ on Computational (Higher) Type Theory.
For further guidance, we recommend that new users consult the many other proofs
in the ``examples/`` subdirectory.

.. _POPL 2018 tutorial: https://existentialtype.wordpress.com/2018/01/15/popl-2018-tutorial/

|RedPRL| is a program logic for a functional programming language extended with
constructs for higher-dimensional reasoning. A proof in |RedPRL| is a tactic
script that constructs a program (or *extract*) and demonstrates that it
inhabits the specified type.

Getting started
---------------

Let's start by defining the function that negates a boolean:

::

  theorem Not :
    (-> bool bool)
  by {
    lam b =>
    if b then `ff else `tt
  }.

The ``lam b =>`` tactic introduces a variable ``b : bool`` in the context,
``if then else`` performs a case split, and each branch is resolved by a boolean
literal (```ff`` and ```tt``). We can inspect the proof state at any point using
a *hole*. Replace ```ff`` with ``?the-tt-case``, and run |RedPRL| again:

::

  ?the-tt-case.
  Goal #0.
    b : bool
    ---------
    bool

That is, the current subgoal has type ``bool``, and ``b : bool`` is in scope.
Replace ``?the-tt-case`` with ```ff`` once again, and follow this theorem by:

::

  print Not.

The ``print`` command displays the theorem statement and its extract. In this
case, we can prove ``Not`` with the extract directly:

::

  theorem NotDirect :
    (-> bool bool)
  by {
    `(lam [b] (if [_] bool b ff tt))
  }.

In general, we might not have a particular extract in mind, or establishing the
type of that extract may require non-trivial reasoning, so we typically choose
(or are forced) to use interactive tactics rather than specifying extracts.

|RedPRL| has a notion of exact, extensional equality of programs, written ``=``.
For example, applying ``Not`` twice is equal to the identity function.
(Function application is written ``$``.)

::

  theorem NotNot :
    (->
     [b : bool]
     (= bool ($ Not ($ Not b)) b))
  by {
    lam b => auto
  }.

This instance of ``auto`` cases on ``b``, and in each case simplifies the
left-hand side and supplies a reflexive equality.  (For example, the subgoal
``(= bool tt tt)`` is handled by the :ref:`refinement rule <bool/eq/tt>`
``refine bool/eq/tt``.)

Families of types respect equality of indices. For example, suppose we have a
boolean-indexed family of types ``family``. By virtue of the equation we just
proved, an element of the type ``($ family b)`` is also an element of the type
``($ family ($ Not ($ Not b)))``:

::

  theorem RespectEquality :
    (->
     [family : (-> [b : bool] (U 0))]
     [b : bool]
     ($ family b)
     ($ family ($ Not ($ Not b))))
  by {
    lam family b pf =>
    rewrite ($ NotNot b);       // equation to rewrite along
    [ with b' => `($ family b') // what to rewrite (i.e., b')
    , use pf
    ];
    auto
  }.

Here, ``(U 0)`` is a universe (the "type of small types"). The ``rewrite``
tactic rewrites the argument to ``family`` along the equality
``(= bool ($ Not ($ Not b)) b)`` given by ``($ NotNot b)``, taking
``pf : ($ family b)`` to a proof of ``($ family ($ Not ($ Not b))))``.

Surprisingly, the extract is just a constant function: ``(lam [x0 x1 x2] x2)``!
The reason is that at runtime, for any particular ``b``, the types
``($ family b)`` and ``($ family ($ Not ($ Not b))))`` will be exactly the same,
so there's no need for a coercion.

Cubical reasoning
-----------------

.. todo::
  This part isn't written yet!

::

  // Paths (cf equalities), like those arising from
  // equivalences via univalence, do induce computation.
  theorem FunToPair :
    (->
     [ty : (U 0 kan)]
     (-> bool ty)
     (* ty ty))
  by {
    lam ty fun =>
    {`($ fun tt), `($ fun ff)}
  }.

  theorem PathFunToPair :
    (->
     [ty : (U 0 kan)]
     (path [_] (U 0 kan) (-> bool ty) (* ty ty)))
  by {
    lam ty => abs x =>
    `(V x (-> bool ty) (* ty ty)
      (tuple [proj1 ($ FunToPair ty)] [proj2 ($ FunToPairIsEquiv ty)]))
  }.

  // We can coerce elements of (bool -> ty) to (ty * ty).
  theorem RespectPaths :
    (->
     [ty : (U 0 kan)]
     (-> bool ty)
     (* ty ty))
  by {
    lam ty fun =>
    `(coe 0~>1 [x] (@ ($ PathFunToPair ty) x) fun)
  }.

  print RespectPaths.

  // When coercing, the choice of PathFunToPair matters!
  theorem ComputeCoercion :
    (=
     (* bool bool)
     ($ RespectPaths bool (lam [b] b))
     (tuple [proj1 tt] [proj2 ff]))
  by {
    auto
  }.

foo

::

  // A constant path does not depend on its dimension.
  theorem Refl :
    (->
     [ty : (U 0)]
     [a : ty]
     (path [_] ty a a))
  by {
    lam ty a =>
    abs _ => `a
  }.

  theorem PathConcat :
    (->
     [ty : (U 0 kan)]
     [a b c : ty]
     [p : (path [_] ty a b)]
     [q : (path [_] ty b c)]
     (path [_] ty a c))
  by {
  //        p          -- x
  //     -------      |
  //    |      |      y
  //  a |      | q
  //    |      |
  //    a .... c

    lam ty a b c p q =>
    abs x =>
    `(hcom 0~>1 ty (@ p x) [x=0 [_] a] [x=1 [y] (@ q y)])
  }.

  // Although the path type is not defined by refl and J
  // (as in HoTT), we can still define J using hcom + coe.
  // The #l is an example of a parametrized definition.
  theorem J(#l:lvl) :
    (->
     [ty : (U #l kan)]
     [a : ty]
     [fam : (-> [x : ty] (path [_] ty a x) (U #l kan))]
     [d : ($ fam a (abs [_] a))]
     [x : ty]
     [p : (path [_] ty a x)]
     ($ fam x p))
  by {
    lam ty a fam d x p =>
    `(coe 0~>1
      [i] ($ fam
             (hcom 0~>1 ty a [i=0 [_] a] [i=1 [j] (@ p j)])
             (abs [j] (hcom 0~>j ty a [i=0 [_] a] [i=1 [j] (@ p j)]))) d)
  }.

  theorem JInv :
    (->
     [ty : (U 0 kan)]
     [a b : ty]
     [p : (path [_] ty a b)]
     (path [_] ty b a))
  by {
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
  }.

  print JInv.

foo
