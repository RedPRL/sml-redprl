Refinement rules
==================================

.. todo::
  Fill in the refinement rules listed below.

Booleans
--------

:index:`bool/eqtype`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
::

  H >> bool = bool in (U #l #k)

:index:`bool/eq/tt`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
::

  H >> tt = tt in bool

:index:`bool/eq/ff`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
::

  H >> ff = ff in bool

:index:`bool/eq/if`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

  H >> (if [x] (#c0 x) #m0 #t0 #f0) = (if [x] (#c1 x) #m1 #t1 #f1) in #ty
  where H >> #m0 = #m1 synth ~> bool, psi
  | H >> #t0 = #t1 in (#c0 tt)
  | H >> #f0 = #f1 in (#c0 ff)
  | H, x:bool >> (#c0 x) = (#c1 x) type
  | psi
  | H >> (#c0 #m0) <= #ty type


Natural numbers and integers
----------------------------

:index:`nat/eqtype`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
::

  H >> nat = nat in (U #l #k)

:index:`nat/eq/zero`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
::

  H >> (nat 0) = (nat 0) in nat

:index:`nat/eq/succ`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
::

  H >> (succ #n) = (succ #m) in nat
  | H >> #n = #m in nat

:index:`nat/eq/nat-rec`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

  H >> (nat-rec [x] (#c0 x) #m0 #n0 [a b] (#p0 a b)) = (nat-rec [x] (#c1 x) #m1 #n1 [a b] (#p1 a b)) in #ty
  | H >> #m0 = #m1 in nat
  | H >> #n0 = #n1 in (#c0 (nat 0))
  | H, a:nat, b:(#c0 a) >> #p0 a b = #p1 a b in (#c0 (succ a))
  | H, x:nat >> (#c0 x) = (#c1 x) type
  | H >> (#c0 #m0) <= #ty type

:index:`int/eqtype`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
::

  H >> int = int in (U #l #k)

:index:`int/eq/pos`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
::

  H >> (pos #m) = (pos #n) in int
  | H >> #m = #n in nat

:index:`int/eq/negsucc`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
::

  H >> (negsucc #m) = (negsucc #n) in int
  | H >> #m = #n in nat

:index:`int/eq/int-rec`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
::

  H >> (int-rec [x] (#e0 x) #m0 [a] (#n0 a) [b] (#p0 b)) = (int-rec [x] (#e1 x) #m1 [a] (#n1 a) [b] (#p1 b)) in #ty
  | H >> #m0 = #m1 in int
  | H, b:nat >> (#p0 b) = (#p1 b) in #e0 (pos b)
  | H, a:nat >> (#n0 a) = (#n1 a) in #e0 (negsucc a)
  | H, x:int >> (#e0 x) = (#e1 x) type
  | H >> (#e0 m0) <= #ty type

Void
----

:index:`void/eqtype`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
::

  H >> void = void in (U #l #k)

Circle
------

:index:`s1/eqtype`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
::

  H >> S1 = S1 in (U #l #k)
  where kan <= #k universe

:index:`s1/eq/base`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
::

  H >> base = base in S1

:index:`s1/eq/loop`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
::

  H >> loop #r = loop #r in S1

:index:`s1/eq/fcom`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`s1/eq/s1-rec`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
::

  H >> (S1-rec [x] (#c0 x) #m0 #b0 [u] #l0) = (S1-rec [x] (#c1 x) #m1 #b1 [u] #l1) in #ty
  | H >> #m0 = #m1 in S1
  | H >> #b0 = #b1 in (#c0 base)
  | H, u:dim >> (#l0 u) = (#l1 u) in (#c0 (loop u))
  | H >> (#l0 0) = #b0 in (#c0 base)
  | H >> (#l0 1) = #b0 in (#c0 base)
  | H, x:S1 >> (#c0 x) = (#c1 x) kan type
  | H >> (#c0 #m0) <= #ty type

:index:`s1/beta/loop`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
::

  H >> (S1-rec [x] (#c x) (loop #r) #b [u] (#l u)) = #m in #ty
  | H >> (#l #r) = #m in #ty
  | H, #r=0 >> #b = #m in #ty
  | H, #r=1 >> #b = #m in #ty

Dependent functions
-------------------

:index:`fun/eqtype`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

  H >> (-> [x : #a0] (#b0 x)) = (-> [x : #a1] (#b1 x)) in (U #l #k)
  where
    (#k/dom, #k/cod) <-
      (discrete, discrete) if #k == discrete
      (coe, kan) if #k == kan
      (pre, hcom) if #k == hcom
      (coe, coe) if #k == coe
      (pre, pre) if #k == pre
  | H >> #a0 = #a1 in (U #l #k/dom)
  | H, x:#a0 >> (#b0 x) = (#b1 x) in (U #l #k/cod)

:index:`fun/eq/lam`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

  H >> (lam [x] (#e0 x)) = (lam [x] (#e1 x)) in (-> [x : #a] (#b x))
  | H, x:#a >> (#e0 x) = (#e1 x) in (#b x)
  | H >> #a type

:index:`fun/intro`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

  H >> (-> [x : #a] (#b x)) ext (lam [x] (#e x))
  | H, x:#a >> (#b x) ext (#e x)
  | H >> #a type

:index:`fun/eq/eta`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

  H >> #e = #f in (-> [x : #a] (#b x))
  | H >> (lam [x] ($ #e x)) = #f in (-> [x : #a] (#b x))
  | H >> #e = #e in (-> [x : #a] (#b x))


:index:`fun/eq/app`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

  H >> ($ #f0 #e0) = ($ #f1 #e1) in #ty
  where H >> #f0 = #f1 synth ~> (-> [x : #a] (#b x)), psi
  | H >> #e0 = #e1 in #a
  | psi
  | H >> (#cod #e0) <= #ty type

Records
-------

:index:`record/eqtype`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

  H >> (record [lbl/a : #a0] ... [lbl/b : (#b0 lbl/a ...)])
       = (record [lbl/a : #a1] ... [lbl/b : (#b1 lbl/a ...)])
       in (U #l #k)
  where
    (#k/hd, #kltl) <-
      (discrete, discrete) if #k == discrete
      (kan, kan) if #k == kan
      (hcom, kan) if #k == hcom
      (coe, coe) if #k == coe
      (pre, pre) if #k == pre
  | H >> #a0 = #a1 in (U #l #k/hd)
  | ...
  | H, x : #a0, ... >> (#b0 x ...) = (#b1 x ...) in (U #l #k/tl)

.. todo::

  The choice of kinds ``#k/hd`` and ``#k/tl`` looks a little fishy; is this
  exactly what would be generated if a record were encoded as an iterated sigma
  type?


:index:`record/eq/tuple`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

  H >> (tuple [lbl/a #p0] ... [lbl/b #q0])
       = (tuple [lbl/a #p1] ... [lbl/b #q1])
       in (record [lbl/a : #a] ... [lbl/b : (#b lbl/a ...)])
  | H >> #p0 = #p1 in #a
  | ...
  | H >> #q0 = #q1 in (#b #p0 ...)
  | ...
  | H, x:#a, ... >> (#b x ...) type

:index:`record/eq/eta`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

  H >> #e0 = #e1 in (record [lbl/a : #a] ... [lbl/b : (#b lbl/a ...)])
  | H >> (tuple [lbl/a (! lbl/a #e0)] ... [lbl/b (! lbl/b #e0)])
  |      = #e1 in (record [lbl/a : #a] ... [lbl/b : (#b lbl/a ...)])
  | H >> #e0 in (record [lbl/a : #a] ... [lbl/b : (#b lbl/a ...)])


:index:`record/eq/proj`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

  H >> (! lbl #e0) = (! lbl #e1) in #ty
  where H >> #e0 = #e1 synth ~> (record [lbl0 : #a0] ... [lbl : (#a ...)] ...), psi
  | psi
  | H >> (#a (! lbl0  #e0) ...) <= #ty type

:index:`record/intro`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

  H >> (record [lbl/a : #a] ... [lbl/b : (#b lbl/a ...)])
       ext (tuple [lbl/a #p/a] ... [lbl/b #p/b])
  | H >> #a ext #p/a
  | ...
  | H >> (#b #p/a ...) ext #p/b
  | ...
  | H, x:#a, ... >> (#b x ...) type

Paths
-----

:index:`path/eqtype`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
::

  H >> (path [u] (#a0 u) #m0 #n0) = (path [u] (#a1 u) #m1 #n1) in (U #l #k)
  where
    #ka <-
      discrete if #k == discrete
      kan if #k == kan
      hcom if #k == hcom
      kan if #k == coe
      pre if #k == pre
  | H, u:dim >> (#a0 u) = (#a1 u) in (U #l #ka)
  | H >> #m0 = #m1 in (#a0 0)
  | H >> #n0 = #n1 in (#a0 1)

:index:`path/eq/abs`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
::

  H >> (abs [v] (#m0 v)) = (abs [v] (#m1 v)) in (path [v] (#a v) #p0 #p1)
  | H, v:dim >> #m0 v = #m1 v in (#a v)
  | H >> (#m0 0) = #p0 in (#a 0)
  | H >> (#m0 1) = #p1 in (#a 1)

:index:`path/intro`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
::

  H >> (path [u] (#a u) #p0 #p1) ext (abs [u] (#m u))
  | H, u:dim >> (#a u) ext (#m u)
  | H >> (#m 0) = #p0 in (#a 0)
  | H >> (#m 1) = #p1 in (#a 1)

:index:`path/eq/eta`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
::

  H >> #m = #n in (path [u] (#a u) #p0 #p1)
  | H >> (abs [u] (#m u)) = #n in (path [u] (#a u) #p0 #p1)
  | H >> #m = #m in (path [u] (#a u) #p0 #p1)

:index:`path/eq/app`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
::

  H >> (@ #m0 #r) = (@ #m1 #r) in #ty
  where H >> #m0 = #m1 synth ~> (path [u] (#a u) #p0 #p1), psi
  | psi
  | H >> (#a #r) = #ty type

:index:`path/eq/app/const`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
::

  H >> (@ #m #r) = #p in #a
  where
    H >> #m = #m synth ~> (path [x] (#ty x) #p0 #p1), psi
    #pr <-
      #p0 if #r == 0
      #p1 if #r == 1
  | H >> #pr = #p in #a
  | psi
  | H >> #ty #r <= #a type


:index:`path/eq/from-line`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
::

  H >> #m0 = #m1 in (path [x] (#ty x) #n0 #n1)
  | H >> #m0 = #m1 in (line [x] (#ty x))
  | H >> #n0 = (@ #m0 0) in (#ty 0)
  | H >> #n1 = (@ #m1 1) in (#ty 1)

Lines
-----

:index:`line/eqtype`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
::

  H >> (line [u] (#a0 u)) = (line [u] (#a1 u)) in (U #l #k)
  where
    #ka <-
      discrete if #k == discrete
      kan if #k == kan
      hcom if #k == hcom
      kan if #k == coe
      pre if #k == pre
  | H, u:dim >> (#a0 u) = (#a1 u) in (U #l #ka)


:index:`line/eq/abs`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
::

  H >> (abs [u] (#m0 u)) = (abs [u] (#m1 u)) in (line [u] (#a u))
  | H, u:dim >> #m0 u = #m1 u in (#a u)

:index:`line/intro`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
::

  H >> (line [u] (#a u)) ext (abs [u] (#m u))
  | H, u:dim >> (#a u) ext (#m u)

:index:`line/eq/eta`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
::

  H >> #m = #n in (line [u] (#a u))
  | H >> #m in (line [u] (#a u))
  | H >> (abs [u] (@m u)) = #n in (line [u] (#a u))

:index:`line/eq/app`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
::

  H >> (@ #m0 #r) = (@ #m0 #r) in #ty
  where H >> #m0 = #m1 synth ~> (line [u] (#a u)), psi
  | psi
  | H >> (#a #r) <= #ty type

Pushouts
--------

:index:`pushout/eqtype`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
::

  H >> (pushout #a0 #b0 #c0 [x] (#f0 x) [x] (#g0 x)) = (pushout #a1 #b1 #c1 [x] (#f1 x) [x] (#g1 x)) in (U #l #k)
  where
    (#k/end, #k/apex) <-
      (coe, coe) if #k == kan
      (coe, coe) if #k == coe
      (pre, pre) if #k == hcom
      (pre, pre) if #k == pre
  | H, x:#c0 >> (#f0 x) = (#f1 x) in #a0
  | H, x:#c0 >> (#g0 x) = (#g1 x) in #b0
  | H >> #a0 = #a1 in (U #l #k/end)
  | H >> #b0 = #b1 in (U #l #k/end)
  | H >> #c0 = #c1 in (U #l #k/apex)

:index:`pushout/eq/left`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
::

  H >> (left #m0) = (left #m1) in (pushout #a #b #c [x] (#f x) [x] (#g x))
  | H >> #m0 = #m1 in #a
  | H, x:#c >> (#f x) in #a
  | H, x:#c >> (#g x) in #b
  | H >> #b type
  | H >> #c type

:index:`pushout/eq/right`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
::

  H >> (right #m0) = (right #m1) in (pushout #a #b #c [x] (#f x) [x] (#g x))
  | H >> #m0 = #m1 in #b
  | H, x:#c >> (#f x) in #a
  | H, x:#c >> (#g x) in #b
  | H >> #a type
  | H >> #c type

:index:`pushout/eq/glue`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
::

  H >> (glue #r #m0 #fm0 #gm0) = (glue #r #m1 #fm1 #gm1) in (pushout #a #b #c [x] (#f x) [x] (#g x))
  | H >> #m0 = #m1 in #c
  | H >> #fm0 = #fm1 in #a
  | H >> #gm0 = #gm1 in #b
  | H >> (#f #m0) = #fm0 in #a
  | H >> (#g #m0) = #gm0 in #b
  | H, x:#c >> (#f x) in #a
  | H, x:#c >> (#g x) in #b

:index:`pushout/eq/fcom`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`pushout/eq/pushout-rec`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
::

  H >> (pushout-rec [p] (#d0 p) #m0 [a] (#n0 a) [b] (#p0 b) [v x] (#q0 v x)) = (pushout-rec [x] (#d1 x) #m1 [a] (#n1 a) [b] (#p1 b) [v x] (#q1 v x)) in #ty
  where H >> #m0 = #m1 synth ~> (pushout #a #b #c [x] (#f x) [x] (#g x)), psi
  | H, a:#a >> (#n0 a) = (#n1 a) in (#d0 (left a))
  | H, b:#b >> (#p0 b) = (#p1 b) in (#d1 (right b))
  | H, v:dim, x:#c >> (#q0 v x) = (#q1 v x) in (#d0 (glue v x (#f x) (#g x)))
  | H, x:#c >> (#q0 0 x) = (#n0 (#f x)) in (#d0 (left (#f x)))
  | H, x:#c >> (#q0 1 x) = (#p0 (#g x)) in (#d0 (right (#g x)))
  | H, p:(pushout #a #b #c [x] (#f x) [x] (#g x)) >> (#d0 p) = (#d1 p) kan type
  | psi
  | H >> (#d0 #m0) <= #ty type

:index:`pushout/beta/glue`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
::

  H >> (pushout-rec [p] (#d p) (glue #r #t #ft #gt) [a] (#n a) [b] (#p b) [v x] (#q v x)) = #s in #ty
  | H >> (#q #r #t) = #s in #ty
  | H, #r=0 >> (#n #ft) = #s in #ty
  | H, #r=1 >> (#p #gt) = #s in #ty

Coequalizers
------------

:index:`coeq/eqtype`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`coeq/eq/cod`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`coeq/eq/dom`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`coeq/eq/fcom`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`coeq/beta/dom`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`coeq/eq/coeq-rec`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Exact equalities
----------------

:index:`eq/eqtype`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`eq/eq/ax`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`eq/eta`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Composite types
---------------

:index:`fcom/eqtype`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`fcom/eq/box`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`fcom/intro`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

V types
-------

:index:`V/eqtype`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`V/eq/uain`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`V/intro`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`V/eq/proj`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`universe/eqtype`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Kan operations
--------------

:index:`hcom/eq`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`hcom/eq/cap`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`hcom/eq/tube`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`coe/eq`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`coe/eq/cap`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Universes
---------

:index:`subtype/eq`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`universe/subtype`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^


