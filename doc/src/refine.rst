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
  | H, x:S1 >> (#c0 x) = (#c1 x) type
  | H >> (#c0 #m0) <= #ty type

:index:`s1/beta/loop`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
::

  H >> (S1-rec [x] (#c x) (loop #r) #b [u] (#l u)) = #m in #ty
  | H >> (#l #r) = #m in #ty
  | H >> #b[0/#r] = #m[0/#r] in #ty[0/#r]
  | H >> #b[1/#r] = #m[1/#r] in #ty[1/#r]

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

:index:`path/eq/abs`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`path/intro`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`path/eq/eta`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`path/eq/app`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`path/eq/app/const`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`path/eq/from-line`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Lines
-----

:index:`line/eqtype`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`line/eq/abs`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`line/intro`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`line/eq/eta`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`line/eq/app`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Pushouts
--------

:index:`pushout/eqtype`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`pushout/eq/left`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`pushout/eq/right`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`pushout/eq/glue`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`pushout/eq/fcom`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`pushout/eq/pushout-rec`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`pushout/beta/glue`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

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


