Refinement Rules
==================================

.. todo::
  Fill in the refinement rules listed below.

Booleans
--------

:index:`bool/eqtype`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
::

  H >> bool = bool #k type at #l

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
  where bool, psi... <- #m0 = #m1 synth
  | H >> #t0 = #t1 in (#c0 tt)
  | H >> #f0 = #f1 in (#c0 ff)
  | H, x:bool >> #c0 = #c1 type
  | H >> #ty <= (#c0 #m0) type
  | psi...


Natural numbers and integers
----------------------------

:index:`nat/eqtype`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`nat/eq/zero`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`nat/eq/succ`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`nat/eq/nat-rec`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`int/eqtype`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`int/eq/pos`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`int/eq/negsucc`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`int/eq/int-rec`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Void
----

:index:`void/eqtype`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Circle
------

:index:`s1/eqtype`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`s1/eq/base`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`s1/eq/loop`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`s1/eq/fcom`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`s1/eq/s1-rec`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`s1/beta/loop`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Dependent functions
-------------------

:index:`fun/eqtype`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

  H >> (-> [x : #a0] (#b0 x)) = (-> [x : #a1] (#b1 x)) #k type at #l
  where
    (#k/dom, #k/cod) <-
      (discrete, discrete) if #k == discrete
      (coe, kan) if #k == kan
      (pre, hcom) if #k == hcom
      (coe, coe) if #k == coe
      (pre, pre) if #k == pre
  | H >> #a0 = #a1 #k/dom type at #l
  | H, x:#a0 >> (#b0 x) = (#b1 x) #k/cod type at #l

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

.. todo::

  In the current rule, the first subgoal is omitted if ``#e`` and ``#f`` are the same term.
  Another option would be to make the first subgoal unconditional, but then omit the second
  subgoal.


:index:`fun/eq/app`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

  H >> ($ #f0 #e0) = ($ #f1 #e1) in #ty
  where (-> [x : #a] (#b x)), psi... <- #f0 = #f1 synth
  | H >> #e0 = #e1 in #a
  | psi...
  | H >> #ty <= (#cod #e0) type

Records
-------

:index:`record/eqtype`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`record/eq/tuple`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`record/eq/eta`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`record/eq/proj`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:index:`record/intro`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

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


