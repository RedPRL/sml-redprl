Language Reference
==================

|RedPRL| documents contain expressions written in multiple languages: the
:ref:`top-level vernacular <top-level-vernacular>`, the :ref:`object language
<object-language>`, and the :ref:`tactic language <tactic-language>`.


.. _top-level-vernacular:

Top-level vernacular
--------------------

The top-level vernacular is a very simple language of commands that interact
with the *signature*: this language is for declaring :ref:`new theorems
<def-theorem>`, :ref:`definitional extensions <def-operator>` and :ref:`tactics
<def-tactic>`; the top-level vernacular can also be used to print out an object
from the signature. This is the language that one writes in a ``.prl`` file.

.. _def-theorem:

Defining theorems
^^^^^^^^^^^^^^^^^

A *theorem* in |RedPRL| is given by a type (an object language expression)
together with a tactic script which establishes that the given type is
inhabited; when a theorem is declared, the tactic script is executed against
the goal, and if the result is successful, the generated evidence is added to
the signature.

::

  Thm OpName(#p : ...) : [
    // goal here (object language expression)
  ] by [
    // script here (tactic expression)
  ].


Most definitions in a RedPRL signature will take the form of theorems; but
other forms of definition may be preferable, :ref:`depending on circumstances
<thm-vs-def>`.

.. _def-operator:

Defining new operators
^^^^^^^^^^^^^^^^^^^^^^

The most primitive way to define a new operator in |RedPRL| is to use the ``Def``
command. A definition is specified by giving an operator name (which must be
capitalized), together with a (possibly empty) sequence of parameters together
with their valences, and an object-language term which shall be the definiens:

::

  Def OpName(#p : [dim].exp, ...) : exp = [
    // object language expression here
  ].

A parameter is referenced using a *metavariable* (which is
distinguished syntactically using the ``#`` sigil); the valence of a parameter
specifies binding structure, with ``[tau1,tau2].tau`` being the valence of a
binder of sort ``tau`` that binds a variable of sort ``tau1`` and a variable of
sort ``tau2``.

A simple definition of sort ``exp`` without parameters can be abbreviated as follows:

::

  Def OpName = [
    // object language expression here
  ].

Definitions of this kind are not subject to any typing conditions in CHTT;
instead, if you use a primitive definition within a proof, you will have to
prove that it is well-typed.


.. _def-tactic:

Defining tactics
^^^^^^^^^^^^^^^^

A tactic can be defined using the special ``Tac`` command:

::

  Tac OpName(#p : ...) = [
    // tactic expression here
  ].


This desugars to an instance of the ``Def`` command, and differs only in that the
body of the definiens is here parsed using the grammar of tactic expressions.


Printing objects
^^^^^^^^^^^^^^^^

To print a previously-defined object from the signature, one can write the
following command:

::

  Print OpName.


.. _thm-vs-def:

When to use theorems or definitions?
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

As a rule of thumb, in most cases it is simpler to interactively construct an
element of a type using a ``Thm`` declaration than it is to define a code for
an element, and then prove that it has the intended type. This is why theorems
are usually preferred to definitions in RedPRL.

However, definitions may be preferable in some cases; consider the definition
of an abbreviation for the type family ``(lam [ty] (-> nat ty))`` of sequences.
As a theorem, this definition must take a universe level as a parameter

::

  Thm Sequence(#l : lvl) : [
    (-> [ty : (U #l)] (U #l))
  ] by [
    // apply function introduction rule in the tactic language
    lam ty =>
      // explicitly give the body of the function in the object language
      `(-> nat ty)
  ].

Later, when using this definition, one would have to explicitly provide the
universe level, even though it does not play a part in the actual defined
object: for instance, ``(Sequence #lvl{0})``. The parameter was present only in
order to express the type of the type family. On the other hand, with a
definition, we can write the following:


::

  Def Sequence = [
    (lam [ty] (-> nat ty))
  ].


One advantage of theorems over definitions is that RedPRL knows their type
intriniscally; whereas definitions must be unfolded and proved to be well-typed
at each use-site.

.. _object-language:

Object language
---------------

|RedPRL|'s object language and tactic language share a common syntactic framework
based on multi-sorted second-order abstract syntax, which provides a uniform
treatment of binding with syntactic sorts. |RedPRL| has three main sorts: ``exp``
(the sort of expressions), ``dim`` (the sort of dimension expressions) and ``tac``
(the sort of tactic expressions).

The object language is written in a variant of s-expression notation, with
binding operators written systematically in the style of ``(lam [x] x)``. An
expression in the object language is an *untyped program* or *realizer* in the
language of Computational Higher Type Theory (CHTT).

These expressions include ordinary programming constructs like lambda
abstraction and application, records, projection, etc., as well as exotic
programming constructs inspired by cubical sets:

- dimension expressions ``i``, ``0``, ``1``
- dimension abstraction ``(abs [i] m)``
- dimension application ``(@ m r)``
- coercion: ``(coe r~>s [i] ty n)``, where ``[i] ty`` is a line of types
- homogeneous composition: ``(hcom r~>s ty cap [i=0 [j] tube0] ...)``
- heterogeneous composition: ``(com r~>s [j] ty cap [i=0 [k] tube0] ..)``
- many other constructs, such as lines of types induced by equivalences (univalence)

Below are summarized many common forms of object language expression.

+-----------------------------+--------------------------------+
| Operation                   | Expression                     |
+=============================+================================+
| dependent function type     | ``(-> [x y... : A]... C)``     |
+-----------------------------+--------------------------------+
| lambda abstraction          | ``(lam [x y...] e)``           |
+-----------------------------+--------------------------------+
| function application        | ``($ f e1 e2...)``             |
+-----------------------------+--------------------------------+
| path type                   | ``(path [i] A e0 e1)``         |
+-----------------------------+--------------------------------+
| line type                   | ``(-> [i : dim]... C)``        |
+-----------------------------+--------------------------------+
| path/line abstraction       | ``(abs [i j...] e)``           |
+-----------------------------+--------------------------------+
| path/line application       | ``(@ e r1 r2...)``             |
+-----------------------------+--------------------------------+
| dependent record type       | ``(record [lbl... : A]... C)`` |
+-----------------------------+--------------------------------+
| tuple (record element)      | ``(tuple [lbl e]...)``         |
+-----------------------------+--------------------------------+
| record projection           | ``(!lbl e)``                   |
+-----------------------------+--------------------------------+
| ...                         |                                |
+-----------------------------+--------------------------------+


.. todo::
  Finish summary of object language terms.



.. _tactic-language:

Tactic language
---------------



.. todo::
  Summarize tactic language
