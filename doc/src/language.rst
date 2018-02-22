Language Reference
==================

|RedPRL| documents contain expressions written in multiple languages: the
top-level vernacular, the object language, and the tactic language.

Object language
---------------

|RedPRL|'s object language and tactic language share a common syntactic framework
based on multi-sorted second-order abstract syntax, which provides a uniform
treatment of binding with syntactic sorts. |RedPRL| has three main sorts: ``exp``
(the sort of expressions), ``dim`` (the sort of dimension expressions) and ``tac``
(the sort of tactic expressions).

The object language is written in a variant of s-expression notation, where
binding operators written systematically in the style of ``(lam [x] x)``. An
expression in the object language is an *untyped program* or *realizer* in the
language of Computational Higher Type Theory (CHTT).

These expressions include ordinary programming constructs like lambda
abstraction and application, records, projectsion, etc., as well as exotic
programming constructs inspired by cubical sets:

- dimension expressions ``i``, ``0``, ``1``
- dimension abstraction ``(abs [i] m)``
- coercion: ``(coe r~>s [i] ty n)``, where ``[i] ty`` is a line of types
- homogeneous composition: ``(hcom r~>s ty cap [i=0 [j] tube0] ...)``
- heterogeneous composition: ``(com r~>s [j] ty cap [i=0 [j] tube0] ..)``
- many other constructs, such as lines of types induced by equivalences (univalence)

.. todo::
  Give systematic summary of object language terms.


Tactic language
---------------

.. todo::
  Summarize tactic language

Top-level vernacular
--------------------

The top-level vernacular is a very simple language of commands that interact
with the *signature*: this language is for declaring definitional extensions,
new theorems and tactics; the top-level vernacular can also be used to print
out an object from the signature. This is the language that one writes in a
``.prl`` file.

Defining new operators
^^^^^^^^^^^^^^^^^^^^^^

The most basic way to define a new operator in |RedPRL| is to use the ``Def``
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


Defining tactics
^^^^^^^^^^^^^^^^

A tactic can be defined using the special ``Tac`` command:

::

  Tac OpName(#p : ...) = [
    // tactic expression here
  ].


This desugars to an instance of the ``Def`` command, and differs only in that the
body of the definiens is here parsed using the grammar of tactic expressions.


Defining theorems
^^^^^^^^^^^^^^^^^

A *theorem* in |RedPRL| is a definition that comes with a goal and a tactic
script; when a theorem is declared, the tactic script is executed against the
goal, and if the result is successful, the generated evidence is added to the
signature.

::

  Thm OpName(#p : ...) : [
    // goal here (object language expression)
  ] by [
    // script here (tactic expression)
  ].


Printing objects
^^^^^^^^^^^^^^^^

To print a previously-defined object from the signature, one can write the
following command:

::

  Print OpName.


