Atomic Judgments
================

|RedPRL| currently has five forms of atomic (non-hypothetical) judgments that may appear in subgoals.

1. :ref:`Truth <jdg-true>` asserts that a type is inhabited.
2. :ref:`Type equality <jdg-eqtype>` asserts an equality between two types.
3. :ref:`Subtyping <jdg-subtype>` asserts a subtyping relation.
4. :ref:`Subkinding <jdg-subkind>` asserts that some type is actually a universe in which
   all types has a particular kind.
5. :ref:`Term <jdg-term>` lets the user give an expression.

Note that these judgment forms differ from our semantic presentations in papers.

.. _jdg-true:

Truth
-----

A *truth* judgment

::

    a true

or simply

::

    a

means ``a`` is an inhabited type.
Any inhabitant can realize this judgment.
This is commonly used
to state a theorem or specify the type of the program to be implemented.
In fact, all top-level theorems (see :ref:`def-theorem`) must be in this judgmental form.

.. _jdg-eqtype:

Type Equality
-------------

A *type equality* judgment

::

    a = b type

means ``a`` are ``b`` are equal types (without regard to universe level),
and its realizer must be ``ax``, the same as the realizer of equality types.
Multiverses are supported through kind markers such as ``kan`` or ``discrete``. For example::

    a = b discrete type
    a = b kan type
    a = b coe type
    a = b hcom type
    a = b pre type

where ``a = b kan type`` means ``a`` and ``b`` are equal Kan types.
(The judgment ``a = b type`` is really an abbreviation of ``a = b pre type``
because ``pre`` is the default kind.)
To save some typing, ``a type`` stands for ``a = a type``
and ``a kan type`` stands for ``a = a kan type``.

In the presence of universes and equality types,
one might wonder why we still have a dedicated judgmental form for type equality.
It turns out to be very convenient to state type equality without specifying the universe levels;
with this, we can survive without a universe level synthesizer as the one in Nuprl,
which was created to alleviate the burden of guessing universe levels.
One may intuitively treat the judgment

::

    a = b type

as ``(= (U omega) a b) true`` except that we cannot talk about ``(U omega)`` internally.

.. _jdg-subtype:

Subtyping
---------

A *subtype* judgment

::

    a <= b type

states that ``a`` is a subtype of ``b``. More precisely, the partial equivalence relation
associated with ``a`` is a subrelation of the one associated with ``b``.
The realizer must be ``ax``.
There is no support of kind markers because the subtyping relation
never takes additional structures into consideration.

This is currently used whenever we only need a subtyping relationship
rather than type equality. For example, if a function ``f`` is in type ``(-> a b)``,
the rule to determine whether the function application ``($ f x)`` is in type ``b'``
will only demand ``b <= b' type`` rather than ``b = b' type``.
That said, the only non-trivial subtyping relation one can prove in |RedPRL| now
is the one induced by cumulativity of universes.

.. _jdg-subkind:

Subkinding
----------

*Subkind* judgments

::

    a <= discrete universe
    a <= kan universe
    a <= coe universe
    a <= hcom universe
    a <= pre universe

assert that ``a`` is a subuniverse of the universe of the specified kind at the omega level.
Intuitively, ``a <= k universe`` would mean ``a <= (U omega k) type``
if we could internalize universes at the omega level.
The realizer must be ``ax``.
These judgments are similar to the subtyping judgments
except that the right hand side is some omega-level universe.

.. _jdg-term:

Term
----

A *term* judgment is displayed in the sort of the expression
it is asking for, for example

::

    dim
    exp

The realizer is the received term from the user.
This is used to obtain motives or dimension expressions.
For example, the ``rewrite`` tactic requires users to specify
the parts to be rewritten by fulfilling *term* subgoals.
