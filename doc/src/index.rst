The RedPRL Proof Assistant
==========================

|RedPRL| is an experimental proof assistant based on cubical computational type
theory, which extends the Nuprl_ semantics by higher-dimensional features
inspired by homotopy type theory. |RedPRL| is created and maintained by the
`RedPRL Development Team`_.

.. _Nuprl: http://www.nuprl.org/
.. _RedPRL Development Team: https://github.com/RedPRL/sml-redprl/blob/master/CONTRIBUTORS.md

|RedPRL| is written in `Standard ML <http://sml-family.org/>`_, and is available
for download on `GitHub <http://github.com/redprl/sml-redprl>`_.

Features
--------

* computational canonicity and extraction
* univalence as a theorem
* strict (exact) equality types
* coequalizer and pushout types
* functional extensionality
* equality reflection
* proof tactics

Papers & Talks
--------------

* Favonia. `Cubical Computational Type Theory & RedPRL`_. 2018.
* Harper, Angiuli. `Computational (Higher) Type Theory`_. ACM POPL Tutorial Session 2018.
* Angiuli, Harper, Wilson. `Computational Higher-Dimensional Type Theory`_. POPL 2017.
* Sterling, Harper. `Algebraic Foundations of Proof Refinement`_. Draft, 2016.

.. _Computational (Higher) Type Theory: https://www.cs.cmu.edu/~rwh/talks/POPL18-Tutorial.pdf
.. _Cubical Computational Type Theory & RedPRL: http://favonia.org/files/chtt-penn2018-slides.pdf
.. _Computational Higher-Dimensional Type Theory: http://www.cs.cmu.edu/~rwh/papers/chitt/popl17.pdf
.. _Algebraic Foundations of Proof Refinement: http://www.redprl.org/pdfs/afpr.pdf

RedPRL User Guide
=================

.. toctree::
   :maxdepth: 2

   tutorial
   language
   atomic-judgment
   multiverse
   refine

Indices
-------
* :ref:`genindex`
* :ref:`search`

Acknowledgments
---------------

This research was sponsored by the Air Force Office of Scientific Research under
grant number FA9550-15-1-0053 and the National Science Foundation under grant
number DMS-1638352. We also thank the Isaac Newton Institute for Mathematical
Sciences for its support and hospitality during the program "Big Proof" when
part of this work was undertaken; the program was supported by the Engineering
and Physical Sciences Research Council under grant number EP/K032208/1. The
views and conclusions contained here are those of the authors and should not be
interpreted as representing the official policies, either expressed or implied,
of any sponsoring institution, government or any other entity.
