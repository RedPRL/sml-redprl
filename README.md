### What is Red JonPRL?

*Red JonPRL* is the People's Refinement Logic, a next-generation homage
to [Nuprl](http://www.nuprl.org); Red JonPRL was preceeded by
[JonPRL](http://www.github.com/jonsterling/jonprl), written by Jon Sterling,
Danny Gratzer and Vincent Rahli.

The purpose of Red JonPRL is to consolidate several advances in refinement logics,
including:

- a multi-sorted version of abstract binding trees (immediate)
- support for nominal abstraction and unguessable atoms (immediate)
- a dependent version of the LCF apparatus to support refinement rules
  for existential judgments (long-term)

Red JonPRL is a proof assistant for Nominal Multi-Sorted Computational Type Theory,
whose semantics are defined in Sterling & Morrison's
[Type Refinements for the Working Class](https://github.com/jonsterling/type-refinements-for-the-working-class). The syntactic framework is described in
[Syntax and Semantics of Abstract Binding Trees](https://github.com/jonsterling/syntax-and-semantics-of-abts),
also by Sterling & Morrison.

### What is this repository?

This is the repository for the nascent development of Red JonPRL. Currently, there are
only bits and pieces, but eventually, enough kit will be here that we can start migrating
the JonPRL sources to the new order.

### How do I build it?

First, fetch all submodules. If you are cloning for the first time, use

    git clone --recursive git@github.com:JonPRL/sml-red-jonprl.git

If you have already cloned, then be sure to make sure all submodules are up to date,
as follows:

    git submodule update --init --recursive

Next, make sure that you have the [MLton compiler](http://mlton.org/) for Standard
ML installed. Then, simply run

    ./script/mlton.sh

Then, a binary will be placed in `./bin/jonprl`, which you may run as
follows

    ./bin/jonprl my-development.jonprl
