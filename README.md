![PRL: We Can Prove It](https://pbs.twimg.com/media/Ch1klO6U4AAlj62.jpg)

(image courtesy of [@tranngocma](http://twitter.com/tranngocma))

### What is RedPRL?

*RedPRL* is the People's Refinement Logic, a next-generation homage
to [Nuprl](http://www.nuprl.org); RedPRL was preceeded by
[JonPRL](http://www.github.com/jonsterling/jonprl), written by Jon Sterling,
Danny Gratzer and Vincent Rahli.

The purpose of RedPRL is to consolidate several advances in refinement logics,
including:

- a multi-sorted version of abstract binding trees
- support for nominal abstraction and unguessable atoms
- a dependent version of the LCF apparatus to support refinement rules
  whose premises depend on each other's evidence

### Literature and background on RedPRL

RedPRL is a proof assistant for Nominal Multi-Sorted Computational Type Theory,
whose semantics are defined in Sterling & Morrison's
[Type Refinements for the Working Class](https://github.com/jonsterling/type-refinements-for-the-working-class). The syntactic framework is described in
[Syntax and Semantics of Abstract Binding Trees](https://github.com/jonsterling/syntax-and-semantics-of-abts),
also by Sterling & Morrison.


### What is this repository?

This is the repository for the nascent development of RedPRL. RedPRL is an
experiment which is constantly changing; we do not yet have strong
documentation, but we have an IRC channel on Freenode (#redprl) where we
encourage anyone to ask any question, no matter how silly it may seem.

### How do I build it?

First, fetch all submodules. If you are cloning for the first time, use

    git clone --recursive git@github.com:RedPRL/sml-redprl.git

If you have already cloned, then be sure to make sure all submodules are up to date,
as follows:

    git submodule update --init --recursive

Next, make sure that you have the [MLton compiler](http://mlton.org/) for Standard
ML installed. Then, simply run

    ./script/mlton.sh

Then, a binary will be placed in `./bin/redprl`, which you may run as
follows

    ./bin/redprl my-development.prl
