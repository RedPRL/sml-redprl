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

### Editor Support

RedPRL is presently supported in Atom and Emacs.

#### Atom

The Atom plugin is available at [atom.io](https://atom.io/packages/language-redprl).

### Emacs

[![MELPA](https://melpa.org/packages/redprl-badge.svg)](https://melpa.org/#/redprl)

The Emacs mode is a part of this repository. Additionally, it is available in
[MELPA](https://melpa.org/#/redprl).

The easiest way to install the package is from MELPA, using their [getting
started](https://melpa.org/#/getting-started) instructions. The package is named
`redprl`. It will probably be necessary to set the customization variable
`redprl-command` to the path to the `redprl` binary.

When `redprl-mode` is installed, files ending in `.prl` will automatically open
in the mode. If they do not, run `M-x redprl-mode`. The mode supports the
following features:


 * Press `C-c C-l` to send the current development to RedPRL.

 * Imenu (or wrappers such as `helm-imenu`) can be used to jump to definitions
   in the buffer.

 * Completion is supported for names of declarations in the current buffer.

 * Flycheck is also supported, and can be used in lieu of `C-c C-l` if you like.
   Be sure that either the `redprl` executable is in your path, or set
   `flycheck-redprl-executable` in your own Emacs configuration.

