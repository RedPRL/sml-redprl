![PRL: We Can Prove It](https://pbs.twimg.com/media/Ch1klO6U4AAlj62.jpg)

(image courtesy of [@tranngocma](http://twitter.com/tranngocma))

### What is RedPRL?

*RedPRL* is the People's Refinement Logic, a next-generation homage
to [Nuprl](http://www.nuprl.org); RedPRL was preceeded by
[JonPRL](http://www.github.com/jonsterling/jonprl), written by Jon Sterling,
Danny Gratzer and Vincent Rahli.

The purpose of RedPRL is to provide a practical implementation of Computational
Cubical Type Theory in the Nuprl style, integrating modern advances in proof
refinement.

### Literature and background on RedPRL

RedPRL is (becoming) a proof assistant for Computational Cubical Type Theory,
as described by Angiuli and Harper in [Computational Higher Type Theory II:
Dependent Cubical Realizability](http://arxiv.org/abs/1606.09638).  The
syntactic framework is described in a note by Jon Sterling called [Aspects of
Cubical Type
Theory](https://github.com/jonsterling/aspects-of-cubical-type-theory), and is
inspired by Harper's "abstract binding trees" (Harper, [Practical Foundations
for Programming Languages](http://www.cs.cmu.edu/~rwh/pfpl.html); Sterling &
Morrison, [Syntax and Semantics of Abstract Binding
Trees](https://github.com/jonsterling/syntax-and-semantics-of-abts)).


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

    ./bin/redprl test/test.prl


### Editor Support: Visual Studio Code

The easiest/most user-friendly way to get started is with [Visual Studio
Code](https://code.visualstudio.com); the [RedPRL
mode](https://marketplace.visualstudio.com/items?itemName=freebroccolo.redprl)
can be downloaded from the Marketplace.

### Editor Support: Emacs

We have support for interactive RedPRL development in Emacs.

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


### Contributing

If you'd like to help, the best place to start are issues with the following labels:

* [`E-easy`](https://github.com/RedPRL/sml-redprl/issues?q=is%3Aissue+is%3Aopen+label%3AE-easy)
* [`E-help-wanted`](https://github.com/RedPRL/sml-redprl/issues?q=is%3Aissue+is%3Aopen+label%3AE-help-wanted)

We follow the issue labels used by Rust which are described in detail
[here](https://github.com/rust-lang/rust/blob/master/CONTRIBUTING.md#issue-triage).

If you find something you want to work on, please leave a comment so that others
can coordinate their efforts with you. Also, please don't hesitate to open a new
issue if you have feedback of any kind.

*The above text is stolen from [Yggdrasil](https://github.com/freebroccolo/yggdrasil/blob/master/README.md).*
