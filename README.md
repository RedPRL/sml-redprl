![PRL: We Can Prove It](https://pbs.twimg.com/media/Ch1klO6U4AAlj62.jpg)

(image courtesy of [@tranngocma](http://twitter.com/tranngocma))

### What is RedPRL?

*RedPRL* is the People's Refinement Logic, a next-generation homage
to [Nuprl](http://www.nuprl.org); RedPRL was preceeded by
[JonPRL](http://www.github.com/jonsterling/jonprl), written by Jon Sterling,
Daniel Gratzer and Vincent Rahli.

The purpose of RedPRL is to provide a practical implementation of Computational
Cubical Type Theory in the Nuprl style, integrating modern advances in proof
refinement.

### Literature and background on RedPRL

RedPRL is (becoming) a proof assistant for Computational Cubical Type Theory, as
described by Angiuli, Favonia, and Harper in [Computational Higher Type Theory
III: Univalent Universes and Exact Equality](https://arxiv.org/abs/1712.01800).
The syntactic framework is inspired by second-order abstract syntax (relevant
names include Aczel, Martin-Löf, Fiore, Plotkin, Turi, Harper, and many others).

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

    ./bin/redprl example/README.prl

### Editor Support: Vim

Our best-supported editor is currently Vim.
See the RedPRL plugin under [vim/](vim/).

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

Please see `CONTRIBUTING.md` for copyright assignment.

### Acknowledgments

This research was sponsored by the Air Force Office of Scientific Research under
grant number FA9550-15-1-0053 and the National Science Foundation under grant
number DMS-1638352. We also thank the Isaac Newton Institute for Mathematical
Sciences for its support and hospitality during the program "Big Proof" when
part of this work was undertaken; the program was supported by the Engineering
and Physical Sciences Research Council under grant number EP/K032208/1. The
views and conclusions contained here are those of the authors and should not be
interpreted as representing the official policies, either expressed or implied,
of any sponsoring institution, government or any other entity.
