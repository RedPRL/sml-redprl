### Engineering Notes

Having learned a bit from JonPRL's development, I'm compiling a bit of a
manifesto on various matters concerning the new codebase.

#### MLton first

We may support SML/NJ if our contributors want to, there we *only* require that
the MLton build work properly. There are a few reasons for favoring MLton:

- MLton implements Standard ML more faithfully; in addition to the (useful)
  extensions that SML/NJ provides to SML, there are a number of cases where its
  implementation is in fact incompatible with the definition. Whereas everything
  that MLton builds should also build in SML/NJ, I believe.

- MLton has powerful whole-program optimization. Originally, JonPRL was
  intended to be a library, and JonPRL proofs were just ML programs; under
  these circumstances, SML/NJ made a lot of sense, because it builds much faster
  than MLton. Today, however, JonPRL is a proof assistant, and so the trade-off
  is different.

- It is totally straightforward to produce an honest-to-god binary with MLton.
  I still have no idea what this "heap image" crap is about in SML/NJ.

Downsides of MLton are:

- Source code cannot contain unicode characters; in practice, this means that
  you have to use the decimal code in string literals.

- Builds take longer. In practice, by splitting parts of JonPRL into smaller
  libraries, we can still get reasonable build-and-code turnaround by only
  building the part of JonPRL that we are working on.

- There's no REPL. In practice, the REPL has not been used almost at all for
  day-to-day JonPRL development, so I do not see this is a very serious
  disadvantage. The only benefit of the REPL is that you can quickly print out some
  datastructure without writing your own pretty-printer for it.

#### No clever stuff

I want the code to be straightforward. I considered using `sml-open-ended`
again for operators, for instance, and in addition to the fact that it may be
non-trivial to make it work at higher kind, it's just another piece of the
codebase that is incredibly mystifying to people who don't understand what it
is.

#### Adhere to a common whitespace & lexical style

The whitespace and lexical style that I prefer is used in JonPRL and the ABT
library. Contributors are *not* required to adhere to this perfectly, but we
will ensure that no code is merged into master which does not match the
surrounding style.



#### This is a living document!

Feel free to submit additions and changes.
