Currently there are four kinds of categorical judgements:

- `EQ_TYPE (a, b)`: `a` and `b` are equal types.
- `EQ ((m, n), a)`: `EQ_TYPE (a, a)` and `m` and `n` are related by the PER associated with `a`.
- `TRUE a`: `EQ_TYPE (a, a)` and there exists a term `m` such that `EQ ((m, m), a)`.
- `SYNTH m`: there is a (canonical) choice of `a` such that `EQ_TYPE (a, a)` and `EQ ((m, m), a)`.

A realizer for each judgment is:

- `EQ_TYPE (a, b)`: always `AX` (trivial).
- `EQ ((m, n), a)`: always `AX` (trivial).
- `TRUE a`: a term `m` such that `EQ_TYPE (a, a)` and `EQ ((m, m), a)`.
- `SYNTH m`: a term `a` such that `EQ_TYPE (a, a)` and `EQ ((m, m), a)`.

As an abbreviation, `TYPE a` is defined as `EQ_TYPE (a, a)` and `MEM (m, a)` is defined as `EQ ((m, m), a)`.
