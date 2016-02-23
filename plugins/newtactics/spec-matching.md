# matching (existing solutions)

Phases:
1. verbatim matching: no conversion, ignore implicits, aka "least surprise"
2. keyed matching: verbatim key, full unif on args, aka "ssr matching"

## keyed matching (the crucial one)

See [https://hal.inria.fr/hal-00652286v1/document](preprint) of paper by Enrico
and Georges.

## verbatim matching (optimization, to be decided)

This is typically not even explained to users, documented only in the preprint,
section 3.2.  The idea is that if you see
```
a + 2 * b = a + (b + c)
```
and you rewrite with a lemma normalizing associativity you don't expect the
LHS to be touched.  If you compute `*` then a `+` is exposed and associativity
could operate.  Note that the key `+` is there, but the RHS is a more natural
match.

This "UI optimization" is not coded correctly in ssr.  It does FO unification
(with conversion turned off) but this makes the machinery never work in the
algebraic part of the library, where conversion is needed to type check things.

A difficulty is that matching today works with `constr`.  If you type
```
rewrite [3 + _]foo
```
and `+` is an overloaded symbol, what you get your hands on is
```
(Ring.add rationals_Ring 3 _)
```
while the goal could contain
```
(Ring.add (ring_of_fiel rationals_Field) 3 _)
```
making FO matching fail because 2 invisible terms are syntactically different.
Keyed matching would succeed, so the user never perceives it.  It would perceive
it on arithmetic goals (where `*` unfolds to `+`), but there we don't overload,
hence no implicit arguments.  I.e. math-comp is not really affected by the
buggy implementation, but it still sucks.

In some sense the FO matching has to take into account "what is written by the 
user and what is inferred by typing" making the latter irrelevant.  A sort of
FO unification modulo "implicit arguments" and "coercions" and any other
piece of info inserted by the system.

# matching (extensions)

The main limitation is "no support for binders".  The technical issue
is that if the pattern `(_ + _)` is inferred outside the binder, then
unification forbids instantiating `_` with a term containing the bound
variable.  An option is to "refresh" the pattern when we move under a
binder.  We would then need to find a way to pass to the `setoid_rewrite`
machinery the position (maybe via a "rewrite strategy", to be checked).

Things are different when the pattern is given by the user.  There using an
unbound name that would become bound once the matching goes under the binder
is a bad idea, since the names in the goal are fragile.  The plan for Ssr is
to have the user write the binder in the pattern. Example goal:
```
\sum_(i \in A) 3 + (2 * i)
rewite [_ * j in F j in \sum_(k \in _) F k]mulnC
```
A more compact syntax not inspired by Ssr could be
```
rewrite [i j |- i + 2*j]addnC
```
Meaning: "move under at least 2 binders, then find `?1 + 2 * ?2` where
`?1` and `?2` cannot be identified.  Dunno how this lightweight syntax
can be married with contextual patterns.

Complexity side note: if the goal contains, say, 3 binders:
```
forall a b c, b - (a + 2*c)
```
one has to align the list?/set? `{a b c}` with `{i j}` and (in case of sets)
this is exponential (keyword: equivariant unification, typical of nominal logic).

Going back to the ssr syntax, this extension also enables `set` to name and
grab terms under binders
```
set g := (F i in \sum_(j \in _) F (2 * j)).
```
would produce the goal
```
g := fun k => 3 + k
==============
\sum_(i \in A) g (2 * i)
```
and a more appealing syntax could be
```
set g (2 * i) := (F i in \sum_(k \in _) F k).
```
that reads: "g is a function that when applied to (2 * i) gives the body
of the big sum on i".

In general a pattern `e(i) in F i in ctx(F t)` would generalize today's
contextual pattern `e in X in ctx(X)` by putting `X` is now under a binder
we name explicitly `i` as in `F i`.  The name `i` can be used in `e(i)` and
we can pass a value `t` for `i` in `ctx(F t)`.
