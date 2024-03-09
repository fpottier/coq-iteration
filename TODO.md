# To Do

## Definitions

* Characterize what it means for an iteration space to be
  deterministic. Note that a deterministic iteration space
  is isomorphic to a finite or infinite stream.

* Characterize what it means for an iteration space to be
  finite. Note that a finite iteration space is isomorphic
  to a set of lists (which represent the complete sequences).

* Note that a deterministic and finite iteration space is
  isomorphic to a single list.

* Define derivatives, both on iteration spaces and on automata,
  and prove a correspondence.

* An alternative way of converting an iteration space to an automaton is to
  use `derivative`. The states of the automaton are iteration spaces, and the
  transitions are given by `derivative`. A state is final if `complete []`
  holds.

* Define deterministic automata, with a single initial state, with a
  transition function of type `state → option (A * state)`.
  Define a conversion of a deterministic automaton into
  a non-deterministic one.
  Note that a deterministic automaton is isomorphic
  to a finite or infinite stream.

* Define non-deterministic automata with ε transitions. Define conversions
  (both ways) between them and ordinary non-deterministic automata.

## Combinators

* Offer all of the combinators of regular expressions (empty,
  singleton, union, sequence, star) both on iteration spaces
  and on automata, and establish a correspondence.
  Investigate more combinators:
  intersection, Cartesian product.
  On the automaton side, some combinators are easier to express
  if ε transitions are allowed (Thompson's construction).

## Technicalities

* Set up rewriting modulo the preorders on spaces / automata.

## Maybe Not

* Offer an alternative definition of an iteration space as a set of finite
  sequences of iteration events (`Yield` or `Done`), where a `Done` event can
  never be followed by any event.

* Offer a variant of iteration spaces
  that allows observable `Skip` steps in the style of the
  [stream fusion](https://dl.acm.org/doi/10.1145/1291220.1291199) paper.
  There should exist some correspondence with automata with ε transitions.
