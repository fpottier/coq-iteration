# To Do

## Definitely

* Non-deterministic automata should have multiple initial states,
  so they are closed under derivative.

* Characterize what it means for an iteration space to be
  deterministic.

* Offer all of the combinators of regular expressions (empty,
  singleton, union, sequence, star) both on iteration spaces
  and on automata, and establish a correspondence.
  Investigate more combinators:
  intersection, Cartesian product.
  On the automaton side, some combinators are easier to express
  if ε transitions are allowed (Thompson's construction).

* Define derivatives, both on iteration spaces and on automata,
  and prove a correspondence.

* An alternative way of converting an iteration space to a (deterministic)
  automaton is to use `derivative`. The states of the automaton are iteration
  spaces, and the transitions are given by `derivative`. A state is final if
  `complete []` holds.

## Maybe

* Define deterministic automata, with a single initial state, with a
  transition function instead of a transition relation, and where
  a final state does not have successors. Define conversions (both
  ways) between deterministic and non-deterministic automata.

* Define non-deterministic with ε transitions. Define conversions
  (both ways) between them and ordinary non-deterministic automata.

## Maybe Not

* Offer an alternative definition of an iteration space as a set of finite
  sequences of iteration events (`Yield` or `Done`), where a `Done` event can
  never be followed by any event.

* Offer a variant of iteration spaces
  that allows observable `Skip` steps in the style of the
  [stream fusion](https://dl.acm.org/doi/10.1145/1291220.1291199) paper.
  There should exist some correspondence with automata with ε transitions.
