# To Do

## Definitions

* Characterize what it means for an iteration space to be
  deterministic. Note that a deterministic iteration space
  is isomorphic to a (finite or infinite) stream.

* Characterize what it means for an iteration space to be
  finite. Note that a finite iteration space is isomorphic
  to a set of lists (which represent the complete sequences).
  [Actually, I don't think that we can characterize finiteness;
  it is not a safety property. We can characterize boundedness,
  i.e., the iteration space of all sequences of length at most `k`.]

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
  to a (finite or infinite) stream.
  Note that a deterministic automaton is just a chain.
  Note that these automata are not the same as the automata that are
  usually taught, because they are not necessarily finite-state, and
  because they describe *producers*, not *recognizers*.
  In particular, a non-deterministic automaton cannot be
  converted to an equivalent deterministic automaton.

* Define non-deterministic automata with ε transitions. Define conversions
  (both ways) between them and ordinary non-deterministic automata.

## Combinators

Many combinators can be expressed both on iteration spaces
and on automata, and a correspondence can be established.

On the automaton side, some combinators may be easier to express
if ε transitions are allowed (Thompson's construction).

* the empty sequence.
* a singleton sequence.
* the union of two (or more) iteration spaces. 
* the intersection of two (or more) iteration spaces.
* the concatenation of two iteration spaces.
* the repetition (Kleene star) of an iteration space.
* the Cartesian product of two iteration spaces.

* the integers from `i` up to `j`.
* the integers from `j` down to `i`.
* the elements of the list `xs`, in order.
* the elements of the infinite stream `xs`, in order.
* the elements of the set `xs`, in an arbitrary order.
* the elements of the multiset `xs`, in an arbitrary order.
* any bounded sequence of elements.
* any increasing sequence of elements.

* toplogical iteration on a directed graph
    (obtained as a combination of some of the previous concepts).
* breadth-first iteration on a directed graph.
* depth-first iteration on a directed graph
    (parameterized with an iteration space on the successors of each vertex!)
    (possibly with preorder/postorder variants).

* the sequences of elements that satisfy some property P (`filter`).
* the image of an iteration space through a function (`map`).
* the image of an iteration space through a relation.
* the orbit of a function of type `A → A`.
* the orbit of a function of type `A → option A`.
* the orbit of a function of type `S → option (A * S)` (`unfold`).
    (the previous two are special cases)
    (this is related to deterministic automata)

Check the Haskell list library to see what we are missing.

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
