# TODO

Sections and Pages relative to <https://fare.tunes.org/files/tmp/phd/thesis.pdf>
taken at thesis-draft-119-ga030e4e committed on 2023-07-18T21:44:24+02:00.

## Most Urgent

### 3.3.1 p.59 Composition.
Define a category in which the objects are
"observed semantics", i.e.
operational semantics (category where objects are called "states", morphisms "transitions"),
with an identified subset of observable states (inducing a full subcategory),
and morphisms are co-implementations (from concrete to abstract).
Empty implementations (empty set of observable states) are initial objects.
One possible representation for implementations is as pro-functors with a restriction
such that the concrete functor defines a full subcategory.

### 3.2.2 p.49 Completeness
Define a category in which the objects as observed semantics
equipped with a "simple" subset of their transitions.
Morphisms are complete implementations, i.e. where given a simple abstract transition,
you can "force" the concrete system to follow a simple transition that is its preimage.
Prove "(co)monotonicity" of these morphisms with respect to inclusion
of the set of simple transitions.

### 3.2.5 p.56 Observability
Equip observed semantics with a "simple" subset of transitions,
a "valid" subset of states,
a "safe" subset of valid states,
and an "observe" function from valid state to simple transitions from
the valid state to a safe state.
Morphisms are co-implementations where each concrete observed state maps to an abstract valid state.

### 3.2.3 p.51 Advancing
Equip observed semantics with a subset of strictly _advancing_ transitions
that doesn't include null transitions (categorical identities).

### 3.2.3 p.52 Liveness
Category of live implementations between observed semantics with advancing subsets.

## POSTPONE these developments until later

### 3.2.2 p.50 Totality
Observed semantics where the implementation is a total pro-functor,
its co-implementation is surjective over abstract states.

### 3.2.2 p.50 Fullness
Observed semantics where the co-implementation
is surjective over abstract transitions between reachable abstract states.

### 3.2.2 p.50 Strong Completeness
### 3.2.2 p.51 Weak Completeness
### 3.2.3 p.52 Bounded Liveness
### 3.2.3 p.53 Strong Liveness
### 3.2.3 p.53 Bounded Strong Liveness
### 3.2.3 p.54 Bounded Strong Step Preservation
### 3.2.4 p.54 Co-Liveness
### 3.2.4 p.55 Relevance
### 3.2.4 p.55 Advance Preservation
### 3.2.5 p.58 Bounded Observability
### 3.2.5 p.58 Strong Observability
