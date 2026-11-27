# When observability composes

An observable implementation can always bring an interrupted computation to one of its own safe points. At that point the machine may still be halfway through an operation of the language above it. To finish the upper operation, the lower implementation must realize the particular continuation chosen by the upper implementation, starting at the concrete state where it just stopped.

This note states the argument for categories of paths and partial interpretations. It develops the argument in François-René Rideau, [The Semantics of Reflective Systems](https://fare.tunes.org/tmp/phd/thesis.pdf), §§3.2.2 and 3.2.5. The formal statements are `Composition.observable-compose` and `Composition.complete-compose` in [Towers/Implementation.agda](Towers/Implementation.agda).

## Model

Write an implementation as a span $C \leftarrow O \xrightarrow{F} A$. In `Impl.Implementation`, the left leg includes the **full** subcategory on pairs of a concrete state and evidence for `isObservable`. Thus every concrete arrow between two chosen observable endpoints is available to the functor. The functor $F$ interprets those arrows in the abstract system. Distinct paths with the same endpoints may denote different arrows. The composite with $A\leftarrow U\xrightarrow{G}P$ has observable category $O\times_A U$. Its arrows are precisely those observable lower arrows whose interpretations are observable upper arrows.

Each implementation has its own `isSimpleA-hom` and `isSimpleC-hom`. Write $S_C$ for lower concrete simplicity and $S_P$ for upper abstract simplicity. At the shared middle level, distinguish $S_M^U$ (upper concrete) and $S_M^L$ (lower abstract). The sufficient hypotheses for the conjunction are

1. $S_M^U(u) \to S_M^L(u)$ for each middle arrow $u$ (`MiddleCompatible`).
2. Two composable $S_C$ arrows have $S_C$ composite (`BottomClosed`).

Using the same wide subcategory at each interface is one way to satisfy the hypotheses. The proofs below require neither identity closure nor proof irrelevance. The implementation records use witness types and their operations return actual witnesses.

* **Observability (safe-point recovery).** From an observable state $o$, take any concrete prefix $f:o\to x$. There exist a safe suffix $s:x\to y$ and an observable arrow $h:o\to y$ whose underlying concrete arrow is $s\circ f$. This last equation makes the whole recovered execution interpretable, even when the interruption itself has no interpretation. In a full observable subcategory the observable endpoint suffices.
* **Completeness on safe arrows (safe path lifting).** For each observable $o$ and each $u:F(o)\to a$ satisfying $S_M^L$, there exists an observable arrow $k:o\to y$ whose underlying arrow is in $S_C$ and whose interpretation is exactly $u$. This quantifies over every starting representation. The endpoint and the choice of lift may depend on that representation.

## Composition theorem

If both layers have safe-point recovery and safe path lifting with compatible middle parameters and composition-closed bottom simplicity, their composite has both properties.

**Recovery.** Start at a composite-observable state $o$ and interrupt after an arbitrary concrete prefix $f:o\to x$.

1. Lower recovery yields $s:x\to y$ in $S_C$ and $h=s\circ f$ in $O$. Thus $F(h):F(o)\to F(y)$ is a middle prefix starting at an upper-observable state.
2. Upper recovery on that prefix yields $u:F(y)\to z$ satisfying $S_M^U$, hence $S_M^L$, such that $u\circ F(h)$ belongs to $U$.
3. Lower lifting at **$y$** yields $k:y\to w$ observable and concrete-safe with $F(k)=u$. The recovery suffix $k\circ s$ is safe. The entire recovered path $k\circ h$ is lower-observable and its image is $u\circ F(h)$ by functoriality. Thus the entire path is composite-observable.

**Lifting.** Given a safe top arrow starting at $G(F(o))$, lift through $G$ from $F(o)$ to obtain an upper-observable, middle-safe arrow $u$. Lift $u$ through $F$ from $o$. The second lift is concrete-safe, belongs to the pullback together with $u$, and has the prescribed top interpretation. No uniqueness is required.

Only lower lifting is used for composite recovery. Upper lifting enters when proving composite lifting, which lets the argument iterate up a finite tower.

The endpoint of a lift in `IsComplete.proof` agrees with the prescribed endpoint by a path $p$, and the interpreted arrow agrees by a dependent path over $p$. For recovery, transport the upper endpoint’s observation witness backwards along $p$. For completeness, transport the upper lift’s endpoint witness and its arrow equation together along the equality of (endpoint, arrow) pairs. This works even if a state has several observation witnesses.

## If “safe” means bounded

For separate parameters it suffices that upper recovery outputs middle suffixes accepted by lower lifting, and that concatenating the two bottom suffixes fits the composite recovery parameter. Likewise upper lifts must land in the domain of lower lifting. This formulation also works for fixed length budgets, which generally fail closure under concatenation.

The current `_I∘_` always retains the bottom simplicity predicate. The following numerical variant requires a separately parameterized output predicate if the budget increases. For example, take additive path length and monotone bounds. Let lower and upper recovery cost at most $r_L$ and $r_U$ steps in their respective concrete machines. Suppose lifting a safe middle path of length at most $n$ costs at most $L(n)$ bottom steps, and lifting a safe top path of length at most $n$ costs at most $U(n)$ middle steps. Provided the domains include the bounds used, composite recovery costs at most $r_L+L(r_U)$ and composite lifting costs at most $L(U(n))$. The interrupted prefix is already executed and contributes nothing to the recovery budget.

## A finite counterexample

Take the following directed graphs, their free path categories, and all paths as safe.

| Level | Generating edges | Interpretation |
|---|---|---|
| Top | A single state $p$ | |
| Middle | $a_0\to a_1\to a_2$ | The full subcategory on $a_0,a_2$ maps to $p$ and its identity |
| Bottom | $c_0\to c_1$ | Every state and path is observable. The edge maps to $a_0\to a_1$ |

Lower recovery always chooses the identity suffix. In the middle, the only interruption needing a nonidentity suffix is at $a_1$, where $a_1\to a_2$ suffices. In the composite only $c_0$ is observable. After $c_0\to c_1$ the only available suffix is the identity at $c_1$, so recovery fails even with an unlimited budget. The exact missing lift is that of $a_1\to a_2$ from $c_1$.

Even surjectivity on middle states would not fix this example. Add an isolated bottom state $c_2$ representing $a_2$. The correct target now has a representative, but no path from $c_1$ reaches it.

[Towers/Counterexample.agda](Towers/Counterexample.agda) checks an even smaller variant on two states. The bottom preorder permits $0\to1$ and the middle preorder also permits $1\to0$. Every bottom state is lower-observable; only $0$ is upper-observable. Both simplicity predicates accept every arrow. After $0\to1$, composite recovery requires a bottom return to $0$. The Agda proof `composite-fails` eliminates both possible endpoints of the alleged recovery.

## Naming

Keep *observability* as the project-level concept. Use *safe-point recovery* and *safe path lifting* as the two obligations in a theorem or API. The first name records what an interruption handler must produce. The second makes the fixed source and prescribed abstract path explicit. For the unrestricted version, *path lifting* suffices. A bare “complete” leaves open whether the claim concerns states, endpoints, paths or whole runs.

## Review of the existing model

* The three holes at the end of the original module concern the proposed wild category. There is a mathematical obstruction to its two unit laws. The composite takes abstract simplicity from its upper factor and concrete simplicity from its lower factor. The identity supplies `Unit*` for both. Placing it above an implementation overwrites abstract simplicity; placing it below overwrites concrete simplicity. On the terminal category choose the overwritten predicate constantly empty. Equality of the implementations would induce an equality between the empty and unit types. One repair is to equip the objects with simplicity policies and require each morphism to use its endpoint policies. An alternative is to keep policies external to the category of bare implementations. The composition lemmas here work with the existing morphism-local parameters.
* `IsLive.proof` returns a prefix and suffix with the correct intermediate endpoint, but never asks for their composite to equal the supplied execution. In a category with parallel paths these witnesses may describe a different execution. If liveness is meant to factor the given execution, require the equation as a field of the witness.
* `isObservable`, both simplicity predicates, and `Advancement.isAdvancing` take values in `Type`. Describing them as subsets would ordinarily require proposition-valued membership. The present types allow richer evidence, and the interpretation can depend on that evidence. The composition proofs preserve it.


## Checking the proofs

With Agda 2.8.0, register the `.agda-lib` files for `agda/cubical` at `5c1bccf5d4868f854a78fdc11f68593c17f41aad` and `um-catlab/cubical-categorical-logic` at `3a1f2fea115ac6a6c1ec7640681ddf2ddfccad96`. From the root run

```sh
agda Towers/Counterexample.agda
```

This checks both composition lemmas and the counterexample without allowing unsolved metas. The unfinished wild-category declaration lives in `Towers/WildCatDraft.agda` and can be explored independently.
