# ATT
A Type Theory I threw together during lockdown. ATT has:
- universal quantifiers (`forall (var: type), exp`) and normal implication (`A -> B`, desugars to `forall (_: A), B`)
- typed and untyped lambda-abstractions (`fun (var: type) => exp` and `fun var => exp` respectively)
- predicative universes - internally ATT builds up a directed graph representing the ordering of the universes, and checks if it is well-founded. Try `id True id`!
- *very* primitive 'holes' with no unification (i.e. `id _ id` will declare that ATT has `Found hole of type forall (a: Type), a -> a` but not fill it in) and annotations (`x : T`)
- nothing in the way of type inference whatsoever! (except for `(fun var => exp) : forall (x: A), B`)
- special syntax (and pretty printing) for naturals (i.e. `3` is elaborated to `S (S (S Z))`)

# The Command Language
ATT is interacted with using a (quite aesthetic, even if I say so myself) 'vernacular' command-oriented language a lá Coq - to the point of Coq syntax highlighting being entirely usable for ATT (however commands are *separated* - not terminated as in Coq - by a `.`). This language offers:
- definitions (`Definition name := exp`)
- axioms (`Axiom name : type`)
- the creation of arbitrary reductions (called ρ-reductions) for axioms (`Reduction (arg0 : t0) ... (argN : tN) (axiom exp0 ... expM) := exp)`)
- typechecking/inference (`Check exp`)
- universe constraint checking (`Check Constraints ...`)
    + valid constraints (comma-separated) are `X = Y, X >= Y, X > Y, X ≤ Y` and so on if `X` and `Y` are naturals
- evaluation of expressions (`Compute exp`)
- evaluation of expressions with a given reduction strategy (`Eval ... in exp`)
    + valid reduction strategies (space-separated) are `ehnf`, `esnf`, `(match exp)`, and `(unfolding ...)`
- creation inductive types (`Inductive name (arg0 : t0) ... (argN : tN) : exp := case0 : exp0 | ... | caseN : expN`) with automatically derived induction rules
- printing definitions or axioms (`Print name`) or the entire context (`Print All`), or the universe ordering graph (`Print Universes`).
- setting a name's δ-expansion or ρ-reduction to be reduced agressively (`Transparent name`)
- setting a name's δ-expansion or ρ-reduction to only be reduced during conversion (`Opaque name`)

In ATT, a name's δ-expansion or ρ-reduction is not, by default, reduced agressively, but instead only when types are being converted. For example, in the environment given by `Definition id := fun (A: Type) (x: A) => x`, only when attempting to match `id Type` with, say, `fun (y: Type) => y`, is the definition of `id` unfolded.

## Using ATT
ATT can be compiled and run with `cabal` by running `cabal new-repl`, where you should be given the prompt `att> `. The REPL accepts commands (for example `Definition False := forall (P: Type), P` and `Check x. Check y`), but also the queries `:l FILEPATH` which interprets the file at `FILEPATH`, and `:q` which quits the REPL. For example, you can test some examples with `:l examples.att`.