# ATT
A (very minimal) Type Theory I threw together in an attempt to stave off the boredom during lockdown, which, in the end, yielded little avail. ATT has:
- universal quantifiers (`forall (var: type), exp`) and normal implication (`A -> B`, desugars to `forall (_: A), B`)
- typed and untyped lambda-abstractions (`fun (var: type) => exp` and `lam var => exp` respectively)
- predicative universes - internally ATT builds up a directed graph representing the ordering of the universes, and checks if it is well-founded. Try `id True id`!
- *very* primitive 'holes' (i.e. `id Set _` will declare that ATT has `found hole of type Set`) and annotations (`x : T`)
- nothing in the way of type inference whatsoever! (except for `(lam var => exp) : forall (x: A), B`)

It is interacted with using a (quite aesthetic) 'vernacular' (if it can possibly be described as that) command-oriented language a lá Coq - to the point of Coq syntax highlighting being entirely usable for ATT. (however commands are *separated* - not terminated as in Coq - by a `.`). This language offers:
- the ability to add definitions to the context (`Definition name := exp`)
- the ability to add axioms to the context (`Axiom name : type`)
- the ability to check the types of expressions (`Check exp`)
- the ability to evaluate expressions (`Eval exp`)
- the ability to print definitions or axioms (`Print name`) or the entire context (`Print All`).

One point of minor interest is the handling of global identifiers in types and expressions - in ATT, their δ-expansion is delayed until the name is incompatibly matched with another type, at which point it is unfolded. For example, in the environment given by `Definition id := fun (A: Set) (x: A) => x`, only when attempting to match `id Set` with, say, `fun (y: Set) => y`, is the definition of `id` unfolded.

## Using ATT
ATT can be compiled and run with `cabal` by running `cabal new-repl`, where you should be given the prompt `att> `. The REPL accepts commands (for example `Definition False := forall (P: Set), P` and `Check x. Check y`), but also the queries `:l FILEPATH` which interprets the file at `FILEPATH`, and `:q` which quits the REPL. For example, you can test some examples with `:l examples.att`.