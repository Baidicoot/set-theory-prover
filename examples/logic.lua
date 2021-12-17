notation("[SORT `( [SORT x] `) ]", "`x")
notation("[SORT Prop ]", "[prop]")
notation("[SORT [SORT x] `-> [SORT y] ]", "[func `x `y]")

notation("[PROP `( [PROP x] `) ]", "`x")
notation("[PROP `_ ]", "[hole]")
notation("[PROP `λ [IDENT x] `. [PROP y] ]", "[lam `x `y]")
notation("[PROP `∀ [IDENT x] `: [SORT y] `, [PROP z] ]", "[forall `x `y `z]")
notation("[PROP [PROP x] `=> [PROP y] ]", "[imp `x `y]")
notation("[PROP [PROP x] [PROP y] ]", "[app `x `y]")

notation("[PROOF `( [PROOF x] `) ]", "`x")
notation("[PROOF `_ ]", "[hole]")
notation("[PROOF introThm [IDENT x] `: [PROP y] `, [PROOF z] ]", "[introThm `x `y `z]")
notation("[PROOF introObj [IDENT x] `: [SORT y] `, [PROOF z] ]", "[introObj `x `y `z]")
notation("[PROOF [PROOF x] `{ [PROP y] `} ]", "[uniElim `x `y]")
notation("[PROOF [PROOF x] [PROOF y] ]", "[modPon `x `y]")

const("True","Prop")
const("False","Prop")

assert("trivial","True")

const("and","Prop -> (Prop -> Prop)")
const("or","Prop -> (Prop -> Prop)")

notation("[PROP [PROP x] `∧ [PROP y] ]","(and `x) `y")
notation("[PROP [PROP x] `∨ [PROP y] ]","(or `x) `y")

assert("and_proj_left","∀x:Prop, ∀y:Prop, (x ∧ y) => x")
assert("and_proj_right","∀x:Prop, ∀y:Prop, (x ∧ y) => y")

assert("and_inj","∀x:Prop, ∀y:Prop, x => (y => (x ∧ y))")

assert("or_inj_left","∀x:Prop, ∀y:Prop, x => (x ∨ y)")
assert("or_inj_right","∀x:Prop, ∀y:Prop, y => (x ∨ y)")

assert("or_proj","∀x:Prop, ∀y:Prop, ∀z:Prop, (x => z) => ((y => z) => ((x ∨ y) => z))")

define("iff","λ x. λ y. ((x => y) ∧ (y => x))")

notation("[PROP [PROP x] `<=> [PROP y] ]","(iff `x) `y")

define("id","λ x. x")

beginProof("True <=> True")