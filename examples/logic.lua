require "examples/utils"
import "notations"

const("True","Prop")
const("False","Prop")

assert("unit","True")

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

beginProof("∀x:Prop, ∀y:Prop, (x <=> y) => (y <=> x)")
    refine("introObj x:Prop, _")
    refine("introObj y:Prop, _")
    refine("introThm Z: _, _")
    refine("((subst _ in (subst _ in and_inj)) _) _")
    refine("(subst _ in (subst _ in and_proj_right)) Z")
    refine("(subst _ in (subst _ in and_proj_left)) Z")
endProof("iff_refl")