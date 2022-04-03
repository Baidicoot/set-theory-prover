require "examples/utils"
import "logic"

sort("Set")

const("member","Set -> (Set -> Prop)")
notation("[PROP [PROP x] `∈ [PROP y]]","(member `x) `y")
notation("[PROP [PROP x] `∉ [PROP y]]","¬(`x ∈ `y)")

beginProof("∀φ:Prop, ∀χ:Prop, ∀ψ:Prop, (φ ∧ χ) => ((φ => (χ => ψ)) => ψ)")
    refine("introObj φ:Prop, _")
    refine("introObj χ:Prop, _")
    refine("introObj ψ:Prop, _")
    refine("introThm H:_, _")
    refine("introThm F:_, _")
    refine("(F _) _")
    refine("(subst _ in (subst _ in and_proj_left)) H")
    refine("(subst _ in (subst _ in and_proj_right)) H")
endProof("destruct_and")

beginProof("∀φ:Prop, (φ => ¬φ) => (((¬φ) => φ) => False)")
    refine("introObj φ:Prop, _")
    refine("introThm H0:_, _")
    refine("introThm H1:_, _")
    refine("(((subst _ in (subst _ in (subst _ in or_proj))) _) _) (subst φ in excluded_middle)")
        
        refine("introThm H2:_, _")
        refine("H2 (H1 H2)")

        refine("introThm H2:_, _")
        refine("(H0 H2) H2")
endProof("contradiction_loop")

beginProof("∀x:Set, ¬(∀y:Set, (y ∉ y) <=> (y ∈ x))")
    refine("introObj x:Set, _")
    refine("introThm H:_, _")
    refine("((subst _ in (subst _ in (subst _ in destruct_and))) (subst x in H)) _")
    refine("introThm H0:_, _")
    refine("introThm H1:_, _")
    refine("((subst _ in contradiction_loop) H1) H0")
endProof("no_russell_set")