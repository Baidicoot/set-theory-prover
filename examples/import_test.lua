require "examples/utils"
import "notations"

const("True","Prop")
assert("unit","True")

beginProof("∀x:Prop,True")
    refine("introObj x : Prop, _")
    refine("unit")
endProof("pointless")