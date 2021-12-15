const("True", "[prop]")
assert("unit", "True")

sort("Set")

beginProof("[forall x Set True]")
    refine("[introObj x Set [hole]]")
    refine("unit")
endProof("pointless")