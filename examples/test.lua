const("True", "(prop)")
assert("unit", "True")

const("True2", "(prop)")
assert("unit2", "True2")

sort("Set")

beginProof("(forall x Set True)")
    refine("(introsObj x Set (hole))")
    refine("unit2")
endProof("pointless")