const("True", "(prop)")
assert("unit", "True")
sort("Set")

beginProof("(forall x Set True)")
    refine("(introsObj x Set (hole))")
    refine("unit")
endProof("pointless")