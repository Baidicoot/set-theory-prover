const("some_const","[prop]")
const("some_other_const","[prop]")
const("some_other_other_const","[prop]")
assert("some_axiom","some_const")
assert("some_other_axiom",
    "[imp some_const some_other_const]")

beginProof("some_other_other_const")
    refine("[modPon some_other_axiom [hole]]")
    refine("some_axiom")
endProof("logic")