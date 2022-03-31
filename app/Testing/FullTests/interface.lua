sort("Set")
const("empty","Set")

notation("[PROP `∅]","empty")

const("True","[prop]")
assert("unit","True")

keyword("test")

define("trivial","True")

beginProof("trivial")
    refine("unit")
    done()
endProof("easy")