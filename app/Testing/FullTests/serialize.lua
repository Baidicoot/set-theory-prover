keyword("Prop")

notation("[SORT `Prop]", "[prop]")
notation("[SORT [SORT x] `-> [SORT y]]",
    "[func `x `y]")
notation("[SORT `( [SORT x] `) ]", "`x")

const("True","Prop")
assert("unit","True")

fp = io.open("serialized.atp","w+")
fp:write(dumpState())
fp:close()

