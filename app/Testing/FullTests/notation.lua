keyword("Prop")

notation("[SORT `Prop]", "[prop]")
notation("[SORT [SORT x] `-> [SORT y]]", "[func `x `y]")
notation("[SORT `( [SORT x] `) ]", "`x")

const("some_type","Prop -> ((Prop -> Prop) -> Prop)")