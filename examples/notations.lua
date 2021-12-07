notation("[SORT `( [SORT x] `) ]", "`x")
notation("[SORT Prop ]", "[prop]")
notation("[SORT [SORT x] `-> [SORT y] ]", "[func `x `y]")

const("test1", "Prop -> Prop")
const("test2", "(Prop -> Prop) -> Prop")
const("test3", "Prop -> Prop -> Prop")