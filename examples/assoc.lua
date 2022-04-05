keyword("Prop")

nonterminal("NOTFUNC","SORT")

notation("[SORT `( [SORT x] `) `-> [SORT y]]","[func `x `y]")
notation("[SORT [NOTFUNC x] `-> [SORT y]]","[func `x `y]")
notation("[SORT `( [SORT x] `) ]","`x")
notation("[SORT [NOTFUNC x]]","`x")

notation("[NOTFUNC `Prop]","[prop]")
notation("[NOTFUNC `( [PROP x] `) ]","`x")

printGrammar()

const("test","Prop -> Prop -> Prop")