require "examples/utils"

notation("[SORT `( [SORT x] `) ]", "`x")
notation("[SORT Prop ]", "[prop]")
notation("[SORT [SORT x] `-> [SORT y] ]", "[func `x `y]")

notation("[PROP `( [PROP x] `) ]", "`x")
notation("[PROP `_ ]", "[hole]")
notation("[PROP `λ [IDENT x] `. [PROP y] ]", "[lam `x `y]")
notation("[PROP `∀ [IDENT x] `: [SORT y] `, [PROP z] ]", "[forall `x `y `z]")
notation("[PROP [PROP x] `=> [PROP y] ]", "[imp `x `y]")
notation("[PROP [PROP x] [PROP y] ]", "[app `x `y]")

notation("[PROOF `( [PROOF x] `) ]", "`x")
notation("[PROOF `_ ]", "[hole]")
notation("[PROOF introThm [IDENT x] `: [PROP y] `, [PROOF z] ]", "[introThm `x `y `z]")
notation("[PROOF introObj [IDENT x] `: [SORT y] `, [PROOF z] ]", "[introObj `x `y `z]")
notation("[PROOF subst [PROOF x] [PROP y] ]", "[uniElim `x `y]")
notation("[PROOF [PROOF x] [PROOF y] ]", "[modPon `x `y]")

export "notations"