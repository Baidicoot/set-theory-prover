print("this is a test of the CLI API")

require "examples/utils"
import "notations"

sort("Nat")

const("0","Nat")
const("S","Nat -> Nat")

function topeano(n)
    peano = "0"
    for i=1,n do
        peano = "S ("..peano..")"
    end
    return peano
end

for i=1,9 do
    define(tostring(i),topeano(i))
end