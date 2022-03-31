fp = io.open("serialized.atp")
includeState(fp:read("*all"))
fp:close()

beginProof("True")
    refine("unit")
endProof("easy")

