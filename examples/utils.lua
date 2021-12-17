function import(n)
    fp = io.open(n..".atp")
    includeState(fp:read("*all"))
    fp:close()
end

function export(n)
    fp = io.open(n..".atp","w+")
    fp:write(dumpState())
    fp:close()
end

utils = {
    import = import,
    export = export
}

return utils