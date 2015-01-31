-- This function shows every element of the table
function dump(tbl, indent)
	if not indent then indent = 1 end
	space = "   "
	print(string.rep(space,indent-1) .. "{")
	for k, v in pairs(tbl) do
		formatting = string.rep(space, indent) .. k .. ": "
		if type(v) == "table" then
			print(formatting)
			dump(v, indent+1)
		elseif(type(v) ~= 'function')then
			print(formatting .. v)
		end
	end
	print(string.rep(space,indent-1) .. "}")
end 


-- This function create a copy of a table without metatables
function deepcopy(orig)
    local orig_type = type(orig)
    local copy
    if orig_type == 'table' then
        copy = {}
        for orig_key, orig_value in next, orig, nil do
            copy[deepcopy(orig_key)] = deepcopy(orig_value)
        end
    else -- number, string, boolean, etc
        copy = orig
    end
    return copy
end
