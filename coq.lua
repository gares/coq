__t = {}
local M = {}

function M.parse(f)
	__t = {}
	local j = io.open(f)
	print("reading",f)
	for l in j:lines() do
		local x=loadstring("__t[#__t + 1] = "..l)
		if x then x() end
	end
	j:close()
	return __t
end

function M.interpret(t)
  local r = {
   id = t[1];
   file = t[2];
   char_begin = t[3];
   char_end = t[4];
   res = t[5];
   time = math.abs(t[6]);
   init = t[7];
   hashcons = t[8];
   red_time = t[9];
   success = t[10];
  }
  r.raw_time = math.max(0,r.time - r.init - r.hashcons)
  r.conv_time = math.max(0,r.raw_time - r.red_time)
  return r
end

return M
