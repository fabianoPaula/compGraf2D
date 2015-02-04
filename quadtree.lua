local _M = {}
-- list of functions
local quadtree_meta = {}
quadtree_meta.__index = {}


function _M.quadtree(_left, _top, _width, _height)
	return setmetatable({
			left = _left,
			top = _top,
			width = _width,
			height = _height,
			children = nil,
			objects = {},
			elements = nil
	}, quadtree_meta)
end


function quadtree_meta.__index.subdivide(self,depth,maxdepth)
	if self.children ~= nil and depth < maxdepth then
		for i,child in pairs(self.children) do
			child:subdivide(depth+1,maxdepth)
		end
	else
		local x = self.left
		local y = self.top
		local w = floor(self.width / 2)
		local h = floor(self.height / 2)
		self.children = {
			_M.quadtree(x , y , w, h),
			_M.quadtree(x + w, y , w, h),
			_M.quadtree(x , y + h, w, h),
			_M.quadtree(x + w, y + h, w, h)
		}
	end
end
-- verifica se tem o ponto e retonar o quadtree que o possui.
function quadtree_meta.__index.check (self,x,y)
	if self.children then
		for i,child in pairs(self.children) do
			local chi = child:check(x,y)
			if chi ~= nil then 
				return chi
			end
		end
	else
		return self
	-- if x ~= nil and x-self.left < self.width and y - self.top  < self.height then 
	-- return self
	-- else
	-- return nil
	-- end
	 end
end

function quadtree_meta.__index.clean() 
	if self.children and depth < maxdepth then
		for i,child in pairs(self.children) do
			child:clean()
		end
	else
		if #self.element == 0 then
			self = nil
		end
	end
end


return _M
