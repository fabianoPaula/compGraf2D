local driver = require("driver")
local image = require("image")
local chronos = require("chronos")
local xform = require("xform")
local vec = require("vector")

local unpack = table.unpack
local abs   = math.abs

local _M = driver.new()

-- begin my requirements
local quad = require("quadratic")
local cubic = require("cubic")

local sqrt  = math.sqrt
local floor = math.floor
local max   = math.max
local min   = math.min
local deg   = math.deg
local atan2  = math.atan2
local inf   = math.huge
local EPS = 1.17549435E-38

-- ending my requirements

function _M.triangle(x1, y1, x2, y2, x3, y3)
	return _M.path{_M.M,x1,y1,_M.L,x2,y2,_M.L,x3,y3,_M.L,x1,y1,_M.Z}
end


function _M.polygon(data)
	local inst = {}	-- instrcutions
	inst[1] = _M.M
	inst[2] = data[1]
	inst[3] = data[2]
	for i = 3, #data, 2 do 
		inst[#inst + 1] = _M.L
		inst[#inst + 1] = data[i]
		inst[#inst + 1] = data[i+1]
	end
	inst[#inst + 1] = _M.L
	inst[#inst + 1] = data[1]
	inst[#inst + 1] = data[2]
	inst[#inst+1] = _M.Z
    return _M.path(inst) -- this shouldn't be empty, of course
end


local rvgcommand = {
    begin_open_contour = "M",
    begin_closed_contour = "M",
    linear_segment = "L",
    quadratic_segment = "Q",
    rational_quadratic_segment = "R",
    cubic_segment = "C",
    end_closed_contour = "Z",
}



-- begin basic functions
local function sign(n)
	if n > 0 then
		return 1
	elseif n < 0 then 
		return -1
	else
		return 0
	end
end

local function composecolor(color,ncolor)
	local r, g, b, a = unpack(color)
	local nr, ng, nb, alpha = unpack(ncolor)

	r = alpha*nr + (1-alpha)*r
	g = alpha*ng + (1-alpha)*g
	b = alpha*nb + (1-alpha)*b

	return {r,g,b,a}
end

-- ending basic functions 

-- begin gradient functions

local function ajusttoramp(ramp,x)
	local lambda, xmin, xmax,index = 0,0,0,0
	for i = 1,#ramp-2,2 do
		if (ramp[i] <= x) and (x <= ramp[i+2]) then
			xmin, xmax = ramp[i], ramp[i+2]
			index = i
		end
	end

	local result = (x - xmin)/(xmax - xmin)

	local r = (1 - result)*ramp[index+1][1] + result*ramp[index+3][1]
	local g = (1 - result)*ramp[index+1][2] + result*ramp[index+3][2]
	local b = (1 - result)*ramp[index+1][3] + result*ramp[index+3][3]
	local a = (1 - result)*ramp[index+1][4] + result*ramp[index+3][4]
	return r,g,b,a
end

-- ending gradient functions

-- begin conic functions 
-- this a function was created to return quickly if a point is inside a conic
local function applytheconic(conic,x,y)
	local v = vec.vector(x,y)
	local aux =  conic * v
	local result,rest = v:dot(aux)
	return result + rest
end

local function conic2origin(conic)
	local a,h,g,h1,b,f,g1,f1,c = unpack(conic)
	local p = (-b*g + f*h)/(a*b - h*h)
	local q = (a*f - g*h)/(-a*b + h*h)
	return p,q
end

local function boundBox(shape, conic)
	-- translate the center of ellipse to the origin
	t = xform.translate(conic2origin(conic))
	local nconic = t:transpose()*conic*t
	-- new coefficients
	a,h,g,h1,b,f,g1,f1,c = unpack(nconic)
	-- limits of the box
	y1 = sqrt((a*c)/ (h*h - a*b))
	y2 = -1*y1

	x1 = sqrt((b*c)/ (h*h - a*b))
	x2 = -1*x1

	-- needs the inverse transfomation
	x1,y1 = t:apply(x1,y1)
	x2,y2 = t:apply(x2,y2)
	return x2,y2,x1,y1 
end

-- ending conic functions 

local function lerp(x0, x1, a)
    local a1 = 1-a
    return a1*x0+a*x1
end

-- quadratic interpolation
local function lerp2(x0, x1, x2, a, b)
    local x00 = lerp(x0, x1, a)
    local x01 = lerp(x1, x2, a)
    return lerp(x00, x01, b)
end

local function lerp3(x0,x1,x2,x3,a,b,c)
	local x00 = lerp2(x0,x1,x2,a,b)
	local x01 = lerp2(x1,x2,x3,a,b)
	return lerp(x00,x01,c)
end

function linear_coefficients(x0,x1)
	return x1 - x0,x0
end


function quadratic_coefficients(x0,x1,x2)
	return (x0 - 2*x1 + x2), 2*(x1-x0), x0
end

function cubic_coefficients(x0,x1,x2,x3)
	return (x3+3*x1-3*x2-x0), 3*(x0-2*x1+x2), 3*(x1-x0), x0
end

local inside = {}

function inside.circle(shape, p)
	if (applytheconic(shape.conic,p[1],p[2]) <= 0) then 
		return 1
	else
		return 0
	end
end

-- here is a somewhat verbose and repetitive implementation of the function
-- that dumps the paths in the RVG format, using iterators
function inside.path(path, p)
	local winding = 0
    local iterator = {}
	function iterator:begin_open_contour(len, x0, y0)
    end
    function iterator:begin_closed_contour(len, x0, y0)
    end
    function iterator:linear_segment(x0, y0, x1, y1)
		local a,b = linear_coefficients(y0,y1)
		if a ~= 0 then
			local t  = (-b+p[2]) /a
			if t >= 0 and t < 1 then
				if p[1] < lerp(x0,x1,t)then
					winding = winding + sign(a)
				end
			end
		end
    end
    function iterator:quadratic_segment(x0, y0, x1, y1, x2, y2)
		local a,b,c = quadratic_coefficients(y0,y1,y2)
		local root = {quad.quadratic(a,b,c - p[2])}
		if root[1] == 2 then
			for i = 2,4,2 do
				local t = root[i]/root[i+1]
				if t >= 0 and t < 1 then
					if p[1] < lerp2(x0,x1,x2,t,t)then
						winding = winding + sign(2*a*t + b)
					end
				end
			end
		end
	end
    function iterator:rational_quadratic_segment(x0, y0, x1, y1, w1, x2, y2)
    end
    function iterator:cubic_segment(x0, y0, x1, y1, x2, y2, x3, y3)
		local a,b,c,d = cubic_coefficients(y0,y1,y2,y3)
		local root = {cubic.cubic(a,b,c,d -  p[2])}
		for i = 2,#root-1,2 do
			local t = root[i]/root[i+1]
			if t >= 0 and t < 1 then
				if p[1] < lerp3(x0,x1,x2,x3,t,t,t)then
					winding = winding + sign(3*a*t^2 + 2*b*t + c)
				end
			end
		end
    end
    function iterator:end_open_contour(len)
    end
    function iterator:end_closed_contour(len)
    end
   	path:iterate(iterator)
	return winding 
end

local function preparescene(scene)
	-- implement
	local xf = scene.xf
	for k,e in ipairs(scene.elements) do
		e.paint.xf = xf * e.paint.xf
		e.shape.xf = xf * e.shape.xf
	end

	for k,e in ipairs(scene.elements) do

		if e.shape['type'] == 'circle' then
			local s = e.shape
			local a,b,f,g = 1,1,-1*s.cy,-1*s.cx
			local c = s.cx*s.cx + s.cy*s.cy - s.r*s.r
			s.conic = xform.xform(a,0,g, 0,b,f, g,f,c)
			s.conic = s.xf:inverse():transpose() * s.conic * s.xf:inverse() 
			-- aplly the transform to the circle to be a ellipse for example
			s.xmin, s.ymin, s.xmax, s.ymax = boundBox(s,s.conic)
		end

		if e.paint['type'] == 'lineargradient' then
			local p = e.paint

			local tp1 = xform.translate(unpack(p.data.p1)):inverse()

			p.data.tp2 = {tp1:apply(unpack(p.data.p2))}

			local degree = deg(atan2(p.data.tp2[2],p.data.tp2[1]))
			local rot = xform.rotate(-degree)

			-- rotate p2 to be in the x-axis
			p.data.tp2 = {rot:apply(unpack(p.data.p2))}
			p.data.px = p.data.tp2[1]
			p.xf = rot*tp1*p.xf:inverse()
		end

		if e.paint['type'] == 'radialgradient' then
			local p = e.paint

			local center = p.data.center
			local r = p.data.radius

			-- use implicity representation
			local a,b,f,g = 1,1,-center[2],-center[1]
			local c = center[1]*center[1] + center[2]*center[2] - r*r
			p.circle = xform.xform(a,0,g, 0,b,f, g,f,c)

			-- translate the focus to the origin
			local tfocus = xform.translate(unpack(p.data.focus)):inverse()

			-- translate the focus to the origin, center and the circle
			p.data.tcenter = {tfocus:apply(unpack(p.data.center))}
			p.circle = tfocus:inverse():transpose() * p.circle * tfocus:inverse() 

			assert(applytheconic(p.circle,p.data.tcenter[1],p.data.tcenter[2]) < 0, 
			"the center is out of the conic")


			local degree = deg(atan2(p.data.tcenter[2],p.data.tcenter[1]))
			local rot = xform.rotate(-degree)

			p.data.tcenter = {rot:apply(unpack(p.data.tcenter))}
			p.circle = rot:inverse():transpose() * p.circle * rot:inverse() 

			local centerscale = 1/p.data.tcenter[1]
			local tscale = xform.scale(centerscale)

			p.data.tcenter = {tscale:apply(unpack(p.data.tcenter))}
			p.circle = tscale:inverse():transpose() * p.circle * tscale:inverse() 

			assert( (p.circle[1] - p.circle[2+3]) < EPS, 
			"problems with implicity representation of the circle in the radialgradient")

			p.circleRadius = sqrt(abs(p.circle[3+6]/p.circle[1] - 1))
			p.xf = rot * tscale * tfocus * p.xf:inverse()
		end

		if e.shape['type'] == 'path' then
			local shape = e.shape
			local xfs = e.shape.xf
			local data = e.shape.data
			local xmin,ymin,xmax,ymax = inf,inf,0,0
			
		    for i,v in ipairs(shape.instructions) do
		        local o = shape.offsets[i]
		        local s = rvgcommand[v]
		        if s then
		            if s == "M" then
		                data[o+1],data[o+2] = xfs:apply(data[o+1],data[o+2])
						xmin = min(xmin,data[o+1])
						ymin = min(ymin,data[o+2])
						xmax = max(xmax,data[o+1])
						ymax = max(ymax,data[o+2])
		            elseif s == "L" then
		                data[o+2],data[o+3] = xfs:apply(data[o+2],data[o+3])
						xmin = min(xmin,data[o+2])
						ymin = min(ymin,data[o+3])
						xmax = max(xmax,data[o+2])
						ymax = max(ymax,data[o+3])
		            elseif s == "Q" then
		                data[o+2],data[o+3] = xfs:apply(data[o+2],data[o+3])
		                data[o+4],data[o+5] = xfs:apply(data[o+4],data[o+5])
						xmin = min(xmin,data[o+2],data[o+4])
						ymin = min(ymin,data[o+3],data[o+5])
						xmax = max(xmax,data[o+2],data[o+4])
						ymax = max(ymax,data[o+3],data[o+5])
        		    elseif s == "C" then
		                data[o+2],data[o+3] = xfs:apply(data[o+2],data[o+3])
		                data[o+4],data[o+5] = xfs:apply(data[o+4],data[o+5])
		                data[o+6],data[o+7] = xfs:apply(data[o+6],data[o+7])
						xmin = min(xmin,data[o+2],data[o+4],data[o+6])
						ymin = min(ymin,data[o+3],data[o+5],data[o+7])
						xmax = max(xmax,data[o+2],data[o+4],data[o+6])
						ymax = max(ymax,data[o+3],data[o+5],data[o+7])
		            elseif s == "R" then
						data[o+2],data[o+3],data[o+4] = xfs:apply(data[o+2],
											data[o+3],data[o+4])
						data[o+5],data[o+6] = xfs:apply(data[o+5],data[o+6])
						xmin = min(xmin,data[o+2],data[o+5])
						ymin = min(ymin,data[o+3],data[o+6])
						xmax = max(xmax,data[o+2],data[o+5])
						ymax = max(ymax,data[o+3],data[o+6])
		            end
		        end
		    end
			shape.xmin = xmin
			shape.ymin = ymin
			shape.xmax = xmax
			shape.ymax = ymax
		end
	end
	return scene
end

local filltype = {}

function filltype.solid(paint,p)
	local r,g,b,a = unpack(paint.data)
	local opacity = paint.opacity
	return opacity*r,opacity*g, opacity*b,	opacity*a
end

function filltype.lineargradient(paint,p)
	local i = 0
	local ramp  = paint.data.ramp
	local opacity = paint.opacity
	local x,y,w = paint.xf:apply(p[1],p[2])

	local result  = abs(x/paint.data.px)
	result = result % 1

	
	local r,g,b,a = ajusttoramp(ramp,result)
	return opacity*r,opacity*g, opacity*b,	opacity*a
end

function filltype.radialgradient(paint,p)
	local i = 0
	local x,y,w = paint.xf:apply(p[1],p[2])

	local opacity = paint.opacity
	local ramp    = paint.data.ramp

	local a = x*x + y*y
	local b = -2*x
	local c = 1 - paint.circleRadius*paint.circleRadius

	local root = {quad.quadratic(a,b,c)}

	local t = root[3]/root[2]
	t = abs(t)% 1

	local r,g,b,a = ajusttoramp(ramp,t)
	return opacity*r,opacity*g, opacity*b,	opacity*a
end

function shapecallback(element,p)
	local shape = element.shape

	if (shape.ymax <= p[2])or(shape.ymin > p[2])or
		(shape.xmin > p[1])or(p[1] > shape.xmax) then
		return false
	end 

	local callback = assert(inside[shape.type], 
	"No callback for "..shape.type)
	local result = callback(shape,p)

	if element.type == 'fill' then
		return (result ~= 0)
	elseif element.type == 'eofill' then
		return (result % 2 == 1)
	end
end

function filltype.eofill(element,p)
	local shape = element.shape

	if (shape.ymax <= p[2])or(shape.ymin > p[2])
		or(shape.xmin > p[1])or(p[1] > shape.xmax) then
		return false
	end 

	local callback = assert(insideeofill[shape.type], 
	"No callback for "..shape.type)
	return callback(shape,p)
end

-- sample scene at x,y and return r,g,b,a
local function sample(scene, x, y)
	local p = {x,y}
	local color,ncolor = {1,1,1,1}, {}

	local layer = nil
	for k,e in pairs(scene.elements) do 
	--	local shapecallback = assert(filltype[e.type],
	--	"no handler for " .. e.type)
		if shapecallback(e,p) then
			local paintcallback = assert(filltype[e.paint.type],
			"no handler for " .. e.paint.type)

			ncolor = {paintcallback(e.paint,p)}
			color = composecolor(color,ncolor)
		end
	end
	return unpack(color)
end

-- verifies that there is nothing unsupported in the scene
local function checkscene(scene)
	for i, element in ipairs(scene.elements) do
		assert(element.type == "fill" or
		element.type == "eofill", "unsupported element")
		assert(element.shape.type == "circle" or
		element.shape.type == "triangle" or
		element.shape.type == "polygon"  or
		element.shape.type == "path", "unsuported primitive")
		assert(not element.shape.style, "stroking not unsuported")
		assert(element.paint.type == "solid" or
		element.paint.type == "lineargradient" or
		element.paint.type == "radialgradient" or
		element.paint.type == "texture",
		"unsupported paint")
	end
end

-- output formatted string to stderr
local function stderr(...)
	io.stderr:write(string.format(...))
end

function _M.render(scene, viewport, file)
	local time = chronos.chronos()
	-- make sure scene does not contain any unsuported content
	checkscene(scene)
	-- transform and prepare scene for rendering
	scene = preparescene(scene)
	-- get viewport
	local vxmin, vymin, vxmax, vymax = unpack(viewport, 1, 4)
	stderr("preprocess in %.3fs\n", time:elapsed())
	time:reset()
	-- get image width and height from viewport
	local width, height = vxmax-vxmin, vymax-vymin
	-- allocate output image
	local img = image.image(width, height)
	-- render
	for i = 1, height do
		stderr("\r%d%%", floor(1000*i/height)/10)
		for j = 1, width do
			img:set(j, i, sample(scene, j-0.5, i-0.5))
		end
	end
	stderr("\n")
	stderr("rendering in %.3fs\n", time:elapsed())
	time:reset()
	-- store output image
	image.png.store8(file, img)
	stderr("saved in %.3fs\n", time:elapsed())
end

return _M
