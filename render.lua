local driver = require("driver")
local image = require("image")
local chronos = require("chronos")
local xform = require("xform")
local vec = require("vector")

local unpack = table.unpack
local abs   = math.abs

local _M = driver.new()

-- begin my requirements
require("dump")
local quad = require("quadratic")

local sqrt  = math.sqrt
local floor = math.floor
local max   = math.max
local min   = math.min
local deg   = math.deg
local atan2  = math.atan2
local inf   = math.huge
local EPS = 1.17549435E-38

-- ending my requirements


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

local function rootofline(a,b)
	return -b/a
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


-- begin line segment functions

function intersection(p0,p1,p)
	local result = nil
	-- This functions use the equation of line passing by two points and
	-- returns the value of the point aplied to the equation
	-- points: (x1,y1), (x2,y2)
	-- equation: (y2 - y1) x + (x1 - x2)y = y2x1 - y1x2
	local max = max(p0.y,p1.y)
	local min = min(p0.y,p1.y)
	if (p.y > max)or(p.y < min) then
		return false
	end

	local a = (p1.y - p0.y)
	local b = (p0.x - p1.x)
	local c = -p1.y*p0.x + p1.x*p0.y

	result = a*p.x + b*p.y + c 
	return(result * sign(a) > 0)
end
-- ending line segment functions


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

require("bezier")

-- My functions 

local insidefill = {}

function insidefill.triangle(shape,p)
	local p1 = {x=shape.x1 ,y=shape.y1 }
	local p2 = {x=shape.x2 ,y=shape.y2 }
	local p3 = {x=shape.x3 ,y=shape.y3 }
	local sum = 0 

	if  intersection(p1,p2,p) then
		sum = sum +  sign(p2.y - p1.y)   
	end
	if  intersection(p2,p3,p) then 
		sum = sum + sign(p3.y - p2.y)
	end
	if intersection(p3,p1,p) then
		sum = sum + sign(p1.y - p3.y)
	end
	return( sum ~= 0 )
end

function insidefill.polygon(shape,p)
	local points = shape.data
	local sum = 0

	for i = 1,#points,2 do
		local p0 = {x = points[i], y = points[i+1] }
		local p1 = nil
		if i < #points -2 then
			p1 = {x = points[i+2], y = points[i+3] }
		else
			p1 = {x = points[1], y = points[2] }
		end
		if intersection(p0,p1,p) then
			sum = sum + sign(p1.y - p0.y)	
		end 
	end
	return(sum ~= 0)
end

function insidefill.circle(shape, p)
	return (applytheconic(shape.conic,p.x,p.y) <= 0)
end

-- here is a somewhat verbose and repetitive implementation of the function
-- that dumps the paths in the RVG format, using iterators
function insidefill.path(shape, p)
	local seg = shape.segments
	local windingnumber = 0

	for i,b in pairs(seg) do
		if b['command'] == 'L' then
			local t = intersectionBezier1D(b,p)
			if t then
				local pt = bezier1D(b,t)
				if p.x < pt[1] then
					local dy = b['DerivateCoeff'][2]
					windingnumber = windingnumber + sign(dy)
				end
			end
		elseif b['command'] == 'Q' then
			local t = intersectionBezier2D(b,p)
			if t then
				local velocity = velocityBezier2D(b,t)
				windingnumber = windingnumber + sign(velocity[2])
			end
		elseif b['command'] == 'C' then
			local t = intersectionBezier3D(b,p)
			if t then
				local velocity = velocityBezier3D(b,t)
				windingnumber = windingnumber + sign(velocity[2])
			end 

		end

	end

	return( windingnumber ~= 0)
end

insideeofill = {}

function insideeofill.polygon(shape,p)
	local points = shape.data
	local sum = 0

	for i = 1,#points,2 do
		local p0 = {x = points[i], y = points[i+1] }
		local p1 = nil
		if i < #points -2 then
			p1 = {x = points[i+2], y = points[i+3] }
		else
			p1 = {x = points[1], y = points[2] }
		end
		if intersection(p0,p1,p) then 
			sum = sum + sign(p1.y - p0.y)
		end 
	end
	return(sum % 2 == 1)
end

local function preparescene(scene)
	-- implement
	local xf = scene.xf
	for k,e in ipairs(scene.elements) do
		e.paint.xf = xf * e.paint.xf
		e.shape.xf = xf * e.shape.xf
	end

	for k,e in ipairs(scene.elements) do
		if e.shape["type"] == "polygon" then 
			local s = e.shape
			local points = e.shape.data
			local xmin,xmax,ymin,ymax = points[1],points[1],points[2],points[2]

			for i = 1,#points,2 do
				points[i], points[i+1] = s.xf:apply(points[i],points[i+1])
			end

			for i = 1,#points,2 do
				-- caculate the minimun and maximun y and maximun x
				xmin = points[i] < xmin and points[i] or xmin 
				xmax = points[i] > xmax and points[i] or xmax
				ymin = points[i+1] < ymin and points[i+1] or ymin
				ymax = points[i+1] > ymax and points[i+1] or ymax 
			end
			s.xmin = xmin
			s.xmax = xmax
			s.ymin = ymin
			s.ymax = ymax
		end

		if e.shape['type'] == 'triangle' then
			local s = e.shape
			-- transform the vertex
			s.x1, s.y1 = s.xf:apply(s.x1, s.y1)
			s.x2, s.y2 = s.xf:apply(s.x2, s.y2)
			s.x3, s.y3 = s.xf:apply(s.x3, s.y3)

			s.ymax = max(s.y1,s.y2,s.y3)
			s.ymin = min(s.y1,s.y2,s.y3)
			s.xmax = max(s.x1,s.x2,s.x3)
			s.xmin = min(s.x1,s.x2,s.x3)
		end

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
			local s = e.shape
			local data = e.shape.data
			local xmin,ymin,xmax,ymax = inf,inf,0,0

			s.segments = {}
			local seg = s.segments

			local previous = ""
			for i,v in ipairs(s.instructions) do
				local o = s.offsets[i]
				local command = rvgcommand[v]
				if command then
					if command == "M" then
						data[o],data[o+2] = s.xf:apply(data[o],data[o+2])
					elseif command == "L" then
						data[o+2],data[o+3] = s.xf:apply(data[o+2],data[o+3])
						-- linear segment are always monotonic
						local points = {{data[o],data[o+1]},
										{data[o+2],data[o+3]}}
						seg[#seg+1] = newBezier1D(points[1],points[2])
						xmin = min(xmin,seg[#seg]['xmin'])
						ymin = min(ymin,seg[#seg]['ymin'])
						xmax = max(xmax,seg[#seg]['xmax'])
						ymax = max(ymax,seg[#seg]['ymax'])
					elseif command == "Q" then
						data[o+2],data[o+3] = s.xf:apply(data[o+2],data[o+3])
						data[o+4],data[o+5] = s.xf:apply(data[o+4],data[o+5])
						-- Quadratics could have three monotonic pieces
						local points = {{data[o],data[o+1]},
									    {data[o+2],data[o+3]},
		                                {data[o+4],data[o+5]}}
						--dump(newBezier2D(points[1],points[2],points[3]))
						local correct = monotoniseBezier2D(points[1],points[2],points[3])
						for i,e in pairs(correct) do
							seg[#seg+1] = e
							--dump(e)
							xmin = min(xmin,seg[#seg]['xmin'])
							ymin = min(ymin,seg[#seg]['ymin'])
							xmax = max(xmax,seg[#seg]['xmax'])
							ymax = max(ymax,seg[#seg]['ymax'])
						end
					elseif command == 'C' then
						data[o+2],data[o+3] = s.xf:apply(data[o+2],data[o+3])
						data[o+4],data[o+5] = s.xf:apply(data[o+4],data[o+5])
						data[o+6], data[o+7] = s.xf:apply(data[o+6],data[o+7])
						-- Cubics could have five monotonic pieces
						local points = {{data[o],data[o+1]},
									    {data[o+2],data[o+3]},
		                                {data[o+4],data[o+5]},
		                                {data[o+6],data[o+7]}}
						seg[#seg+1] = newBezier3D(points[1],points[2],points[3],points[4])
 					
						xmin = min(xmin,seg[#seg]['xmin'])
						ymin = min(ymin,seg[#seg]['ymin'])
						xmax = max(xmax,seg[#seg]['xmax'])
						ymax = max(ymax,seg[#seg]['ymax'])
					end
					previous = v
				end
			end
			s.xmin = xmin
			s.ymin = ymin
			s.xmax = xmax
			s.ymax = ymax
		end
	end
	return scene
end

local filltype = {}

function filltype.solid(paint,p)
	local r,g,b,a = unpack(paint.data)
	return r,g,b,a
end

function filltype.lineargradient(paint,p)
	local i = 0
	local ramp  = paint.data.ramp
	local x,y,w = paint.xf:apply(p.x,p.y)

	local result  = abs(x/paint.data.px)
	result = result % 1

	return ajusttoramp(ramp,result)
end

function filltype.radialgradient(paint,p)
	local i = 0
	local x,y,w = paint.xf:apply(p.x,p.y)


	local a = x*x + y*y
	local b = -2*x
	local c = 1 - paint.circleRadius*paint.circleRadius

	local root = {quad.quadratic(a,b,c)}

	local t = root[3]/root[2]
	t = abs(t)% 1

	return ajusttoramp(paint.data.ramp,t)
end

function filltype.fill(element,p)
	local shape = element.shape

	if (shape.ymax <= p.y)or(shape.ymin > p.y)or(shape.xmin > p.x)or(p.x > shape.xmax) then
		return false
	end 

	local callback = assert(insidefill[shape.type], 
	"No callback for "..shape.type)
	return callback(shape,p)
end

function filltype.eofill(element,p)
	local shape = element.shape

	if (shape.ymax <= p.y)or(shape.ymin > p.y)or(shape.xmin > p.x)or(p.x > shape.xmax) then
		return false
	end 

	local callback = assert(insideeofill[shape.type], 
	"No callback for "..shape.type)
	return callback(shape,p)
end

-- sample scene at x,y and return r,g,b,a
local function sample(scene, x, y)
	local p = { x=x, y=y}
	local color,ncolor = {1,1,1,1}, {}

	local layer = nil
	for k,e in pairs(scene.elements) do 
		local shapecallback = assert(filltype[e.type],
		"no handler for " .. e.type)
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



					--[[
					elseif command == "C" then
						local actual = {}
						actual["x1"] = data[o]
						actual["y1"] = data[o+1]
						actual["x2"] = data[o+2]
						actual["y2"] = data[o+3]
						actual["x3"] = data[o+4]
						actual["y3"] = data[o+5]
						actual["x4"] = data[o+6]
						actual["y4"] = data[o+7]
						actual["command"] = "C"
						seg[#seg+1] = actual
					elseif command == "R" then
						-- not implemented
						--[[
						local actual = {}
						actual["x1"] = data[o]
						actual["y1"] = data[o+1]
						actual["x2"] = data[o+2]
						actual["y2"] = data[o+3]
						actual["x3"] = data[o+4]
						actual["y3"] = data[o+5]
						actual["command"] = "R"
						seg[#seg+1] = actual
						data[o+4],data[o+5] = s.xf:apply(data[o+4],data[o+5])
						print(data[o+2], ",", data[o+3], ",")
						print(data[o+4], ",", data[o+5], ",")
						print(data[o+6], ",")
						--]]
						--
						--
	
--[[
					local ax = e['coeff'][1][1]
					local bx = e['coeff'][1][2] 
					local cx = e['coeff'][1][3] - p.x 

					local x0 = ax*t1^2  + bx*t1 + cx

					if x0 > 0 then
						local dy = e['DerivateCoeff'][2][1]*t1 + e['DerivateCoeff'][2][2]
						windingnumber = windingnumber + sign(dy)
					end
				end
				if (t2 >= 0 and t2 <= 1) then
					local ax = e['coeff'][1][1]
					local bx = e['coeff'][1][2] 
					local cx = e['coeff'][1][3] - p.x 

					local x0 = ax*t2^2  + bx*t2 + cx

					if x0 > 0 then
						local dy = e['DerivateCoeff'][2][1]*t1 + e['DerivateCoeff'][2][2]
						windingnumber = windingnumber + sign(dy)
					end
					
				end
			end
			--]]
