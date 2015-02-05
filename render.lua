local driver = require"driver"
local image = require"image"
local chronos = require"chronos"

local sqrt = math.sqrt
local min = math.min
local max = math.max
local unpack = table.unpack
local floor = math.floor
local abs = math.abs

-- output formatted string to stderr
local function stderr(...)
    io.stderr:write(string.format(...))
end

local FLT_MIN = 1.17549435E-38 -- smallest-magnitude normalized single-precision
local TOL = 0.01 -- root-finding tolerance, in pixels
local MAX_ITER = 30 -- maximum number of bisection iterations in root-finding
local MAX_DEPTH = 8 -- maximum quadtree depth

local _M = driver.new()

-- here are functions to cut a rational quadratic Bezier
-- you can write your own functions to cut lines,
-- integral quadratics, and cubics

-- linear interpolation
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

-- cubic interpolation
local function lerp3(x0,x1,x2,x3,a,b,c)
	local x00 = lerp2(x0,x1,x2,a,b)
	local x01 = lerp2(x1,x2,x3,a,b)
	return lerp(x00,x01,c)
end

-- cut canonic rational quadratic segment and recanonize
local function cutr2s(a, b, x0, y0, x1, y1, w1, x2, y2)
    local u0 = lerp2(x0, x1, x2, a, a)
    local v0 = lerp2(y0, y1, y2, a, a)
    local r0 = lerp2(1, w1, 1, a, a)
    local u1 = lerp2(x0, x1, x2, a, b)
    local v1 = lerp2(y0, y1, y2, a, b)
    local r1 = lerp2(1, w1, 1, a, b)
    local u2 = lerp2(x0, x1, x2, b, b)
    local v2 = lerp2(y0, y1, y2, b, b)
    local r2 = lerp2(1, w1, 1, b, b)
    local ir0, ir2 = 1/r0, 1/r2
    assert(ir0*ir2 >= 0, "canonization requires split!")
    local ir1 = sqrt(ir0*ir2)
    return u0*ir0, v0*ir0, u1*ir1, v1*ir1, r1*ir1, u2*ir2, v2*ir2
end

-- here are functions to find a root in a rational quadratic
-- you can write your own functions to find roots for lines,
-- integral quadratics, and cubics

-- assumes monotonic and x0 <= 0 <= x2
local function recursivebisectrationalquadratic(x0, x1, w1, x2, ta, tb, n)
    local tm = 0.5*(ta+tb)
    local xm = lerp2(x0, x1, x2, tm, tm)
    local wm = lerp2(1, w1, 1, tm, tm)
    if abs(xm) < TOL*abs(wm) or n >= MAX_ITER then
        return tm
    else
        n = n + 1
        if (wm < 0) ~= (xm < 0) then ta = tm
        else tb = tm end
        -- tail call
        return recursivebisectrationalquadratic(x0, x1, w1, x2, ta, tb, n)
    end
end

-- assumes monotonic and root in [0, 1]
local function bisectrationalquadratic(x0, x1, w1, x2)
    -- ensure root is bracketed by [0,1]
    assert(x2*x0 <= 0, "no root in interval!")
    -- reorder segment so it is increasing
    if x0 > x2 then
        return 1-recursivebisectrationalquadratic(x2, x1, w1, x0, 0, 1, 0)
    else
        return recursivebisectrationalquadratic(x0, x1, w1, x2, 0, 1, 0)
    end
end

-- transforms path by xf and ensures it is closed by a final segment
local function newxformer(xf, forward)
    local fx, fy -- first contour cursor
    local px, py -- previous cursor
    local xformer = {}
    function xformer:begin_closed_contour(len, x0, y0)
        fx, fy = xf:apply(x0, y0)
        forward:begin_closed_contour(_, fx, fy)
        px, py = fx, fy
    end
    xformer.begin_open_contour = xformer.begin_closed_contour
    function xformer:end_closed_contour(len)
        if px ~= fx or py ~= fy then
            forward:linear_segment(px, py, fx, fy)
        end
        forward:end_closed_contour(_)
    end
    xformer.end_open_contour = xformer.end_closed_contour
    function xformer:linear_segment(x0, y0, x1, y1)
       x1, y1 = xf:apply(x1, y1)
       forward:linear_segment(px, py, x1, y1)
       px, py = x1, y1
    end
    function xformer:quadratic_segment(x0, y0, x1, y1, x2, y2)
        x1, y1 = xf:apply(x1, y1)
        x2, y2 = xf:apply(x2, y2)
        forward:quadratic_segment(px, py, x1, y1, x2, y2)
        px, py = x2, y2
    end
    function xformer:rational_quadratic_segment(x0, y0, x1, y1, w1, x2, y2)
        x1, y1, w1 = xf:apply(x1, y1, w1)
        x2, y2 = xf:apply(x2, y2)
        assert(w1 > FLT_MIN, "unbounded rational quadratic segment")
        forward:rational_quadratic_segment(px, py, x1, y1, w1, x2, y2)
        px, py = x2, y2
    end
    function xformer:cubic_segment(x0, y0, x1, y1, x2, y2, x3, y3)
        x1, y1 = xf:apply(x1, y1)
        x2, y2 = xf:apply(x2, y2)
        x3, y3 = xf:apply(x3, y3)
        forward:cubic_segment(px, py, x1, y1, x2, y2, x3, y3)
        px, py = x3, y3
    end
    return xformer
end

-- remove segments that degenerate to points
-- should be improved to remove "almost" points
-- assumes segments are monotonic
local function newcleaner(forward)
    local cleaner = {}
    function cleaner:begin_closed_contour(len, x0, y0)
        forward:begin_closed_contour(_, x0, y0)
    end
    cleaner.begin_open_contour = cleaner.begin_closed_contour
    function cleaner:linear_segment(x0, y0, x1, y1)
        if x0 ~= x1 or y0 ~= y1 then
            forward:linear_segment(px, py, x1, y1)
        end
    end
    function cleaner:quadratic_segment(x0, y0, x1, y1, x2, y2)
        if x0 ~= x2 or y0 ~= y2 then
            forward:quadratic_segment(x0, y0, x1, y1, x2, y2)
        end
    end
    function cleaner:rational_quadratic_segment(x0, y0, x1, y1, w1, x2, y2)
        if x0 ~= x2 or y0 ~= y2 then
            if abs(w1-1) > FLT_MIN then
                forward:rational_quadratic_segment(x0, y0, x1, y1, w1, x2, y2)
            else
                forward:quadratic_segment(x0, y0, x1, y1, x2, y2)
            end
        end
    end
    function cleaner:cubic_segment(x0, y0, x1, y1, x2, y2, x3, y3)
        if x0 ~= x3 or y0 ~= y3 then
            forward:cubic_segment(x0, y0, x1, y1, x2, y2, x3, y3)
        end
    end
    function cleaner:end_closed_contour(len)
        forward:end_closed_contour(_)
    end
    cleaner.end_open_contour = cleaner.end_closed_contour
    return cleaner
end

-- here is a function that returns a path transformed to
-- pixel coordinates using the iterator trick I talked about
-- you should chain your own implementation of monotonization!
-- if you don't do that, your life will be *much* harder
function transformpath(oldpath, xf)
    local newpath = _M.path()
    newpath:open()
    oldpath:iterate(
        newxformer(xf * oldpath.xf,
         -- newmonotonizer(
                newcleaner(
                    newpath))) -- )
    newpath:close()
    return newpath
end

-- prepare scene for sampling and return modified scene
local function preparescene(scene)
	
	for k,e in ipairs(scene.elements) do
		e.paint.xf = scene.xf * e.paint.xf
		e.shape.xf = scene.xf * e.shape.xf
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

-- This is to get the x coordinates
-- works for vertical lines
local cx = {}
cx.get = function(a,p)
	return a[1],p[1]
end

-- This is to get the y coordinates
-- works for horizontal lines
local cy = {}
cy.get = function(a,p)
	return a[2],p[2]
end

local bt = {}
bt.get = function(u,v)
	return u > v
end

local bte = {}
bte.get = function(u,v)
	return u >= v
end

local lt = {}
lt.get = function(u,v)
	return u < v
end

local lte = {}
lte.get = function(u,v)
	return u <= v
end

-- coord: THis will be cx o cy
-- op: lt,lte,bt,bte
-- value = {xvalue,yvalue}
local function clip(coord,op,value,oldpath)
	local newpath = _M.path()
	newpath:open()
	local fx,fy -- the first point inside the path
	local px,py -- the last point added to the new path

	local iterator = {}
	function iterator:begin_closed_contour(len,x0,y0)
		if op.get(coord.get(value,{x0,y0})) then
			px, py = x0,y0
			fx, fy = x0,y0
		end
	end
	iterator:begin_open_contour = iterator:end_closed_contour
	function iterator:linear_segment(x0,y0,x1,y1)

	end

	function iterator:quadratic_segment(x0,y0,x1,y1,x2,y2)
	end

	function iterator:rational_quadratic_segment(x0,y0,x1,y1,w1,x2,y2)
	end

	function iterator:cubic_segment(x0,y0,x1,y1,x2,y2,x3,y3)
	end

	function iterator:end_closed_contour(len)
	end
	iterator:end_open_conutour = iterator:end_closed_contour

	oldpath:iterate(iterator)
	newpath:close()
	return newpath
end

-- override circle creation function and return a path instead
function _M.circle(cx, cy, r)
    -- we start with a unit circle centered at the origin
    -- it is formed by 3 arcs covering each third of the unit circle
    local s = 0.5           -- sin(pi/6)
    local c = 0.86602540378 -- cos(pi/6)
    local w = s
    return _M.path{
        _M.M,  0,  1,
        _M.R, -c,  s,  w, -c, -s,
        _M.R,  0, -1,  w,  c, -s,
        _M.R,  c,  s,  w,  0,  1,
        _M.Z
    -- transform it to the circle with given center and radius
    }:scale(r, r):translate(cx, cy)
end

-- override triangle creation and return a path instead
function _M.triangle(x1, y1, x2, y2, x3, y3)
	return _M.path{_M.M,x1,y1,_M.L,x2,y2,_M.L,x3,y3,_M.L,x1,y1,_M.Z}
end

-- override polygon creation and return a path instead
function _M.polygon(data)
	local newpath = _M.path()
	newpath:open()
	newpath:begin_closed_contour(_,data[1],data[2])
	local px,py = data[1],data[2]
	for i = 3, #data, 2 do 
		newpath:linear_segment(px,py,data[i],data[i+1])
		px,py = data[i],data[i+1]
	end
	newpath:linear_segment(px,py,data[1],data[2])
	newpath:close()
    return newpath
end

-- verifies that there is nothing unsupported in the scene
-- note that we only support paths!
-- triangles, circles, and polygons were overriden
local function checkscene(scene)
    for i, element in ipairs(scene.elements) do
        assert(element.type == "fill" or element.type == "eofill")
        assert(element.shape.type == "path", "unsuported primitive")
        assert(element.paint.type == "solid" or
               element.paint.type == "lineargradient" or
               element.paint.type == "radialgradient" or
               element.paint.type == "texture",
                    "unsupported paint")
    end
end

-- descend on quadtree, find leaf containing x,y, use leaf
-- to evaluate the color, and finally return r,g,b,a
local function sample(quadtree, xmin, ymin, xmax, ymax, x, y)
    -- implement
    return 0, 0, 0, 1
end

-- this returns an iterator that prints the methods called
-- and then forwards them on.
-- very useful for debugging!
local function newtap(name, forward)
    local newwrite = function(method)
        return function(self, ...)
            io.stderr:write(name, ":", method, "(")
            for i = 1, select("#", ...) do
                io.stderr:write(tostring(select(i, ...)), ",")
            end
            io.stderr:write(")\n")
            forward[method](forward, ...)
        end
    end
    return setmetatable({}, {
        __index = function(tap, index)
            local new = newwrite(index)
            tap[index] = new
            return new
        end
    })
end

-- clip scene against bounding-box and return a quadtree leaf
local function scenetoleaf(scene, xmin, ymin, xmax, ymax)
    -- implement
    return scene
end

-- recursively subdivides leaf to create the quadtree
function subdividescene(leaf, xmin, ymin, xmax, ymax, maxdepth, depth)
    -- implement
    depth = depth or 1

    return leaf
end

-- return smallest power of 2 larger than n
local function power2(n)
    n = floor(n)
    if n > 0 then
        n = n - 1
        n = bit32.bor(n, bit32.rshift(n, 1))
        n = bit32.bor(n, bit32.rshift(n, 2))
        n = bit32.bor(n, bit32.rshift(n, 4))
        n = bit32.bor(n, bit32.rshift(n, 8))
        n = bit32.bor(n, bit32.rshift(n, 16))
        n = n + 1
        return n
    else
        return 1
    end
end

-- adjust the viewport so that the width and the height are
-- the smallest powers of 2 that are large enough to
-- contain the viewport
local function adjustviewport(vxmin, vymin, vxmax, vymax)
    local width = max(power2(vxmax - vxmin), power2(vymax - vymin))
    return vxmin, vymin, vxmin+width, vymin+width
end

-- load your own svg driver here and use it for debugging!
local svg = dofile"svg.lua"

-- append lines marking the tree bounding box to the scene
local function appendbox(xmin, ymin, xmax, ymax, scene)
    -- implement
end

-- recursively append the lines marking cell divisions to the scene
local function appendtree(quadtree, xmin, ymin, xmax, ymax, scene)
    -- implement
end

local function dumpscenetree(quadtree, xmin, ymin, xmax, ymax,
            scene, viewport, output)
    appendbox(xmin, ymin, xmax, ymax, scene)
    appendtree(quadtree, xmin, ymin, xmax, ymax, scene)
    -- use your svg driver to dump contents to an SVG file
    svg.render(scene, viewport, output)
end

function _M.render(scene, viewport, output, arguments)
    local maxdepth = MAX_DEPTH
    local scenetree = false
    -- dump arguments
    if #arguments > 0 then stderr("driver arguments:\n") end
    for i, argument in ipairs(arguments) do
        stderr("  %d: %s\n", i, argument)
    end
    -- list of supported options
    -- you can add your own options as well
    local options = {
        { "^(%-maxdepth:(%d+)(.*))$", function(all, n, e)
            if not n then return false end
            assert(e == "", "invalid option " .. all)
            n = assert(tonumber(n), "invalid option " .. all)
            assert(n >= 1, "invalid option " .. all)
            maxdepth = math.floor(n)
            return true
        end },
        { "^%-scenetree$", function(d)
            if not d then return false end
            scenetree = true
            return true
        end },
        { ".*", function(all)
            error("unrecognized option " .. all)
        end }
    }
    -- process options
    for i, argument in ipairs(arguments) do
        for j, option in ipairs(options) do
            if option[2](argument:match(option[1])) then
                break
            end
        end
    end
    -- create timer
    local time = chronos.chronos()
    -- make sure scene does not contain any unsuported content
    checkscene(scene)
    -- prepare scene for rendering
    scene = preparescene(scene)
    -- get viewport
    local vxmin, vymin, vxmax, vymax = unpack(viewport, 1, 4)
    -- get image width and height from viewport
    local width, height = vxmax-vxmin, vymax-vymin
    -- build quadtree for scene
    local qxmin, qymin, qxmax, qymax =
        adjustviewport(vxmin, vymin, vxmax, vymax)
    local quadtree = subdividescene(
        scenetoleaf(scene, vxmin, vymin, vxmax, vymax),
        qxmin, qymin, qxmax, qymax, maxdepth)
    stderr("preprocess in %.3fs\n", time:elapsed())
    time:reset()
    if scenetree then
        -- dump tree on top of scene as svg into output
        dumpscenetree(quadtree, qxmin, qymin, qxmax, qymax,
            scene, viewport, output)
        output:flush()
        stderr("scene quadtree dump in %.3fs\n", time:elapsed())
        os.exit()
    end
    -- allocate output image
    local outputimage = image.image(width, height)
    -- render
    for i = 1, height do
        stderr("\r%d%%", floor(1000*i/height)/10)
        for j = 1, width do
            local x, y = vxmin+j-.5, vymin+i-5
            local r, g, b, a = sample(quadtree,
                qxmin, qymin, qxmax, qymax, x, y)
            outputimage:set(j, i, r, g, b, a)
        end
    end
    stderr("\n")
    stderr("rendering in %.3fs\n", time:elapsed())
    time:reset()
    -- store output image
    image.png.store8(output, outputimage)
    stderr("saved in %.3fs\n", time:elapsed())
end


return _M
