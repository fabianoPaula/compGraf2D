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


local function recursivebisectline(x0, x1, ta, tb, n)
    local tm = 0.5*(ta+tb)
    local xm = lerp(x0, x1, tm)
    if abs(xm) < TOL or n >= MAX_ITER then
        return tm
    else
        n = n + 1
        if xm < 0 then ta = tm
        else tb = tm end
        -- tail call
        return recursivebisectline(x0, x1, ta, tb, n)
    end
end
-- assumes monotonic and root in [0, 1]
local function bisectline( x0 , x1 )
    assert(x1*x0 <= 0, "no root in interval!")
    if x0 > x1 then
        return 1-recursivebisectline(x1, x0, 0, 1, 0)
    else
        return recursivebisectline(x0, x1, 0, 1, 0)
    end
end

local function recursivebisectquadratic(x0, x1, x2, ta, tb, n)
    local tm = 0.5*(ta+tb)
    local xm = lerp2(x0, x1, x2, tm, tm)
    if abs(xm) < TOL or n >= MAX_ITER then
        return tm
    else
        n = n + 1
        if xm < 0 then ta = tm
        else tb = tm end
        -- tail call
        return recursivebisectquadratic(x0, x1, x2, ta, tb, n)
    end
end

-- assumes monotonic and root in [0, 1]
local function bisectquadratic( x0 , x1 , x2 )
    assert(x2*x0 <= 0, "no root in interval!")
    if x0 > x2 then
        return 1-recursivebisectquadratic(x2 , x1, x0, 0, 1, 0)
    else
        return recursivebisectquadratic(x0, x1, x2, 0, 1, 0)
    end
end

local function recursivebisectcubic(x0, x1, x2, x3, ta, tb, n)
    local tm = 0.5*(ta+tb)
    local xm = lerp3(x0, x1, x2, x3 , tm, tm, tm)
    if abs(xm) < TOL or n >= MAX_ITER then
        return tm
    else
        n = n + 1
        if xm < 0 then ta = tm
        else tb = tm end
        -- tail call
        return recursivebisectcubic(x0, x1, x2, x3, ta, tb, n)
    end
end
-- assumes monotonic and root in [0, 1]
local function bisectcubic( x0 , x1 , x2 , x3 )
    assert(x3*x0 <= 0, "no root in interval!")
   if x0 > x3 then
        return 1-recursivebisectcubic(x3, x2, x1, x0, 0, 1, 0)
    else
        return recursivebisectcubic(x0, x1, x2, x3, 0, 1, 0)
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

--retorna a tragetória dividida em segmentos monotônicos
local function newmonotonizer(forward)
    local monotonizer = {}
    function monotonizer:begin_closed_contour(len, x0, y0)
        forward:begin_closed_contour(_, x0, y0)
    end
    monotonizer.begin_open_contour = monotonizer.begin_closed_contour
    function monotonizer:linear_segment(x0, y0, x1, y1)
        forward:linear_segment(px, py, x1, y1) -- o segmento linear não precisa ser monotonizado
    end
    function monotonizer:quadratic_segment(x0, y0, x1, y1, x2, y2)
        --descobre as raízes de x'(t) e y'(t) ordena os t's e usa lerp2 pra descobrir os pontos de controle          
        local t = { 0 } -- valores de t para os pontos que representam os segmentos monotônicos 
        local Qx = {} -- vetor da coordenada x dos novos pontos de controle
        local Qy = {} -- vetor da coordenada y dos novos pontos de controle
    
        if ( x0 + x2 ~= 2*x1 ) then
            -- caso a raiz não caia no intervalo [0,1], o resultado não nos interessa
            if ( (x0 - x1)/(x0 - 2*x1 + x2) < 1 and (x0 - x1)/(x0 - 2*x1 + x2) > 0 ) then 
                t[#t + 1] =  (x0 - x1)/(x0 - 2*x1 + x2)--raiz de x'(t) = 0
            end
            
        end
        if ( y0 + y2 ~= 2*y1 ) then
            -- caso a raiz não caia no intervalo [0,1], o resultado não nos interessa
            if ( (y0 - y1)/(y0 - 2*y1 + y2) < 1 and (y0 - y1)/(y0 - 2*y1 + y2) > 0 ) then 
                t[#t + 1] =  (y0 - y1)/(y0 - 2*y1 + y2)--raiz de y'(t) = 0
            end
        end

        t[#t + 1] = 1
        --coloca os t's em ordem crescente ( Quick Sort)
        t = table.sort(t, quicksort)
        Qx[1] = x0
        Qy[1] = y0
        for i = 1, #t - 1  do
            Qx[#Qx + 1] = lerp2(x0,x1,x2,x3,t[i],t[i+1])
            Qx[#Qx + 1] = lerp2(x0,x1,x2,x3,t[i+1],t[i+1])
            
            Qy[#Qy + 1] = lerp2(y0,y1,y2,y3,t[i],t[i],t[i+1])
            Qy[#Qy + 1] = lerp2(y0,y1,y2,y3,t[i],t[i+1],t[i+1])

            --já pode dar o foward do quadratic segment pra esses 2 junto com o anterior
            forward:quadratic_segment(Qx[#Qx - 2], Qy[#Qy - 2], Qx[#Qx - 1], Qy[#Qy - 1], Qx[#Qx], Qy[#Qy])
        end
   end
    function monotonizer:rational_quadratic_segment(x0, y0, x1, y1, w1, x2, y2)
        forward:rational_quadratic_segment(x0, y0, x1, y1, w1, x2, y2)
        forward:rational_quadratic_segment(x0, y0, x1, y1, w1, x2, y2)
    end
    function monotonizer:cubic_segment(x0, y0, x1, y1, x2, y2, x3, y3)
        -- raciocínio análogo ao quadratic_segment
        local t = { 0 } -- valores de t para os pontos que representam os segmentos monotônicos 
        local Qx = {} -- vetor da coordenada x dos novos pontos de controle
        local Qy = {} -- vetor da coordenada y dos novos pontos de controle
        local solution
        local t1, s1 , t2 , s2
         solution , t1 , s1 , t2 , s2 = quadratic.quadratic( x3 - 3*x2 + 3*x1 - x0 , 2*x2 - 4*x1 + 2*x0 , x1 - x0 )
         if ( solution == 2 ) then
            if ( t1/s1 > 0 and t1/s1 < 1 )  then
                t[#t + 1] = t1/s1
            end 
            if ( t2/s2 > 0 and t2/s2 < 1 and t2/s2 ~= t1/s1)  then
                t[#t + 1] = t2/s2
            end 
         end

         solution , t1 , s1 , t2 , s2 = quadratic.quadratic( y3 - 3*y2 + 3*y1 - y0 , 2*y2 - 4*y1 + 2*y0 , y1 - y0 )
         if ( solution == 2) then
            if ( t1/s1 > 0 and t1/s1 < 1 )  then
                t[#t + 1] = t1/s1
            end 
            if (  t2/s2 > 0 and t2/s2 < 1 and t2/s2 ~= t1/s1 )  then
                t[#t + 1] = t2/s2
            end 
         end
         t[#t + 1] = 1
        --coloca os t's em ordem crescente ( Quick Sort)
        t = table.sort(t, quicksort)
        Qx[1] = x0
        Qy[1] = y0
        for i = 1, #t - 1  do
            Qx[#Qx + 1] = lerp3(x0,x1,x2,x3,t[i],t[i],t[i+1])
            Qx[#Qx + 1] = lerp3(x0,x1,x2,x3,t[i],t[i+1],t[i+1])
            Qx[#Qx + 1] = lerp3(x0,x1,x2,x3,t[i+1],t[i+1],t[i+1])

            Qy[#Qy + 1] = lerp3(y0,y1,y2,y3,t[i],t[i],t[i+1])
            Qy[#Qy + 1] = lerp3(y0,y1,y2,y3,t[i],t[i+1],t[i+1])
            Qy[#Qy + 1] = lerp3(y0,y1,y2,y3,t[i+1],t[i+1],t[i+1])

            --já pode dar o foward do cubic segment pra esses 3 junto com o anterior
            forward:cubic_segment(Qx[#Qx - 3], Qy[#Qy - 3], Qx[#Qx - 2], Qy[#Qy - 2], Qx[#Qx - 1], Qy[#Qy - 1], Qx[#Qx], Qy[#Qy])
        end
    end
    function cleaner:end_closed_contour(len)
        forward:end_closed_contour(_)
    end
    monotonizer.end_open_contour = monotonizer.end_closed_contour
    return monotonizer
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
          newmonotonizer(
                newcleaner(
                    newpath)))  )
    newpath:close()
    return newpath
end

-- prepare scene for sampling and return modified scene
local function preparescene(scene)
    local newscene = _M.scene()
    --itera sobre a scena tranformando tudo em path
    --itera sobre cada path, transpormando seus elementos em segmentos monotônicos, transformados e não-degenerados 
    return newscene
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
