local driver  = require"driver"
local image   = require"image"
local chronos = require"chronos"

local element   = require"element"
local xform     = require"xform"
local sc        = require"scene"
local quadratic = require"quadratic"
local cubic     = require"cubic"

local sqrt   = math.sqrt
local min    = math.min
local max    = math.max
local unpack = table.unpack
local floor  = math.floor
local abs    = math.abs
local deg    = math.deg
local atan2  = math.atan2
local inf    = math.huge
local pow    = math.pow

-- output formatted string to stderr
local function stderr(...)
    io.stderr:write(string.format(...))
end

local FLT_MIN = 1.17549435E-38 -- smallest-magnitude normalized single-precision
local TOL = 0.01 -- root-finding tolerance, in pixels
local MAX_ITER = 30 -- maximum number of bisection iterations in root-finding
local MAX_DEPTH = 5 -- maximum quadtree depth
local MIN_SEGS = 11 -- minimun of segments in every leaf
local GAMMA_APPLY = 1 -- gamma quantity
local tx,ty = 0,0 --params for translate the scene
local sx,sy = 1,1 --params for scale the scene

local _M = driver.new()


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
	newpath:end_closed_contour(_)
	newpath:close()
    return newpath
end

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

local function linear_coefficients(x0,x1)
	return x1 - x0,x0
end

local function quadratic_coefficients(x0,x1,x2)
	return (x0 - 2*x1 + x2), 2*(x1-x0), x0
end

local function cubic_coefficients(x0,x1,x2,x3)
	return (x3+3*x1-3*x2-x0), 3*(x0-2*x1+x2), 3*(x1-x0), x0
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

-- cut quadratic segment and recanonize
local function cut2s(a, b, x0, y0, x1, y1, x2, y2)
	-- P0
    local u0 = lerp2(x0, x1, x2, a, a)
    local v0 = lerp2(y0, y1, y2, a, a)
	-- P1
    local u1 = lerp2(x0, x1, x2, a, b)
    local v1 = lerp2(y0, y1, y2, a, b)
	-- P2
    local u2 = lerp2(x0, x1, x2, b, b)
    local v2 = lerp2(y0, y1, y2, b, b)
    return u0, v0, u1, v1, u2, v2
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
        forward:end_closed_contour(len)
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
        forward:linear_segment(px, py, x1, y1) 
    end
    function monotonizer:quadratic_segment(x0, y0, x1, y1, x2, y2)
        local t = { 0,1 }  
    
        if ( x0 + x2 ~= 2*x1 ) then
            -- caso a raiz não caia no intervalo [0,1],
			-- o resultado não nos interessa
            if ( (x0 - x1)/(x0 - 2*x1 + x2) < 1 
				and (x0 - x1)/(x0 - 2*x1 + x2) > 0 ) then 
                t[#t + 1] =  (x0 - x1)/(x0 - 2*x1 + x2)--raiz de x'(t) = 0
            end
            
        end
        if ( y0 + y2 ~= 2*y1 ) then
            -- caso a raiz não caia no intervalo [0,1],
			-- o resultado não nos interessa
            if ( (y0 - y1)/(y0 - 2*y1 + y2) < 1 
				and (y0 - y1)/(y0 - 2*y1 + y2) > 0 ) then 
                t[#t + 1] =  (y0 - y1)/(y0 - 2*y1 + y2)--raiz de y'(t) = 0
            end
        end

        table.sort(t, quicksort)
        for i = 1, (#t - 1)  do
            forward:quadratic_segment(cut2s(t[i],t[i+1],x0,y0,x1,y1,x2,y2))
        end
   end
    function monotonizer:rational_quadratic_segment(x0, y0, x1, y1, w1, x2, y2)
		local r = {0,1}

		local a,b,c = quadratic_coefficients(y0,y1,y2)
		local d,e,f = quadratic_coefficients(1,w1,1) 
		local  dca, dcb, dcc = (a*e - b*d), 2*(a*f-c*d), b*f - c*e

		local root = {quadratic.quadratic(dca,dcb,dcc)}
		if root[1] == 2 then
			for i = 2,4,2 do
				local t = root[i]/root[i+1]
				if t > 0 and t < 1 then
					table.insert(r,t)
				end
			end
		end


		local a,b,c = quadratic_coefficients(x0,x1,x2)
		local d,e,f = quadratic_coefficients(1,w1,1) 
		local  dca, dcb, dcc = (a*e - b*d), 2*(a*f-c*d), b*f - c*e

		local root = {quadratic.quadratic(dca,dcb,dcc)}
		if root[1] == 2 then
			for i = 2,4,2 do
				local t = root[i]/root[i+1]
				if t > 0 and t < 1 then
					table.insert(r,t)
				end
			end
		end

		table.sort(r,quicksort)
		for i = 1, #r - 1 do
			 forward:rational_quadratic_segment(
				 cutr2s(r[i],r[i+1],x0,y0,x1,y1,w1,x2,y2)
				 )
		 end
    end
    function monotonizer:cubic_segment(x0, y0, x1, y1, x2, y2, x3, y3)

        -- raciocínio análogo ao quadratic_segment
        local t = { 0 }  
        local Qx = {} -- vetor da coordenada x dos novos pontos de controle
        local Qy = {} -- vetor da coordenada y dos novos pontos de controle
        local solution,t1,s1 , t2 , s2
         solution , t1 , s1 , t2 , s2 = quadratic.quadratic( 
		 	x3 - 3*x2 + 3*x1 - x0 , 2*x2 - 4*x1 + 2*x0 , x1 - x0 )
         if ( solution == 2 ) then
            if ( t1/s1 > 0 and t1/s1 < 1 )  then
                t[#t + 1] = t1/s1
            end 
            if ( t2/s2 > 0 and t2/s2 < 1 and t2/s2 ~= t1/s1)  then
                t[#t + 1] = t2/s2
            end 
         end

         solution , t1 , s1 , t2 , s2 = quadratic.quadratic( 
		 	y3 - 3*y2 + 3*y1 - y0 , 2*y2 - 4*y1 + 2*y0 , y1 - y0 )
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
        table.sort(t, quicksort)
        Qx[1] = x0
        Qy[1] = y0
        for i = 1, #t - 1  do
            Qx[#Qx + 1] = lerp3(x0,x1,x2,x3,t[i],t[i],t[i+1])
            Qx[#Qx + 1] = lerp3(x0,x1,x2,x3,t[i],t[i+1],t[i+1])
            Qx[#Qx + 1] = lerp3(x0,x1,x2,x3,t[i+1],t[i+1],t[i+1])

            Qy[#Qy + 1] = lerp3(y0,y1,y2,y3,t[i],t[i],t[i+1])
            Qy[#Qy + 1] = lerp3(y0,y1,y2,y3,t[i],t[i+1],t[i+1])
            Qy[#Qy + 1] = lerp3(y0,y1,y2,y3,t[i+1],t[i+1],t[i+1])

            --já pode dar o foward do cubic segment pra esses 
			--3 junto com o anterior
            forward:cubic_segment(Qx[#Qx - 3], Qy[#Qy - 3], Qx[#Qx - 2], Qy[#Qy - 2], Qx[#Qx - 1], Qy[#Qy - 1], Qx[#Qx], Qy[#Qy])
        end
    end
    function monotonizer:end_closed_contour(len)
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

-- c liping function
local function cx(x,y) return x end -- To get the x coordinate
local function cy(x,y) return y end -- To get the y coordinate
local function bt(u,v)  return u > v  end
local function bte(u,v) return u >= v end
local function lt(u,v) 	return u < v  end
local function lte(u,v) return u <= v end

local function cubic_intersection(x0,x1,x2,x3,w)
	return bisectcubic(x0 - w, x1 -w, x2 -w,x3 -w)
end

-- c(Cooridinate): this will be cx o cy
-- o: lt,lte,bt,bte
-- value = {xvalue,yvalue}
local function clip(c,op,value,forward)
	local x,y = unpack(value)
	local fx,fy = nil,nil -- the first point inside the path
	local px,py -- the last point added to the new path

	local iterator = {}
	function iterator:begin_closed_contour(len,x0,y0)
		if op(c(x0,y0),c(x,y)) then
			px, py,fx,fy = x0,y0,x0,y0
			forward:begin_closed_contour(_,x0,y0)
		end
	end
	iterator.begin_open_contour = iterator.begin_closed_contour
	function iterator:linear_segment(x0,y0,x1,y1)
		if op(c(x0,y0),c(x,y))and op(c(x1,y1),c(x,y)) then
			if fx == nil then
				fx, fy = x0,y0
				forward:begin_closed_contour(_,fx,fy)
			end
			forward:linear_segment(x0,y0,x1,y1)
			px,py = x1,y1
		elseif not op(c(x0,y0),c(x,y)) and op(c(x1,y1),c(x,y)) then
			local t = bisectline(c(x0,y0) - c(x,y),c(x1,y1) - c(x,y))
			local px0 = lerp(x0,x1,t)
			local py0 = lerp(y0,y1,t)
			if fx == nil then
				fx, fy = px0,py0
				forward:begin_closed_contour(_,fx,fy)
			else
				forward:linear_segment(px,py,px0,py0)
			end
			forward:linear_segment(px0,py0,x1,y1)
			px,py = x1,y1
		elseif op(c(x0,y0),c(x,y)) and not op(c(x1,y1),c(x,y)) then
			if fx == nil then
				fx, fy = x0,y0
				forward:begin_closed_contour(_,fx,fy)
			end
			local t = bisectline(c(x0,y0) - c(x,y),c(x1,y1) - c(x,y))
			local px1 = lerp(x0,x1,t)
			local py1 = lerp(y0,y1,t)
			forward:linear_segment(x0,y0,px1,py1)
			px,py = px1,py1
		end
	end

	function iterator:quadratic_segment(x0,y0,x1,y1,x2,y2)
		if op(c(x0,y0),c(x,y)) and op(c(x2,y2),c(x,y)) then
			if fx == nil then
				fx, fy = x0,y0
				forward:begin_closed_contour(_,fx,fy)
			end
			forward:quadratic_segment(x0,y0,x1,y1,x2,y2)
			px,py = x2,y2
		elseif not op(c(x0,y0),c(x,y)) and op(c(x2,y2),c(x,y)) then
			local t = bisectquadratic(c(x0,y0) - c(x,y),
				c(x1,y1) - c(x,y),c(x2,y2) - c(x,y))
			local px0,py0,px1,py1 = cut2s(t,1,x0,y0,x1,y1,x2,y2)
			if fx == nil then
				fx, fy = px0,py0
				forward:begin_closed_contour(_,fx,fy)
			else 
				forward:linear_segment(px,py,px0,py0) 
			end
			forward:quadratic_segment(px0,py0,px1,py1,x2,y2)
			px,py = x2,y2
		elseif op(c(x0,y0),c(x,y)) and not op(c(x2,y2),c(x,y)) then
			if fx == nil then
				fx, fy = x0,y0
				forward:begin_closed_contour(_,fx,fy)
			end
			local t = bisectquadratic(c(x0,y0) - c(x,y),c(x1,y1) - c(x,y),c(x2,y2) - c(x,y))
			local px0,py0,px1,py1,px2,py2 = cut2s(0,t,x0,y0,x1,y1,x2,y2)
			forward:quadratic_segment(x0,y0,px1,py1,px2,py2)
			px,py = px2,py2
		end
	end

	function iterator:rational_quadratic_segment(x0,y0,x1,y1,w1,x2,y2)
		if op(c(x0,y0),c(x,y)) and op(c(x2,y2),c(x,y)) then
			if fx == nil then
				fx, fy = x0,y0
				forward:begin_closed_contour(_,fx,fy)
			end
			forward:rational_quadratic_segment(x0,y0,x1,y1,w1,x2,y2)
			px,py = x2,y2
		elseif not op(c(x0,y0),c(x,y)) and op(c(x2,y2),c(x,y)) then
			local t = bisectrationalquadratic(c(x0,y0) -c(x,y),
				c(x1,y1) - w1*c(x,y),w1,
				c(x2,y2) - c(x,y)) 
			local px0,py0,px1,py1,pw1,px2,py2 = cutr2s(t,1,x0,y0,x1,y1,w1,x2,y2)
			if fx == nil then
				fx, fy = px0,py0
				forward:begin_closed_contour(_,fx,fy)
			else 
				forward:linear_segment(px,py,px0,py0) 
			end
			forward:rational_quadratic_segment(px0,py0,px1,py1,pw1,x2,y2)
			px,py = x2,y2
		elseif op(c(x0,y0),c(x,y)) and not op(c(x2,y2),c(x,y)) then
			local t = bisectrationalquadratic(c(x0,y0) -c(x,y),
				c(x1,y1) - w1*c(x,y),w1,
				c(x2,y2) - c(x,y)) 
			if fx == nil then
				fx, fy = x0,y0
				forward:begin_closed_contour(_,fx,fy)
			end
			local px0,py0,px1,py1,pw1,px2,py2 = cutr2s(0,t,x0,y0,x1,y1,w1,x2,y2)
			forward:rational_quadratic_segment(x0,y0,px1,py1,pw1,px2,py2)
			px,py = px2,py2
		end
	end

	function iterator:cubic_segment(x0,y0,x1,y1,x2,y2,x3,y3)
		if op(c(x0,y0),c(x,y)) 	and op(c(x3,y3),c(x,y)) then
			if fx == nil then
				fx, fy = x0,y0
				forward:begin_closed_contour(_,fx,fy)
			end
			forward:cubic_segment(x0,y0,x1,y1,x2,y2,x3,y3)
			px,py = x3,y3
		elseif not op(c(x0,y0),c(x,y)) and op(c(x3,y3),c(x,y)) then

			local t = cubic_intersection(c(x0,y0),c(x1,y1),c(x2,y2),c(x3,y3),c(x,y))

			local px0 = lerp3(x0,x1,x2,x3,t,t,t)
			local py0 = lerp3(y0,y1,y2,y3,t,t,t)
			if fx == nil then
				fx, fy = px0,py0
				forward:begin_closed_contour(_,fx,fy)
			else 
				forward:linear_segment(px,py,px0,py0) 
			end

			local px1 = lerp3(x0,x1,x2,x3,t,t,1)
			local py1 = lerp3(y0,y1,y2,y3,t,t,1)

			local px2 = lerp3(x0,x1,x2,x3,t,1,1)
			local py2 = lerp3(y0,y1,y2,y3,t,1,1)

			forward:cubic_segment(px0,py0,px1,py1,px2,py2,x3,y3)
			px,py = x3,y3
		elseif op(c(x0,y0),c(x,y)) and not op(c(x3,y3),c(x,y)) then
			if fx == nil then
				fx, fy = x0,y0
				forward:begin_closed_contour(_,fx,fy)
			end

			local t = cubic_intersection(c(x0,y0),c(x1,y1),c(x2,y2),c(x3,y3),c(x,y))

			local px1 = lerp3(x0,x1,x2,x3,0,0,t)
			local py1 = lerp3(y0,y1,y2,y3,0,0,t)

			local px2 = lerp3(x0,x1,x2,x3,0,t,t)
			local py2 = lerp3(y0,y1,y2,y3,0,t,t)

			local px3 = lerp3(x0,x1,x2,x3,t,t,t)
			local py3 = lerp3(y0,y1,y2,y3,t,t,t)

			forward:cubic_segment(x0,x0,px1,py1,px2,py2,px3,py3)
			px,py = px3,py3
		end
	end

	function iterator:end_closed_contour(len)
		if fx then
			if px ~= fx or py ~= fy then forward:linear_segment(px,py,fx,fy) end
			forward:end_closed_contour(_)
			fx,fy = nil,nil
		end
	end
	iterator.end_open_contour = iterator.end_closed_contour
	return iterator
end

local function clippath(c,o,value,oldpath)
	local newpath = _M.path()
	newpath:open()
	oldpath:iterate(
		clip(c,o,value,newcleaner(newpath))
	)
	newpath:close()
	return newpath
end

local prepare = {}

function prepare.alpha(r,g,b,a)
--	r,g,b = a*r, a*g, a*b
	return r, g , b, a 
end

function prepare.solid(paint)
	local r,g,b,a = unpack(paint.data)
	paint.data = {prepare.alpha(r,g,b,a)}
	return paint
end

function prepare.ramp(ramp)
	for i = 2,#ramp,2 do
		local r,g,b,a = unpack(ramp[i])
		ramp[i] = {prepare.alpha(r,g,b,a)}
	end
end

function prepare.lineargradient(paint)
	local data = paint.data
	local tp1 = xform.translate(unpack(data.p1)):inverse()
	data.tp2 = {tp1:apply(unpack(data.p2))}
	local degree = deg(atan2(data.tp2[2],data.tp2[1]))
	local rot = xform.rotate(-degree)
	-- rotate p2 to be in the x-axis
	data.tp2 = {rot:apply(unpack(data.tp2))}
	local scale = xform.identity()
	if data.tp2[1] > FLT_MIN then scale = xform.scale(1/data.tp2[1],1) end
	paint.xfs = scale*rot*tp1*paint.xfs:inverse()

	prepare.ramp(paint.data.ramp)
	return paint
end

function prepare.radialgradient(paint)
	local data = paint.data
	local center = data.center
	local r = data.radius
	-- use implicity representation
	local a,b,f,g = 1,1,-center[2],-center[1]
	local c = center[1]*center[1] + center[2]*center[2] - r*r
	paint.circle = xform.xform(a,0,g, 0,b,f, g,f,c)
	-- translate the focus to the origin
	local tfocus = xform.translate(unpack(data.focus)):inverse()
	-- translate the focus to the origin, center and the circle
	data.tcenter = {tfocus:apply(unpack(data.center))}
	paint.circle = tfocus:inverse():transpose() * paint.circle * tfocus:inverse() 
	local degree = deg(atan2(data.tcenter[2],data.tcenter[1]))
	local rot = xform.rotate(-degree)
	data.tcenter = {rot:apply(unpack(data.tcenter))}
	paint.circle = rot:inverse():transpose() * paint.circle * rot:inverse() 
	
	local tscale = xform.identity()
	 paint.circlexCenter = 0 
	if (data.tcenter[1] ~= 0) then 
		tscale = xform.scale(1/data.tcenter[1])
		paint.circlexCenter = 1
	end
	data.tcenter = {tscale:apply(unpack(data.tcenter))}
	paint.circle = tscale:inverse():transpose() * paint.circle * tscale:inverse() 
	paint.circleRadius = abs(paint.circle[3+6]/paint.circle[1] - 1)
	paint.xfs = rot * tscale * tfocus * paint.xfs:inverse()

	prepare.ramp(paint.data.ramp,paint.opacity)
	return paint 
end


-- prepare scene for sampling and return modified scene
local function preparescene(scene)
	for k,e in ipairs(scene.elements) do
		e.paint.xfs = scene.xf * e.paint.xf
	end
	for i = 1,#scene.elements do
		local e = scene.elements[i]

		e.shape = transformpath(e.shape,scene.xf)
		local preparecallback = assert(prepare[e.paint.type],
				"no handler for " ..e.paint.type)

		e.paint = preparecallback(e.paint)
	end
	return scene
end

local colour = {}

function colour.opacity(o,r,g,b,a)
	return r, g, b, a*o
end

function colour.solid(paint,p)
	return colour.opacity(paint.opacity,unpack(paint.data))
end

function colour.normalizegradient(x)
	if x > 1 then 
		return 1
	elseif x < 0 then 
		return 0 
	end
	return abs(x)
end

function colour.lineargradient(paint,p)
	local x,y,w = paint.xfs:apply(p[1],p[2])
	local result  = colour.normalizegradient(x)
	return colour.opacity(paint.opacity,ajusttoramp(paint.data.ramp,result))
end

function colour.radialgradient(paint,p)
	local x,y,w = paint.xfs:apply(p[1],p[2])
	local a = x*x + y*y
	local b = -2*x
	local c = paint.circlexCenter - paint.circleRadius
	local root = {quadratic.quadratic(a,b,c)}
	local result = colour.normalizegradient(root[3]/root[2])
	return colour.opacity(paint.opacity,ajusttoramp(paint.data.ramp,result))
end

function colour.composecolor(color,ncolor)
	local r, g, b, a = unpack(color)
	local nr, ng, nb, alpha = unpack(ncolor)

	r = lerp(r,nr,alpha)
	g = lerp(g,ng,alpha)
	b = lerp(b,nb,alpha)

	return {r,g,b,a}
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

local function insidenode(e,x,y)
	return (e.xmin <= x)and(e.xmax >= x)and(e.ymax >= y)and(e.ymin <= y)
end

local function nextnode(quadtree,x,y)
	if quadtree.children then
		for i,e in pairs(quadtree.children) do
			if insidenode(e,x,y) then return e end
		end
	end
	return nil
end

local function bb(xmin,ymin,xmax,ymax,p)
	return (xmax >= p[1])and(ymax > p[2])and(ymin <= p[2])
end


local function path(path, p)
	local winding = 0
    local iterator = {}
	function iterator:begin_open_contour(len, x0, y0) end
    function iterator:begin_closed_contour(len, x0, y0) end
    function iterator:linear_segment(x0, y0, x1, y1)
		if not bb(min(x0,x1),min(y0,y1),max(x0,x1),max(y0,y1),p) then return end
		local t = bisectline(y0-p[2],y1 - p[2])
		if p[1] < lerp(x0,x1,t)then
			winding = winding + sign(y1-y0)
		end
    end
    function iterator:quadratic_segment(x0, y0, x1, y1, x2, y2)
		if not bb(min(x0,x2),min(y0,y2),max(x0,x2),max(y0,y2),p) then return end
		local t = bisectquadratic(y0 - p[2], y1 - p[2], y2 - p[2])
		if p[1] < lerp2(x0,x1,x2,t,t) then
			winding = winding + sign(y2 - y0)
		end
	end
    function iterator:rational_quadratic_segment(x0, y0, x1, y1, w1, x2, y2)
		if not bb(min(x0,x2),min(y0,y2),max(x0,x2),max(y0,y2),p) then return end
		local t = bisectrationalquadratic(y0-p[2],y1 - w1*p[2],w1,y2-p[2])
		if lerp2(1,w1,1,t,t)*p[1] < lerp2(x0,x1,x2,t,t) then
			winding = winding + sign(y2- y0)
		end
    end
    function iterator:cubic_segment(x0, y0, x1, y1, x2, y2, x3, y3)
		if not bb(min(x0,x3),min(y0,y3),max(x0,x3),max(y0,y3),p) then return end
		local a,b,c,d = cubic_coefficients(y0,y1,y2,y3)
		local root = {cubic.cubic(a,b,c,d -  p[2])}
		for i = 2,#root-1,2 do
			local t = root[i]/root[i+1]
			if t >= 0 and t < 1 then
				if p[1] < lerp3(x0,x1,x2,x3,t,t,t)then
					winding = winding + sign(y3-y0)
				end
			end
		end
    end
    function iterator:end_open_contour(len) end
    function iterator:end_closed_contour(len) end
   	path:iterate(iterator)
	return winding 
end

local function shapecallback(element,p)
	local result = path(element.shape,p)
	if element.type == 'fill' then
		return (result ~=0)
	elseif element.type == 'eofill' then
		return (result % 2 == 1)
	end
end

-- descend on quadtree, find leaf containing x,y, use leaf
-- to evaluate the color, and finally return r,g,b,a
local function sample(quadtree, xmin, ymin, xmax, ymax, x, y)
	local child = quadtree
	local parent = nil
	while child do 
		parent = child 
		child = nextnode(child,x,y)
	end

	local p,color,ncolor = {x,y},{1,1,1,1}, {}
	if not parent.scene then return unpack(color) end
	for k,e in pairs(parent.scene.elements) do 
		if shapecallback(e,p) then 
			local paintcallback = assert(colour[e.paint.type],
				"no handler for " ..e.paint.type)
				
			ncolor = {paintcallback(e.paint,p) }
			color = colour.composecolor(color,ncolor)
		end
	end
    return unpack(color)
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
-- the smallest powrs of 2 that are large enough to
-- contain the viewport
local function adjustviewport(vxmin, vymin, vxmax, vymax)
    local width = max(power2(vxmax - vxmin), power2(vymax - vymin))
    return vxmin, vymin, vxmin+width, vymin+width
end

-- clip scene against bounding-box and return a quadtree leaf
local function scenetoleaf(scene, xmin, ymin, xmax, ymax)
	local leaf = {}
	leaf.scene = scene
	leaf.xmin = xmin
	leaf.xmax = xmax
	leaf.ymin = ymin
	leaf.ymax = ymax
    return leaf
end

local function clipbox(xmin,ymin,xmax,ymax,oldpath)
	local shape = clippath(cx,bt,{xmin,ymin},oldpath)
	shape = clippath(cy,bt,{xmin,ymin},shape)
	shape = clippath(cx,lt,{xmax,ymax},shape)
	shape = clippath(cy,lt,{xmax,ymax},shape)
	return shape
end

local function segmentnumber(scene)
	local sum = 0 
	for i,e in pairs(scene.elements) do sum = sum + e.shape.data[1] end
	return sum
end

local function clipscene(xmin,ymin,xmax,ymax,scene)
	xmin = xmin - 0.1
	xmax = xmax + 0.1
	ymin = ymin - 0.1
	ymax = ymax + 0.1
	local newelements = { }
	local shape 
	for i,e in pairs(scene.elements) do 
		shape = clipbox(xmin,ymin,xmax,ymax,e.shape)
		if #shape.instructions > 1 then 
			newelements[#newelements + 1] = element.fill(shape,e.paint)
		end
	end
	return sc.scene(newelements)
end


-- recursively subdivides leaf to create the quadtree
function subdividescene(leaf, xmin, ymin, xmax, ymax, maxdepth, depth)
    depth = depth or 1
	leaf.depth = depth
	if depth == maxdepth then return leaf end
	if segmentnumber(leaf.scene) < MIN_SEGS then return leaf end

	local xm,ym = (xmax+xmin)/2,(ymax+ymin)/2
	local lefttop     = clipscene(xmin,ym,xm,ymax,leaf.scene)
	local righttop    = clipscene(xm,ym,xmax,ymax,leaf.scene)
	local leftbottom  = clipscene(xmin,ymin,xm,ym,leaf.scene)
	local rightbottom = clipscene(xm,ymin,xmax,ym,leaf.scene)

	leaf.children = {
		subdividescene(scenetoleaf(lefttop,xmin,ym,xm,ymax),
			xmin,ym,xm,ymax,maxdepth,depth+1),
		subdividescene(scenetoleaf(righttop,xm,ym,xmax,ymax),
			xm,ym,xmax,ymax,maxdepth,depth+1),
		subdividescene(scenetoleaf(leftbottom,xmin,ymin,xm,ym),
			xmin,ymin,xm,ym,maxdepth,depth+1),
		subdividescene(scenetoleaf(rightbottom,xm,ymin,xmax,ym),
			xm,ymin,xmax,ym,maxdepth,depth+1),
	}
	leaf.scene = nil
    return leaf
end

local svg = dofile"scenetree.lua"

local function dumpscenetree(quadtree, xmin, ymin, xmax, ymax,
            scene, viewport, output)
	if quadtree.depth == 1 then svg.open(viewport) end
	if quadtree.children == nil then
		local viewport = {xmin,ymin,xmax,ymax}
		svg.render(quadtree.scene,viewport)
	else
		if quadtree.children ~= nil then
			for i,e in pairs(quadtree.children) do
				dumpscenetree(e,e.xmin,e.ymin,e.xmax,e.ymax,scene,viewport,output)
			end
		end
	end
	if quadtree.depth == 1 then svg.close(output) end 
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
        { "^(%-p:(%d+)(.*))$", function(all, n, e)
			if not n then return false end
			local aux = assert(tonumber(n), "invalid option "..all)
            assert(aux >= 1, "invalid option " .. all)
            p  = math.floor(aux)
			return true
		end},
        { "^(%-segs:(%d+)(.*))$", function(all, n, e)
			if not n then return false end
			local aux = assert(tonumber(n), "invalid option "..all)
            assert(aux >= 1, "invalid option " .. all)
            MIN_SEGS  = math.floor(aux)
			return true
		end},
        { "^(%-tx:(%d+)(.*))$", function(all, n, e)
			if not n then return false end
			tx = assert(tonumber(n), "invalid option "..all)
			return true
		end},

        { "^(%-ty:(%d+)(.*))$", function(all, n, e)
			if not n then return false end
			ty = assert(tonumber(n), "invalid option "..all)
			return true
		end},
        { "^(%-sx:(%d+)(.*))$", function(all, n, e)
			if not n then return false end
			sx = assert(tonumber(e), "invalid option "..all)
			return true
		end},
        { "^(%-sy:(%d+)(.*))$", function(all, n, e)
			if not n then return false end
			sy = assert(tonumber(e), "invalid option "..all)
			return true
		end},
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

	if p then scene.elements = {scene.elements[p] } end
	scene = scene:scale(sx,sy)
	scene = scene:translate(tx,ty)

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
            local x, y = vxmin+j-.5, vymin+i-.5
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
