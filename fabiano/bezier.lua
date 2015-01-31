-- begin paths fucntions
local max   = math.max
local min   = math.min
local quad  = require("quadratic")
local cubic = require("cubic")
-- this table contem the commands of a path


rvgcommand = {
    begin_open_contour = "M",
    begin_closed_contour = "M",
    linear_segment = "L",
    quadratic_segment = "Q",
    rational_quadratic_segment = "R",
    cubic_segment = "C",
    end_closed_contour = "Z",
}

-- begin bezier functions


-- This function implement the De Casteljou algorithm
-- First receveid n points. Frist calculate points in each linear segment. When
-- calucate for point i and i+1, save the in the i position of cpoints. When 
-- arrive in the end of the vector, come back to the first position, with n-1
-- points. So repeat this procced n times and in the first position will be the 
-- point of the curve
function bezierPoint(points,t)
	local arrayend,i = #points,1
	-- clone the points table
	local cpoints  = deepcopy(points)
	while arrayend > 1 do
		if i == arrayend then 
			i = 1
			arrayend = arrayend - 1
		end
		-- in the end the response, will be in frist position 
		-- with this implementarion
		cpoints[i][1] = (1-t)*cpoints[i][1] + t*cpoints[i+1][1]
		cpoints[i][2] = (1-t)*cpoints[i][2] + t*cpoints[i+1][2]
		i = i + 1
	end
	return cpoint[1]
end


-----------------------------------------------------------------------------
--------------------------------Linear Bezier's------------------------------
-----------------------------------------------------------------------------


-- this function return a point of a quadratic bezier
-- 0 < t < 1
function bezier1D(b, t )
	local x0,y0 = b['x0'],b['y0']
	local x1,y1 = b['x1'],b['y1']

	local x = (1-t)*x0 + t*x1 
	local y = (1-t)*y0 + t*y1 

	return {x,y}
end



-- This function calculate the coefficient of the bezier polynomial for degree=1
function bezierCD1(points)
	local x0,y0 = unpack(points[1])
	local x1,y1 = unpack(points[2])

	local a1,b1 = (x1 - x0 ), x0
	local a2,b2 = (y1 - y0 ), y0

	return {{a1,b1},{a2,b2}}
end


-- This function calculate the coefficient of a derivate of a bezier polynomial
-- of for degree=1
function bezierDerivateCD1(points)
	local x0,y0 = unpack(points[1])
	local x1,y1 = unpack(points[2])

	local a1 = (x1- x0)
	local a2 = (y1 - y0)

	return {a1,a2}
end

function intersectionBezier1D(b,p)
	local ax = b['coeff'][2][1]
	local bx = b['coeff'][2][2] - p.y

	local t = -bx/ax

	if t >= 0 and t <= 1 then
		return t
	else
		return false
	end
end


-- this functions creates a linear bezier
function newBezier1D(p0,p1)
	local points = {p0,p1,p2}
	local b = {}
	b['x0'] = p0[1]
	b['y0'] = p0[2]
	b['x1'] = p1[1]
	b['y1'] = p1[2]
	b['command'] = "L"
	b['coeff'] = bezierCD1(points)
	b['DerivateCoeff'] = bezierDerivateCD1(points)
	b['xmin'] = min(b['x0'],b['x1'])
	b['ymin'] = min(b['y0'],b['y1'])
	b['xmax'] = max(b['x0'],b['x1'])
	b['ymax'] = max(b['y0'],b['y1'])
	b['calculateapoint'] = function(b,t)
		return  b['coeff'][2][1] * t - b['coeff'][2][2]
	end
	return b
end


-----------------------------------------------------------------------------
--------------------------------Quadratic Bezier's---------------------------
-----------------------------------------------------------------------------


-- this function return a point of a quadratic bezier
-- 0 < t < 1
function bezier2D(b, t )
	local x0,y0 = b['x0'],b['y0']
	local x1,y1 = b['x1'],b['y1']
	local x2,y2 = b['x2'],b['y2']

	local x = (1-t)*( (1-t)*x0 + t*x1 ) + t*((1-t)*x1 + t*x2) 
	local y = (1-t)*( (1-t)*y0 + t*y1 ) + t*((1-t)*y1 + t*y2) 

	return {x,y}
end

-- this function use two coordinates to solve find the bezier interpolation point
-- Q(t) --> Q(u,v)
function bezier2D2C(b, u,v )
	local x0,y0 = b['x0'],b['y0']
	local x1,y1 = b['x1'],b['y1']
	local x2,y2 = b['x2'],b['y2']

	local x = (1-u)*( (1-v)*x0 + v*x1 ) + u*((1-v)*x1 + v*x2) 
	local y = (1-u)*( (1-v)*y0 + v*y1 ) + u*((1-v)*y1 + v*y2) 

	return {x,y}
end


-- This function calculate the coefficient of the bezier polynomial for degree=2
function bezierCD2(points)
	local x0,y0 = unpack(points[1])
	local x1,y1 = unpack(points[2])
	local x2,y2 = unpack(points[3])

	local a1,b1,c1 = (x0 - 2*x1 + x2), 2*(x1-x0), x0
	local a2,b2,c2 = (y0 - 2*y1 + y2), 2*(y1-y0), y0

	return {{a1,b1,c1},{a2,b2,c2}}
end


function intersectionBezier2D(b,p)
	local ay = b['coeff'][2][1]
	local by = b['coeff'][2][2]
	local cy = b['coeff'][2][3] - p.y

	local roots = {quad.quadratic(ay,by,cy)}
	local pt = {}
	-- its necessary to prove that this root always is equal
	if roots[1] == 2 then
		local t = roots[2]/roots[3]
		if (t >= 0)and(t <= 1) then
			pt = bezier2D(b,t)
			if p.x < pt[1] then 
				return t
			end
		else
			pt = bezier2D(b,t)
			if p.x < pt[1] then 
				return roots[4]/roots[5]
			end
		end
	else
		return false
	end
end

-- This function returns the derivate vector
function velocityBezier2D(b,t)
	local ay = b['DerivateCoeff'][2][1]
	local by = b['DerivateCoeff'][2][2]

	local ax = b['DerivateCoeff'][1][1]
	local bx = b['DerivateCoeff'][1][2]

	local x = ax*t + bx
	local y = ay*t + by
	
	return {x,y}
end


-- This function calculate the coefficient of a derivate of a bezier polynomial
-- of for degree=2
function bezierDerivateCD2(points)
	local x0,y0 = unpack(points[1])
	local x1,y1 = unpack(points[2])
	local x2,y2 = unpack(points[3])

	local a1,b1 = 2*(x0 - 2*x1 + x2), 2*(x1-x0)
	local a2,b2 = 2*(y0 - 2*y1 + y2), 2*(y1-y0)

	return {{a1,b1},{a2,b2}}
end

-- this function find the points to break the bezier curve
function breakpoints2D(b)
	local ay = b['DerivateCoeff'][2][1]
	local by = b['DerivateCoeff'][2][2]

	local ax = b['DerivateCoeff'][1][1]
	local bx = b['DerivateCoeff'][1][2]

	local t1,t2 = 0,0

	if ax == 0 then
		t1 = nil
	else
		t1 = -bx/ax
	end

	if ay == 0 then
		t2 = nil
	else
		t2 = -bx/ax
	end

	if t1 and t2 then 
		if t2 > t1 then
			local aux = t1
			t1 = t2
			t2 = aux
		end
	elseif not t1 and t2 then
		t1 = t2
	end
	return {t1,t2}
end


-- this functions creates a quadratic bezier
function newBezier2D(p0,p1,p2)
	local points = {p0,p1,p2}
	local b = {}
	b['x0'] = p0[1]
	b['y0'] = p0[2]
	b['x1'] = p1[1]
	b['y1'] = p1[2]
	b['x2'] = p2[1]
	b['y2'] = p2[2]
	b['command'] = "Q"
	b['coeff'] = bezierCD2(points)
	b['DerivateCoeff'] = bezierDerivateCD2(points)
	b['xmin'] = min(b['x0'],b['x1'],b['x2'])
	b['ymin'] = min(b['y0'],b['y1'],b['y2'])
	b['xmax'] = max(b['x0'],b['x1'],b['x2'])
	b['ymax'] = max(b['y0'],b['y1'],b['y2'])
	return b
end


function monotoniseBezier2D(p1,p2,p3)
	local origin = newBezier2D(p1,p2,p3)
	local t = breakpoints2D(origin)

	local result = {}
	local first,control,last = nil,nil,nil

	if t[1] then
		local first = bezier2D2C(origin,0,0)
		local control = bezier2D2C(origin,0,t[1])
		local last = bezier2D2C(origin,t[1],t[1])

		result[#result + 1] = newBezier2D(first,control,last)

		if not t[2] then
			first = bezier2D2C(origin,t[1],t[1])
			control = bezier2D2C(origin,t[1],1)
			last = bezier2D2C(origin,1,1)

			result[#result + 1] = newBezier2D(first,control,last)
		end
	end

	if t[2] then
		if not t[1] then 
			first = bezier2D2C(origin,0,0)
			control = bezier2D2C(origin,0,t[2])
			last = bezier2D2C(origin,t[2],t[2])
		else
			first = bezier2D2C(origin,t[1],t[1])
			control = bezier2D2C(origin,t[1],t[2])
			last = bezier2D2C(origin,t[2],t[2])
		end

		result[#result + 1] = newBezier2D(first,control,last)

		first = bezier2D2C(origin,t[2],t[2])
		control = bezier2D2C(origin,t[2],1)
		last = bezier2D2C(origin,1,1)

		result[#result + 1] = newBezier2D(first,control,last)
	end

	if not t[1] and not t[2] then
		result[#result + 1] = origin
	end

	return result
end

-----------------------------------------------------------------------------
--------------------------------Cubic Bezier's-------------------------------
-----------------------------------------------------------------------------

-- this function calculate the coefficient of a bezier polynomial for degree=3
function bezierCD3(points)
	local x0,y0 = unpack(points[1])
	local x1,y1 = unpack(points[2])
	local x2,y2 = unpack(points[3])
	local x3,y3 = unpack(points[4])

	local a1,b1,c1,d1 = (x3+3*x1-3*x2-x0), 3*(x0-2*x1+x2), 3*(x1-x0), x0
	local a2,b2,c2,d2 = (y3+3*y1-3*y2-y0), 3*(y0-2*y1+y2), 3*(y1-y0), y0

	return {{a1,b1,c1,d1},{a2,b2,c2,d2}}
end

-- This function calculate the coefficient of a derivate of a bezier polynomial
-- of for degree=3
function bezierDerivateCD3(points)
	local x0,y0 = unpack(points[1])
	local x1,y1 = unpack(points[2])
	local x2,y2 = unpack(points[3])
	local x3,y3 = unpack(points[4])

	local a1,b1,c1 = 3*(x0-3*x1-3*x2+x3), 6*(x0-2*x1+x2), 3*(x1-x0)
	local a2,b2,c2 = 3*(y0-3*y1-3*y2+y3), 6*(y0-2*y1+y2), 3*(y1-y0)

	return {{a1,b1,c1},{a2,b2,c2}}
end


-- this functions creates a cubic bezier
function newBezier3D(p0,p1,p2,p3)
	local points = {p0,p1,p2,p3}
	local b = {}
	b['x0'] = p0[1]
	b['y0'] = p0[2]
	b['x1'] = p1[1]
	b['y1'] = p1[2]
	b['x2'] = p2[1]
	b['y2'] = p2[2]
	b['x3'] = p3[1]
	b['y3'] = p3[2]
	b['command'] = "C"
	b['coeff'] = bezierCD3(points)
	b['DerivateCoeff'] = bezierDerivateCD3(points)
	b['xmin'] = min(b['x0'],b['x1'],b['x2'],b['x3'])
	b['ymin'] = min(b['y0'],b['y1'],b['y2'],b['y3'])
	b['xmax'] = max(b['x0'],b['x1'],b['x2'],b['x3'])
	b['ymax'] = max(b['y0'],b['y1'],b['y2'],b['y3'])
	return b
end


-- this function return a point of a cubic bezier
-- 0 < t < 1
function bezier3D(b, t )
	local x0,y0 = b['x0'],b['y0']
	local x1,y1 = b['x1'],b['y1']
	local x2,y2 = b['x2'],b['y2']
	local x3,y3 = b['x3'],b['y3']

	local x1 = (1-t)*( (1-t)*x0 + t*x1 ) + t*((1-t)*x1 + t*x2) 
	local x2 = (1-t)*( (1-t)*x1 + t*x2 ) + t*((1-t)*x2 + t*x3) 
	local x = (1-t)*x1 + t*x2

	local y1 = (1-t)*( (1-t)*y0 + t*y1 ) + t*((1-t)*y1 + t*y2) 
	local y2 = (1-t)*( (1-t)*y1 + t*y2 ) + t*((1-t)*y2 + t*y3) 
	local y = (1-t)*y1 + t*y2

	return {x,y}
end


function intersectionBezier3D(b,p)
	local ay = b['coeff'][2][1]
	local by = b['coeff'][2][2] 
	local cy = b['coeff'][2][3] 
	local dy = b['coeff'][2][4] - p.y

	local roots = { cubic.cubic(ay,by,cy,dy) }
	local pt = {}

	if roots[1] == 3 then
		r = roots[2]/roots[3]
		if ( r >= 0 and r <= 1) then	
			pt = bezier3D(b,r)
			if p.x < pt[1] then 
				return r
			end
		end
		r = roots[4]/roots[5]
		if ( r >= 0 and r <= 1) then	
			pt = bezier3D(b,r)
			if p.x < pt[1] then 
				return r
			end
		end
		r = roots[6]/roots[7]
		if ( r >= 0 and r <= 1) then	
			pt = bezier3D(b,r)
			if p.x < pt[1] then 
				return r
			end
		end
	elseif roots[1] == 1 then
		r = roots[2]/roots[3]
		if ( r >= 0 and r <= 1) then	
			pt = bezier3D(b,r)
			if p.x < pt[1] then 
				return r
			end
		end
	end
	return false
end

-- We need to take care of inflections points
-- so unless take the derivate vector,
-- we will disturb t with a epsilon and took a 
-- diferrence vector of the points t - EPS and t + EPS
function velocityBezier3D(b,t)
	local EPS = 0.01
	local ay = b['coeff'][2][1]
	local by = b['coeff'][2][2]
	local cy = b['coeff'][2][3]
	local dy = b['coeff'][2][4]

	local ax = b['coeff'][1][1]
	local bx = b['coeff'][1][2]
	local cx = b['coeff'][1][3]
	local dx = b['coeff'][1][4]

	local x0 = ax*t^3 + bx*t^2 + cx*t + dx
	local x1 = ax*(t + EPS)^3 + bx*(t + EPS)^2 + cx*(t + EPS) + dx


	local y0 = ay*t^3 + by*t^2 + cy*t + dy
	local y1 = ay*(t + EPS)^3 + by*(t + EPS)^2 + cy*(t + EPS) + dy
	
	return {x1-x0,y1-y0}
end

-- this function find the points to break the bezier curve
function breakpoints3D(b)
	local ay = b['DerivateCoeff'][2][1]
	local by = b['DerivateCoeff'][2][2]
	local cy = b['DerivateCoeff'][2][3]

	local ax = b['DerivateCoeff'][1][1]
	local bx = b['DerivateCoeff'][1][2]
	local cx = b['DerivateCoeff'][1][3]

	local t1,t2,t3,t4 = 0,0,0,0

	if ax == 0 then
		t1 = nil
	else
		t1 = -bx/ax
	end

	if ay == 0 then
		t2 = nil
	else
		t2 = -bx/ax
	end

	if t1 and t2 then 
		if t2 > t1 then
			local aux = t1
			t1 = t2
			t2 = aux
		end
	elseif not t1 and t2 then
		t1 = t2
	end
	return {t1,t2}
end 

-- end bezier functions
-- end path functions
