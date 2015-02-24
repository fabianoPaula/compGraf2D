local driver = require"driver"
local style = require"style"
local arc = require"arc"
local xform = require"xform"

local _M = driver.new()

local unpack = table.unpack
local floor = math.floor

require("buffer")

local defs = { data = {}, nradial = 0, nlinear = 0  } -- is a buffer to save definitions

function defs.init(defs)
	defs.data = {}
end

function defs.addradial(def, str)
	local data = def.data
	data[#data + 1] = str
	defs.nradial = defs.nradial + 1
end

function defs.addlinear(def, str)
	local data = def.data
	data[#data + 1] = str
	defs.nlinear = defs.nlinear + 1
end

function defs.size(defs,str)
	return defs["n"..str]
end

function defs.concat(def)
	return table.concat(def.data)
end

require("dump")

local function xformtostring(xform)
    local a = xform[1]
    local b = xform[1+3]
    local c = xform[2]
    local d = xform[2+3]
    local e = xform[3]
    local f = xform[3+3]
    local t = ""
    -- factor scale and translate
    if b == 0 and c == 0 then
        if  e~= 0 or f ~= 0 then
            if f ~= 0 then
                t = string.format("translate(%g, %g)", e, f)
            else
                t = string.format("translate(%g)", e)
            end
        end
        if a == d then
            if a ~= 1 then
                t = t ~= "" and " " .. t  or t
                t = t .. string.format(" scale(%g)", a) 
            end
        else
            t = t ~= "" and " " .. t  or t
            t = t .. string.format(" scale(%g, %g)", a, d) 
        end
    else
        -- could also try to factor rotate, but not worth it
        t = string.format("matrix(%g, %g, %g, %g, %g, %g)", a, b, c, d, e, f)
    end
    return t
end

local write = {}

local rvgcommand = {
    begin_open_contour = "M",
    begin_closed_contour = "M",
    linear_segment = "L",
    quadratic_segment = "Q",
    rational_quadratic_segment = "R",
    cubic_segment = "C",
    end_closed_contour = "Z",
}

function write.path(shape, buffer)
    local previous = ""
	local s = xformtostring(shape.xf)
 	ecount = ecount + 1
    writeB(buffer, string.format("<path id=\"p%d\" d=\"",ecount))
    for i,v in ipairs(shape.instructions) do
        local o = shape.offsets[i]
        local s = rvgcommand[v]
        if s then
            if v ~= previous then
				if s == "R" then 
	               writeB(buffer,"A")
				else
	               writeB(buffer,s)
				end
                writeB(buffer," ")
            end
            if s == "M" then
                writeB(buffer,shape.data[o+1].." "..shape.data[o+2].." ")
            elseif s == "L" then
                writeB(buffer,shape.data[o+2].." "..shape.data[o+3].." ")
            elseif s == "Q" then
                writeB(buffer,shape.data[o+2].." "..shape.data[o+3].. " ")
                writeB(buffer,shape.data[o+4].." "..shape.data[o+5].. " ")
            elseif s == "C" then
                writeB(buffer,shape.data[o+2].." "..shape.data[o+3].." ")
                writeB(buffer,shape.data[o+4].." "..shape.data[o+5].." ")
                writeB(buffer,shape.data[o+6].." "..shape.data[o+7].." ")
            elseif s == "R" then
				local sx, sy, ax, fa, fs = arc.tosvg(shape.data[o], shape.data[o+1],
					shape.data[o+2], shape.data[o+3], shape.data[o+4], 
					shape.data[o+5],shape.data[o+6])
				writeB(buffer,sx.." "..sy.." "..ax.." "..fa.." "..fs.." ") 
				writeB(buffer,shape.data[o+5].." ".. shape.data[o+6].." ")  
--                writeB(buffer,shape.data[o+2].." "..shape.data[o+3].." ")
--              writeB(buffer,shape.data[o+4].." "..shape.data[o+5].." ")
--            writeB(buffer,shape.data[o+6].." ")
            end
            previous = v
        end
    end
	writeB(buffer,"\" ")
	if s ~= "" then
		writeB(buffer,"transform=\""..s.."\"  ") 
	end
end

function write.polygon(shape, file)
	local s = xformtostring(shape.xf)
    writeB(buffer,string.format("<polygon points=\"%s\" ",table.concat(shape.data, " ")))
	if s ~= "" then
		writeB(buffer,"transform=\""..s.."\"  ") 
	end
end

function write.triangle(shape, file)
	local s = xformtostring(shape.xf)
    writeB(buffer,"<polygon ")
 	ecount = ecount + 1
    writeB(buffer, string.format("id=\"p%d\" ",ecount))
	writeB(buffer,"points=\"")
    writeB(buffer,shape.x1.." " .. shape.y1.."  ")
    writeB(buffer,shape.x2.." "..shape.y2.."  ")
    writeB(buffer,shape.x3.." "..shape.y3.."\" ")
	if s ~= "" then
		writeB(buffer,"transform=\""..s.."\"  ") 
	end
end

function write.circle(shape, buffer)
	local s = xformtostring(shape.xf)
    writeB(buffer,"<circle " )
 	ecount = ecount + 1
    writeB(buffer, string.format("id=\"p%d\" ",ecount))
	writeB(buffer, string.format("cx=\"%g\" ",shape.cx))
	writeB(buffer, string.format("cy=\"%g\" ",shape.cy))
	writeB(buffer, string.format("r=\"%g\" ",shape.r))
	if s ~= "" then
		writeB(buffer,"transform=\"" .. s .. "\"  ") 
	end
end

function writecolor(color)
    local r, g, b, a = unpack(color)
	local color = ""
    r = floor(r*255+.5) -- +.5
    g = floor(g*255+.5)
    b = floor(b*255+.5)
    --a = floor(a*255+.5)
    if a ~= 255 then
        --color = "rgba8(", r, ",", g, ",", b, ",", a, ")")
        color = string.format("rgb(%d,%d,%d)",r,g,b)
    else
        color = string.format("rgb(%d,%d,%d)",r,g,b)
    end
	return color
end

function write.radialgradient(paint, buffer)
	local s = xformtostring(paint.xf)
	local data = paint.data
 	local ramp = paint.data.ramp
	local index = defs:size("radial") + 1

	writeB(buffer," fill=\"url(#radial" .. index .. ")\" ")

	local focus = paint.data.focus
	local radius = paint.data.radius
	local center = paint.data.center

    local def = string.format("<radialGradient id=\"radial%d\" ",index) 
    def = def .. "gradientUnits=\"userSpaceOnUse\" "
	def = def .. string.format("cx=\"%g\" ",center[1])
	def = def .. string.format("cy=\"%g\" ",center[2])
	def = def .. string.format("fx=\"%g\" ",focus[1])
	def = def .. string.format("fy=\"%g\" ",focus[2])
	def = def .. string.format("r=\"%g\" ",radius)
	def = def .. string.format("spreadMethod=\"%s\" ",ramp.spread)
	def = def .. string.format("gradientTransform=\"%s\">\n", s)
	
	local lim = #ramp - 1

	for i = 1,lim,2 do
		def = def .. string.format("<stop offset=\"%g\" ",ramp[i])
		def = def .. string.format("stop-color=\"%s\" ",writecolor(ramp[i+1]))
		def = def .. string.format("stop-opacity=\"%g\"/> \n",ramp[i+1][4]*paint.opacity)
	end
	def = def .. "</radialGradient>\n"
	defs:addradial(def)
end

function write.lineargradient(paint, buffer)
	local s = xformtostring(paint.xf)
	local data = paint.data
 	local ramp = paint.data.ramp
	local index = defs:size("linear") + 1
	writeB(buffer, " fill=\"url(#linear" .. index .. ")\" ")
	local def = string.format("<linearGradient id=\"linear%d\" ",index)
	def = def .. "gradientUnits=\"userSpaceOnUse\" "
	def = def .. string.format("x1=\"%g\" ",data.p1[1])
	def = def .. string.format("y1=\"%g\" ",data.p1[2])
	def = def .. string.format("x2=\"%g\" ",data.p2[1])
	def = def .. string.format("y2=\"%g\" ",data.p2[2])
	def = def .. string.format("spreadMethod=\"%s\" ",ramp.spread)
	def = def .. string.format("gradientTransform=\"%s\" >\n", s)

	local lim = #ramp - 1


	for i = 1,lim,2 do
		def = def .. string.format("<stop offset=\"%g\" ",ramp[i])
		def = def .. string.format("stop-color=\"%s\" ",writecolor(ramp[i+1]))
		def = def .. string.format("stop-opacity=\"%g\" /> \n",ramp[i+1][4]*paint.opacity)
	end
	def = def .. "</linearGradient>\n"
	defs:addlinear(def)
end

function write.solid(paint, buffer)
    writeB(buffer,"fill=\"") 
    writeB(buffer,writecolor(paint.data))
	writeB(buffer,"\" ")
	writeB(buffer,string.format("fill-opacity=\"%g\" ",paint.opacity*paint.data[4]))
end

function write.fill(element, buffer)
    write[element.shape.type](element.shape, buffer)
    write[element.paint.type](element.paint, buffer)
	writeB(buffer," />\n")
end

function write.eofill(element, buffer)
    write[element.shape.type](element.shape, buffer)
    writeB(buffer," fill-rule=\"evenodd\"  ")
    write[element.paint.type](element.paint, buffer)
	writeB(buffer," />\n")
end

local buffer = nil

function _M.open(viewport)

    local vxmin, vymin, vxmax, vymax = unpack(viewport, 1, 4)

	defs:init()
	buffer = newBuffer()
	ecount = 0

	writeB(buffer,"<?xml version=\"1.0\" standalone=\"no\"?>\n")
	writeB(buffer,"<svg \n")
	writeB(buffer," xmlns:xlink=\"http://www.w3.org/1999/xlink\" \n ")
	writeB(buffer,"xmlns:dc=\"http://purl.org/dc/elements/1.1/\" \n ")
	writeB(buffer,"xmlns:cc=\"http://creativecommons.org/ns#\" \n ")
	writeB(buffer,"xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\" \n ")
	writeB(buffer,"xmlns:svg=\"http://www.w3.org/2000/svg\" \n ")
	writeB(buffer,"xmlns=\"http://www.w3.org/2000/svg\" \n ")
	writeB(buffer,"version=\"1.1\" \n ")
	writeB(buffer," viewBox=\"" .. table.concat(viewport," ") ..  "\" ")
	writeB(buffer,">\n")
	writeB(buffer,"<defs></defs>")

	local xfs = xform.scale(1,-1)
	local xft = xform.translate(0,vymax)

	xf = xft*xfs
	
    local s = xformtostring(xf)

	writeB(buffer,"<g id=\"main\" transform=\"" .. s .. "\">\n")
end

group = 0 

function _M.render(scene, viewport)
	assert(buffer, "buffer was not create. Call open first")
    local vxmin, vymin, vxmax, vymax = unpack(viewport, 1, 4)

	
	writeB(buffer,"<g id=\"g"..group.."\">\n")
	writeB(buffer,"<path id=\"c"..ecount.."\" d=\"M "..vxmin.." "..vymin.." L "..
		vxmin.." "..vymax.." L "..vxmax.." "..vymax.." L "..vxmax.." "..vymin..
		" L "..(vxmin+1).." "..vymin.." Z \" stroke=\"black\" fill=\"white\""..
		" stroke-width=\"0.3\" />\n")
	ecount = ecount + 1
    for i,element in ipairs(scene.elements) do
        local callback = assert(write[element.type],
            "no handler for " .. element.type)
        callback(element, buffer)
    end
	writeB(buffer,"</g>\n")
end

function _M.close(file)
	writeB(buffer,"</g>\n")
	writeB(buffer,"</svg>")
	result = table.concat(buffer)
	result = result:gsub("<defs></defs>",string.format("<defs>\n%s</defs>\n",defs:concat()))
	file:write(result)
end

return _M
