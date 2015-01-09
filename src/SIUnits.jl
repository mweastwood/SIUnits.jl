module SIUnits

export quantity, unit
export Meter, KiloGram, Second, Ampere, Kelvin, Mole, Candela
export Kilo, Mega, Giga, Tera, Peta, Exa, Zetta,
       Centi, Milli, Micro, Nano, Pico, Femto, Atto, Zepto, Yocto
export Gram, Joule, Coulomb, Volt, Farad, Newton, Ohm, Hertz, Siemens, Watt, Pascal, CentiMeter
export ElectronVolt, Torr, Atmosphere
export as

typealias UnitTuple NTuple{7,Rational{Int}}
const no_unit_tuple = (0//1,0//1,0//1,0//1,0//1,0//1,0//1)

immutable SIQuantity{T<:Number,pow,unt} <: Number
    val::T
end

typealias UnitQuantity{T} SIQuantity{T,0,no_unit_tuple}

immutable SIUnit{pow,unt} <: Number
end

typealias SIPrefix{pow} SIUnit{pow,no_unit_tuple}

tup{T,pow,unt}(::SIQuantity{T,pow,unt}) = unt
tup{pow,unt}(::SIUnit{pow,unt}) = unt
power{T,pow,unt}(::SIQuantity{T,pow,unt}) = pow
power{pow,unt}(::SIUnit{pow,unt}) = pow

quantity(T::Type,pow::Int,unt::UnitTuple) = SIQuantity{T,pow,unt}
quantity(T::Type,unit::SIUnit) = quantity(T,power(unit),tup(unit))

unit(pow::Int,unt::UnitTuple) = SIUnit{pow,unt}
unit(x::SIQuantity) = unit(power(x),tup(x))

to_q(T::Type,pow::Int,unt::UnitTuple,val) = (unt == no_unit_tuple) ? val : quantity(T,pow,unt)(val)
to_u(pow::Int,unt::UnitTuple) = unit(pow,unt)()
to_u(x::SIQuantity) = to_u(power(x),tup(x))

################################################################################
# Promotion and Conversion Rules

import Base: promote_rule, promote_type, convert, float64, float, int

# MathConsts propagate through units. Fancy!!
promote_rule{sym,T,pow,unt}(x::Type{MathConst{sym}},y::Type{SIQuantity{T,pow,unt}}) = SIQuantity{promote_type(MathConst{sym},T)}
promote_rule{sym,pow,unt}(x::Type{MathConst{sym}},y::Type{SIUnit{pow,unt}}) = SIQuantity{MathConst{sym}}

promote_rule{S,pow,unt}(x::Type{Bool},y::Type{SIQuantity{S,pow,unt}}) = SIQuantity{promote_type(Bool,S)}
promote_rule{pow,unt}(x::Type{Bool},y::Type{SIUnit{pow,unt}}) = SIQuantity{Bool}

promote_rule{T,S,pow,unt}(x::Type{T},y::Type{SIQuantity{S,pow,unt}}) = SIQuantity{promote_type(T,S)}
promote_rule{T,pow,unt}(x::Type{T},y::Type{SIUnit{pow,unt}}) = SIQuantity{T}

promote_rule{T,S,powT,powS,untT,untS}(x::Type{SIQuantity{T,powT,untT}},y::Type{SIQuantity{S,powS,untS}}) = SIQuantity{promote_type(T,S)}
promote_rule{T,powT,powS,untT,untS}(x::Type{SIQuantity{T,powT,untT}},B::Type{SIUnit{powS,untS}}) = SIQuantity{T}

# One unspecified, units, one concrete (unspecified occurs as the promotion result from the rules above)
promote_rule{T,S,pow,unt}(x::Type{SIQuantity{T}},y::Type{SIQuantity{S,pow,unt}}) = SIQuantity{promote_type(T,S)}

# Unlike most other types, the promotion of two identitical SIQuantities is
# not that type itself. As such, the promote_type behavior itself must be
# overridden. C.f. https://github.com/Keno/SIUnits.jl/issues/27
promote_type{T,pow,unt}(::Type{SIQuantity{T,pow,unt}}, ::Type{SIQuantity{T,pow,unt}}) = SIQuantity{T}

if VERSION >= v"0.4-dev"
    @eval convert{T}(::Type{SIQuantity{T}},x::Dates.Period) = error("Conversion from Period to SIQuantity not defined")
end

convert{T,S}(::Type{SIQuantity{T}},x::S) = convert(SIQuantity{T},convert(T,x))
convert{T}(::Type{SIQuantity{T}},x::T) = UnitQuantity{T}(x)
convert{T}(::Type{SIQuantity{T}},x::SIUnit) = to_q(T,power(x),tup(x),one(T))

convert{T}(::Type{SIQuantity{T}},x::SIQuantity{T}) = x
convert{T}(::Type{SIQuantity{T}},x::SIQuantity) = to_q(T,power(x),tup(x),convert(T,x.val))

convert{T,S,pow,unt}(::Type{SIQuantity{T,pow,unt}},val::S) = to_q(T,pow,unt,convert(T,val))

function convert{T,S,powT,powS,untT,untS}(::Type{SIQuantity{T,powT,untT}},val::SIQuantity{S,powS,untS})
    if untT != untS
        error("Dimension mismatch in convert. Attempted to convert a ($(repr(SIUnit{powS,untS}))) to ($(repr(SIUnit{powT,untT})))")
    end
    to_q(T,powT,untT,convert(T,val.val*10^(powS-powT)))
end

float64(x::SIQuantity) = float64(x.val)
float(x::SIQuantity) = float(x.val)
int(x::SIQuantity) = int(x.val)

################################################################################
# Comparisons

import Base: isless

==(x::SIQuantity,y::SIQuantity) = (power(x) == power(y)) && (tup(x) == tup(y)) && (x.val == y.val)
=={T}(x::SIQuantity{T},y::SIUnit) = (power(x) == power(y)) && (tup(x) == tup(y)) && (x.val == one(T))
=={T}(x::SIUnit,y::SIQuantity{T}) = (power(x) == power(y)) && (tup(x) == tup(y)) && (one(T) == y.val)
==(x::SIUnit,y::SIUnit) = (power(x) == power(y)) && (tup(x) == tup(y))

function isless(x::SIQuantity,y::SIQuantity)
    tup(x) != tup(y) && error("Comparing numbers with different dimensions.")
    return isless(log10(x.val)+power(x),log10(y.val)+power(y))
end
function isless(x::SIQuantity, y::Number)
    tup(x) != no_unit_tuple && error("Comparing dimensionful number with dimensionless number.")
    return isless(log10(x.val)+power(x),log10(y))
end
function isless(x::Number, y::SIQuantity)
    tup(y) != no_unit_tuple && error("Comparing dimensionful number with dimensionless number.")
    return isless(log10(x),log10(y.val)+power(y))
end

################################################################################
# Arithmetic

import Base: one, zero, inv, sqrt, mod, isnan, isreal, isimag, isfinite,
             real, imag, abs, conj

one(x::SIQuantity) = one(x.val)
one{T,pow,unt}(::Type{SIQuantity{T,pow,unt}}) = one(T)
zero{T}(x::SIQuantity{T}) = to_q(T,power(x),tup(x),zero(x.val))
zero{T,pow,unt}(::Type{SIQuantity{T,pow,unt}}) = to_q(T,pow,unt,zero(T))

for op in (:+,:-,:*,:/)
    @eval function $op(tup1::UnitTuple,tup2::UnitTuple)
        ($op(tup1[1],tup2[1]),$op(tup1[2],tup2[2]),$op(tup1[3],tup2[3]),
         $op(tup1[4],tup2[4]),$op(tup1[5],tup2[5]),$op(tup1[6],tup2[6]),
         $op(tup1[7],tup2[7]))
    end

    @eval function $op(tup::UnitTuple,i::Union(Integer,Rational))
        ($op(tup[1],i),$op(tup[2],i),$op(tup[3],i),
         $op(tup[4],i),$op(tup[5],i),$op(tup[6],i),
         $op(tup[7],i))
    end
end

-(tup::UnitTuple) = (-tup[1],-tup[2],-tup[3],-tup[4],-tup[5],-tup[6],-tup[7])

for op in (:+,:-)
    @eval function $op(x::SIQuantity,y::SIQuantity)
        tup(x) != tup(y) && error("Unit mismatch.")
        val = $op(x.val,y.val*10^(power(y)-power(x)))
        to_q(typeof(val),power(x),tup(x),val)
    end
end

*(x::SIUnit,y::SIUnit) = to_u(power(x)+power(y),tup(x)+tup(y))
*{T}(x::SIUnit,y::SIQuantity{T}) = to_q(T,power(x)+power(y),tup(x)+tup(y),y.val)
*{T}(x::SIQuantity{T},y::SIUnit) = to_q(T,power(x)+power(y),tup(x)+tup(y),x.val)
function *(x::SIQuantity,y::SIQuantity)
    val = x.val * y.val
    to_q(typeof(val),power(x)+power(y),tup(x)+tup(y),val)
end

*(x::MathConst,y::SIUnit) = to_q(typeof(x),power(y),tup(y),x)

for op in (:/,://)
    @eval $op(x::SIUnit,y::SIUnit) = to_u(power(x)-power(y),tup(x)-tup(y))
    @eval $op{T}(x::SIQuantity{T},y::SIUnit) = to_q(T,power(x)-power(y),tup(x)-tup(y),x.val)
    @eval $op{T}(x::SIUnit,y::SIQuantity{T}) = to_q(T,power(x)-power(y),tup(x)-tup(y),$op(1,y.val))
    @eval function $op(x::SIQuantity,y::SIQuantity)
        val = $op(x.val,y.val)
        to_q(typeof(val),power(x)-power(y),tup(x)-tup(y),val)
    end

    @eval $op(x::Number,y::SIUnit) = x*to_u(-power(y),-tup(y))
    @eval function $op{T}(x::Number,y::SIQuantity{T})
        val = $op(x,y.val)
        to_q(typeof(val),-power(y),-tup(y),val)
    end
end

inv(x::SIUnit) = to_u(-power(x),-tup(x))

^(x::SIUnit,i::Integer) = to_u(power(x)*i,tup(x)*i)
function ^(x::SIQuantity,i::Integer)
    val = x.val^i
    to_q(typeof(val),power(x)*i,tup(x)*i,val)
end

function ^(x::SIUnit,r::Rational)
    pow = power(x)*r
    val = 10^(pow-int(pow))
    to_q(typeof(val),int(pow),tup(x)*r,val)
end
function ^(x::SIQuantity,r::Rational)
    pow = power(x)*r
    val = x.val^r*10^(pow-int(pow))
    to_q(typeof(val),int(pow),tup(x)*r,val)
end

^(x::SIUnit,f::FloatingPoint) = x^rationalize(f)
^(x::SIQuantity,f::FloatingPoint) = x^rationalize(f)

^(x::SIQuantity,y::SIQuantity) = error("Can not raise a number to a unitful quantity. Got ($(repr(unit(x))))^($(repr(unit(y))))")

function sqrt(x::SIQuantity)
    val = sqrt(x.val)
    if isodd(power(x))
        val *= sqrt(10)
    end
    to_q(typeof(val),div(power(x),2),tup(x)/2,val)
end

function mod(x::SIQuantity,y::SIQuantity)
    tup(x) != tup(y) && error("Unit mismatch. Got mod($(repr(unit(x))),$(repr(unit(y))))")
    val = mod(x.val*10^(power(x)-power(y)),y.val)
    to_q(typeof(val),power(y),tup(x),val)
end

for func in (:isnan,:isreal,:isimag,:isfinite)
    @eval $func(x::SIQuantity) = $func(x.val)
end

for func in (:real,:imag,:abs,:conj)
    @eval $func{T}(x::SIQuantity{T}) = to_q(T,power(x),tup(x),$func(x.val))
end

################################################################################
# Definitions

const Meter    = SIUnit{0, (1//1, 0//1, 0//1, 0//1, 0//1, 0//1, 0//1)}()
const KiloGram = SIUnit{0, (0//1, 1//1, 0//1, 0//1, 0//1, 0//1, 0//1)}()
const Second   = SIUnit{0, (0//1, 0//1, 1//1, 0//1, 0//1, 0//1, 0//1)}()
const Ampere   = SIUnit{0, (0//1, 0//1, 0//1, 1//1, 0//1, 0//1, 0//1)}()
const Kelvin   = SIUnit{0, (0//1, 0//1, 0//1, 0//1, 1//1, 0//1, 0//1)}()
const Mole     = SIUnit{0, (0//1, 0//1, 0//1, 0//1, 0//1, 1//1, 0//1)}()
const Candela  = SIUnit{0, (0//1, 0//1, 0//1, 0//1, 0//1, 0//1, 1//1)}()

const Kilo     = SIPrefix{3}()
const Mega     = SIPrefix{6}()
const Giga     = SIPrefix{9}()
const Tera     = SIPrefix{12}()
const Peta     = SIPrefix{15}()
const Exa      = SIPrefix{18}()
const Zetta    = SIPrefix{21}()
const Yotta    = SIPrefix{24}()
const Centi    = SIPrefix{-2}()
const Milli    = SIPrefix{-3}()
const Micro    = SIPrefix{-6}()
const Nano     = SIPrefix{-9}()
const Pico     = SIPrefix{-12}()
const Femto    = SIPrefix{-15}()
const Atto     = SIPrefix{-18}()
const Zepto    = SIPrefix{-21}()
const Yocto    = SIPrefix{-24}()

const Gram       = Milli*KiloGram
const Joule      = KiloGram*Meter^2/Second^2
const Coulomb    = Ampere*Second
const Volt       = Joule/Coulomb
const Farad      = Coulomb^2/Joule
const Newton     = KiloGram*Meter/Second^2
const Ohm        = Volt/Ampere
const Hertz      = inv(Second)
const Siemens    = inv(Ohm)
const Watt       = Joule/Second
const Pascal     = Newton/Meter^2

const CentiMeter = Centi*Meter

################################################################################
# Printing

import Base: show

# Pretty Printing - Text 
superscript(i) = map(repr(i)) do c
    c   ==  '-' ? '\u207b' :
    c   ==  '1' ? '\u00b9' :
    c   ==  '2' ? '\u00b2' :
    c   ==  '3' ? '\u00b3' :
    c   ==  '4' ? '\u2074' :
    c   ==  '5' ? '\u2075' :
    c   ==  '6' ? '\u2076' :
    c   ==  '7' ? '\u2077' :
    c   ==  '8' ? '\u2078' :
    c   ==  '9' ? '\u2079' :
    c   ==  '0' ? '\u2070' :
    error("Unexpected Character")
end

unit2str = Dict(1 => "m", 2 => "kg", 3 => "s", 4 => "A", 5 => "K", 6 => "mol", 7 => "cd")

function spacing(idx::Int, x::SIUnit)
    # Only print a space if there are nonzero units coming after this one
    tup(x)[idx+1:end] == ntuple(length(unit2str)-idx, (i)->0) ? "" : " "
end

function show(io::IO,x::SIUnit)
    pow = power(x)
    pow != 0 && print(io, "10", (pow == 1 ? "" : superscript(pow)), spacing(0,x))
    for i = 1:length(unit2str)
        u   = tup(x)[i]
        str = unit2str[i]
        u != 0//1 && print(io, str, (u == 1//1 ? "" : den(u) == 1 ? superscript(num(u)) : "^"*repr(u)), spacing(i,x))
    end
    nothing
end

function show(io::IO,x::SIQuantity)
    show(io,x.val)
    print(io," ")
    show(io,to_u(x))
end

#=
# Pretty Printing - LaTeX
using TexExtensions

import Base: writemime

macro l(x)
    esc(quote
        $x != 0 && push!($x>0?num:den,string("\\text{",$(string(x)),"\}",abs($x) == 1 ? " " : string("^{",abs($x),"}")))
    end)
end

function Base.Multimedia.writemime{m,kg,s,A,K,mol,cd}(io::IO,::MIME"text/mathtex+latex",x::SIUnit{m,kg,s,A,K,mol,cd})
    num = ASCIIString[]
    den = ASCIIString[]
    @l kg
    @l m
    @l s
    @l A
    @l K
    @l mol
    @l cd
    if !isempty(den)
        if isempty(num)
            write(io,"\\frac{1}{",join(den,"\\;"),"}")
        else
            write(io,"\\frac{",join(num,"\\;"),"}{",join(den,"\\;"),"}")
        end
    else
        write(io,join(num,"\\;"))
    end
end

function Base.Multimedia.writemime{T,m,kg,s,A,K,mol,cd}(io::IO,::MIME"text/mathtex+latex",x::SIQuantity{T,m,kg,s,A,K,mol,cd})
    writemime(io,MIME("text/mathtex+latex"),x.val)
    write(io,"\\;")
    Base.Multimedia.writemime(io,MIME("text/mathtex+latex"),unit(x))
end

function Base.Multimedia.writemime{BaseUnit,Unit}(io::IO,::MIME"text/mathtex+latex",x::NonSIUnit{BaseUnit,Unit})
    write(io,"\\text{",string(Unit),"}")
end

function Base.Multimedia.writemime(io::IO,::MIME"text/mathtex+latex",x::NonSIQuantity)
    writemime(io,MIME("text/mathtex+latex"),x.val)
    write(io,"\\;")
    Base.Multimedia.writemime(io,MIME("text/mathtex+latex"),unit(x))
end
=#

#=
export @prettyshow

macro prettyshow(unit,string)
    esc(quote function Base.show(io::IO,::SIUnits.SIUnit{SIUnits.sidims($(unit))...})
            print(io,$(string))
        end
        function Base.Multimedia.writemime(io::IO,::MIME"text/mathtex+latex",::SIUnits.SIUnit{SIUnits.sidims($(unit))...})
            Base.Multimedia.writemime(io,MIME("text/mathtex+latex"),$(string))
        end
    end)
end
=#

################################################################################
# Ranges

abstract SIRanges{T,pow,unt} <: Ranges{SIQuantity{T,pow,unt}}

if !isdefined(Base, :UnitRange)
    const Range = Ranges # Deprecations introduced early in the 0.3 cycle
    const UnitRange = Range1
end

immutable SIRange{R<:Range,T<:Real,pow,unt} <: SIRanges{T,pow,unt}
    val::R
end

# This is all nessecary because SIQuanity{T<:Real} !<: Real
show(io::IO, x::SIRanges) = (show(io, x.val); show(io,unit(x)))
function show(io::IO, r::SIRange)
    if step(r) == zero(quantity(r))
        print(io, "SIRange(",first(r),",",step(r),",",length(r),")")
    else
        print(io, first(r),':',step(r),':',last(r))
    end
end
show{T<:UnitRange}(io::IO, r::SIRange{T}) = print(io, first(r),':',last(r))
getindex(r::SIRanges,i::Integer) = (quantity(r)(getindex(r.val,i)))
getindex{T<:SIRanges}(r::T,i::Range) = T(getindex(r.val,i))
function next(r::SIRanges, i)
    v, j = next(r.val,i)
    to_q(quantity(r),v), j
end
length(r::SIRanges) = length(r.val)
start(r::SIRanges) = start(r.val)
done(r::SIRanges,i) = done(r.val,i)
eltype(r::SIRanges) = quantity(r)

for func in (:first,:step,:last)
    @eval $(func)(r::SIRanges) = to_q(quantity(r),$(func)(r.val))
end
# Forward some linear range transformations to the wrapped range
rangequantity{R<:Range}(::Type{R},tup::UnitTuple) = SIRange{R,eltype(R),tup[1],tup[2],tup[3],tup[4],tup[5],tup[6],tup[7]}
for func in (VERSION < v"0.3-" ? (:+, :-) : (:.+, :.-)) # version 0.3 swaps fallbacks
    @eval $(func){T,S,m,kg,s,A,K,mol,cd}(x::SIRanges{T,m,kg,s,A,K,mol,cd}, y::SIQuantity{S,m,kg,s,A,K,mol,cd}) = (val = $(func)(x.val, y.val); SIRange{typeof(val),eltype(val),m,kg,s,A,K,mol,cd}(val))
    @eval $(func){T,S,m,kg,s,A,K,mol,cd}(x::SIQuantity{T,m,kg,s,A,K,mol,cd}, y::SIRanges{S,m,kg,s,A,K,mol,cd}) = (val = $(func)(x.val, y.val); SIRange{typeof(val),eltype(val),m,kg,s,A,K,mol,cd}(val))
end
./(x::SIRanges, y::SIQuantity) = (val = ./(x.val, y.val); rangequantity(typeof(val),tup(x)-tup(y))(val))
.*(x::SIRanges, y::SIQuantity) = (val = .*(x.val, y.val); rangequantity(typeof(val),tup(x)+tup(y))(val))
.*(x::SIQuantity, y::SIRanges) = (val = .*(x.val, y.val); rangequantity(typeof(val),tup(x)+tup(y))(val))
# Version 0.2 assumes all Ranges have start and len fields in ==, and
# the fallback in 0.3 needlessly iterates through all values
==(r::SIRanges, s::SIRanges) = r.val == s.val && tup(r) == tup(s)
==(s::SIRanges, r::Range) = s.val == r && tup(s) == no_unit_tuple
==(r::Range, s::SIRanges) = r == s.val && tup(s) == no_unit_tuple














#=
unit{T,m,kg,s,A,K,mol,cd}(x::SIRanges{T,m,kg,s,A,K,mol,cd}) = SIUnit{m,kg,s,A,K,mol,cd}()
quantity{T,m,kg,s,A,K,mol,cd}(x::SIRanges{T,m,kg,s,A,K,mol,cd}) = SIQuantity{T,m,kg,s,A,K,mol,cd}

import Base: length, getindex, next, float64, float, int, show, start, step, last, done, first, eltype, one, zero
import Base: +, -, *, /, //, ^, promote_rule, promote_type, convert, show, ==, mod

export quantity, @quantity

function quantity{S}(T,quant::SIQuantity{S}) 
    quant.val == one(S) || error("Quantity value must be unity!")
    quantity(T,unit(quant))
end
=#

#=
macro quantity(expr,unit)
    esc(:(SIUnits.SIQuantity{$expr,SIUnits.tup($unit)...}))
end
=#



#=
function -{T,S,mS,kgS,sS,AS,KS,molS,cdS,mT,kgT,sT,AT,KT,molT,cdT}(
    x::SIQuantity{T,mT,kgT,sT,AT,KT,molT,cdT},y::SIQuantity{S,mS,kgS,sS,AS,KS,molS,cdS}) 
    error("Unit mismatch. Got ($(repr(unit(x)))) - ($(repr(unit(y))))")
end     

function +{T,S,mS,kgS,sS,AS,KS,molS,cdS,mT,kgT,sT,AT,KT,molT,cdT}(
    x::SIQuantity{T,mT,kgT,sT,AT,KT,molT,cdT},y::SIQuantity{S,mS,kgS,sS,AS,KS,molS,cdS}) 
    error("Unit mismatch. Got ($(repr(unit(x)))) + ($(repr(unit(y))))")
end

function -{T,m,kg,s,A,K,mol,cd}(x::SIQuantity{T,m,kg,s,A,K,mol,cd})
    val = -(x.val)
    SIQuantity{typeof(val),m,kg,s,A,K,mol,cd}(val)
end

function ^{T,m,kg,s,A,K,mol,cd}(
    x::SIQuantity{T,m,kg,s,A,K,mol,cd},r::Rational) 
    if r == 0
        return one(T)
    end
    val = x.val^r
    SIQuantity{typeof(val),convert(Int,m*r),convert(Int,kg*r),convert(Int,s*r),convert(Int,A*r),
    convert(Int,K*r),convert(Int,mol*r),convert(Int,cd*r)}(val)
end

^{T,m,kg,s,A,K,mol,cd}(x::SIQuantity{T,m,kg,s,A,K,mol,cd},r::FloatingPoint) = x^rationalize(r)

^{T,S,m,kg,s,A,K,mol,cd}(x::SIQuantity{T,m,kg,s,A,K,mol,cd},y::SIQuantity{S,0,0,0,0,0,0,0}) = x.val^(y.val)

import Base: sqrt, abs, colon, isless, isfinite, isreal, real, imag, isnan

function colon{T,S,X,m,kg,s,A,K,mol,cd}(start::SIQuantity{T,m,kg,s,A,K,mol,cd},step::SIQuantity{S,m,kg,s,A,K,mol,cd},stop::SIQuantity{X,m,kg,s,A,K,mol,cd})
    val = colon(start.val,step.val,stop.val)
    SIRange{typeof(val),eltype(val),m,kg,s,A,K,mol,cd}(val)
end

function colon{T,S,m,kg,s,A,K,mol,cd}(start::SIQuantity{T,m,kg,s,A,K,mol,cd},stop::SIQuantity{S,m,kg,s,A,K,mol,cd})
    val = colon(start.val,stop.val)
    SIRange{typeof(val),eltype(val),m,kg,s,A,K,mol,cd}(val)
end


=#

include("nonsiunits.jl")
include("shortunits.jl")

end # module
