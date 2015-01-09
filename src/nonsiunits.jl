immutable NonSIUnit{BaseUnit<:SIUnit,Unit}; end
immutable NonSIQuantity{T,Unit<:NonSIUnit} <: Number
    val::T
end

baseunit{BaseUnit}(x::NonSIUnit{BaseUnit}) = BaseUnit()
baseunit{T,Unit}(x::NonSIQuantity{T,Unit}) = baseunit(unit(x))
unit{T,Unit}(x::NonSIQuantity{T,Unit}) = Unit()
quantity(T::Union(Type,TypeVar),x::NonSIUnit) = NonSIQuantity{T,typeof(x)}
quantity(T::Union(Type,TypeVar),U::Type{NonSIUnit}) = NonSIQuantity{T,U}

################################################################################
# Promotion and Conversion Rules

promote_rule(x::Type{MathConst},y::Type{NonSIUnit}) = NonSIQuantity{x,y}
promote_rule{sym,T,Unit}(x::Type{MathConst{sym}},y::Type{NonSIQuantity{T,Unit}}) = NonSIQuantity{promote_type(MathConst{sym},T),Unit}

promote_rule{T,S,U1,U2}(A::Type{NonSIQuantity{T,U1}},B::Type{SIQuantity{S,U2}}) = NonSIQuantity{promote_type(T,S)}
promote_rule{T,U1}(A::Type{NonSIQuantity{T,U1}},U2::Type{NonSIUnit}) = NonSIQuantity{T}
promote_rule{S,U}(x::Type{Bool},y::Type{NonSIQuantity{S,U}}) = NonSIQuantity{promote_type(Bool,S),U}
promote_rule(x::Type{Bool},U::Type{NonSIUnit}) = NonSIQuantity{Bool,U}
promote_rule{T,S,U}(x::Type{T},y::Type{NonSIQuantity{S,U}}) = NonSIQuantity{promote_type(T,S),U}
promote_rule{T}(x::Type{T},U::Type{NonSIUnit}) = NonSIQuantity{T,U}

# Interaction between SI and non-SI quantities
promote_rule{S,T,U,pow,unt}(x::Type{NonSIQuantity{S,U}},y::Type{SIQuantity{T,pow,unt}}) = SIQuantity{promote_type(S,T)}
promote_rule{S,T,U,pow,unt}(x::Type{SIQuantity{T,pow,unt}},y::Type{NonSIQuantity{S,U}}) = SIQuantity{promote_type(S,T)}

siquantity{B}(T,U::NonSIUnit{B}) = quantity(T,B())
siquantity{B}(T,U::Type{NonSIUnit{B}}) = quantity(T,B())
#convert{T,S,U}(::Type{SIQuantity{T}},x::NonSIQuantity{S,U}) = (siquantity(promote_type(T,S),U())(x.val))

# No, these two are not the same. Sometimes we get SIQuantities that are not specialized 
# on the type out of promotion, hence the first method, but we still need the second method
# to be more specific that the convert methods of plain SIUnits above.
convert(::Type{SIQuantity},x::NonSIQuantity) = x.val * convert(SIQuantity,unit(x))
convert{T}(::Type{SIQuantity{T}},x::NonSIQuantity) = x.val * convert(SIQuantity,unit(x))

convert{T}(::Type{NonSIQuantity{T}},U::NonSIUnit) = NonSIQuantity{T,U}(one(T))
convert{T,U}(::Type{NonSIQuantity{T,U}},x::T) = UnitQuantity{T}(x)
#convert{T}(::Type{NonSIQuantity{T}},x::T) = UnitQuantity{T}(x)
#convert{T,S}(::Type{NonSIQuantity{T}},x::S) = convert(NonSIQuantity{T},convert(T,x))
if VERSION >= v"0.4-dev"
    eval(quote
        convert{T,U}(::Type{NonSIQuantity{T,U}},x::Dates.Period) = error("Conversion from Period to NonSIQuantity not defined")
    end)
end
convert{T,U,S}(::Type{NonSIQuantity{T,U}},x::S) = convert(NonSIQuantity{T,U},convert(T,x))
convert{T,U}(::Type{NonSIQuantity{T,U}},x::NonSIQuantity{T,U}) = x
convert{T,S,U1,U2}(::Type{NonSIQuantity{T,U1}},x::NonSIQuantity{S,U2}) = NonSIQuantity{T,U2}(convert(T,x.val))

function as{U<:NonSIUnit}(x::SIQuantity,y::U)
    val = x/y
    @assert !(typeof(val)<:SIQuantity)
    NonSIQuantity{typeof(val),U}(val)
end

function as{U<:NonSIUnit,Q<:SIQuantity}(X::AbstractArray{Q},y::U)
    val = [x/y for x in X]
    @assert !(typeof(eltype(val))<:SIQuantity)
    NonSIQuantity{typeof(val),U}(val)
end

function as(x::NonSIQuantity,y::SIUnit)
    @assert baseunit(x) == y
    convert(SIQuantity,x)
end

as(x::NonSIQuantity,y::SIQuantity) = as(x,unit(y))

################################################################################
# Arithmetic

*{T<:NonSIUnit}(x,t::T) = NonSIQuantity{typeof(x),T}(x)

/{T,U}(x::NonSIQuantity{T,U},y::SIQuantity) = convert(SIQuantity,x)/y
/(x::NonSIUnit,y::SIUnit) = convert(SIQuantity,x)/y
/(x::SIUnit,y::NonSIUnit) = x/convert(SIQuantity,y)

/(x::SIQuantity,y::NonSIUnit) = x/convert(SIQuantity,y)
/(x::NonSIUnit,y::SIQuantity) = convert(SIQuantity,x)/y
-{T,U}(x::NonSIQuantity{T,U}) = NonSIQuantity{T,U}(-x.val) 

^(x::Union(NonSIQuantity,NonSIUnit),i::Integer) = convert(SIQuantity,x)^i

################################################################################
# Definitions

const ElectronVolt = NonSIUnit{typeof(Joule),:eV}()
convert(::Type{SIQuantity},::typeof(ElectronVolt)) = 1.60217656535e-19Joule

const Torr = NonSIUnit{typeof(Pascal),:torr}()
convert(::Type{SIQuantity},::typeof(Torr)) = 133.322368Pascal

const Atmosphere = NonSIUnit{typeof(Pascal),:atm}()
convert(::Type{SIQuantity},::typeof(Atmosphere)) = 101325Pascal

################################################################################
# Printing

show{BaseUnit,Unit}(io::IO,x::NonSIUnit{BaseUnit,Unit}) = write(io,string(Unit))
function show(io::IO,x::NonSIQuantity)
    show(io,x.val)
    print(io," ")
    show(io,unit(x))
end

