BoolNat = Arith +
types   bool,nat    0
arities bool,nat    :: arith
consts  Suc         :: "nat=>nat"
rules   add0        "0 + n = n::nat"
        addS        "Suc(m)+n = Suc(m+n)"
        nat1        "1 = Suc(0)"
        or0l        "0 + x = x::bool"
        or0r        "x + 0 = x::bool"
        or1l        "1 + x = 1::bool"
        or1r        "x + 1 = 1::bool"
end
