Chain = List +
consts chain :: "('a => 'a => bool) * 'a list => bool"
recdef chain "measure (%(r,xs). length xs)"
    "chain(r, [])     = True"
    "chain(r, [x])    = True"
    "chain(r, x#y#zs) = (r x y & chain(r, y#zs))"
end
