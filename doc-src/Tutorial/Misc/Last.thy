Last = List +
consts last :: 'a list => 'a
recdef last "measure (%xs. length xs)"
    "last [x]      = x"
    "last (x#y#zs) = last (y#zs)"
end
