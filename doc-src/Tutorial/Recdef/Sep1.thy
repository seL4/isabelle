Sep1 = Main +
consts sep :: "'a * 'a list => 'a list"
recdef sep "measure (%(a,xs). length xs)"
  "sep(a, x#y#zs) = x # a # sep(a,y#zs)"
  "sep(a, xs)     = xs"
end
