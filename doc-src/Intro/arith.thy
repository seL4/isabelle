Arith = FOL +
classes arith < term
consts  "0"     :: "'a::arith"                  ("0")
        "1"     :: "'a::arith"                  ("1")
        "+"     :: "['a::arith,'a] => 'a"       (infixl 60)
end
