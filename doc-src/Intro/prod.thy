Prod = FOL +
types   "*" 2                                 (infixl 20)
arities "*"     :: (term,term)term
consts  fst     :: "'a * 'b => 'a"
        snd     :: "'a * 'b => 'b"
        Pair    :: "['a,'b] => 'a * 'b"       ("(1<_,/_>)")
rules   fst     "fst(<a,b>) = a"
        snd     "snd(<a,b>) = b"
end
