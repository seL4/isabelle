Gate2 = FOL +
consts  "~&"     :: "[o,o] => o" (infixl 35)
        "#"      :: "[o,o] => o" (infixl 30)
        If       :: "[o,o,o] => o"       ("if _ then _ else _")
rules   nand_def "P ~& Q == ~(P & Q)"    
        xor_def  "P # Q  == P & ~Q | ~P & Q"
        If_def   "if P then Q else R == P&Q | ~P&R"
end
