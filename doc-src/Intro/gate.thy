Gate = FOL +
consts  nand,xor :: "[o,o] => o"
rules   nand_def "nand(P,Q) == ~(P & Q)"
        xor_def  "xor(P,Q)  == P & ~Q | ~P & Q"
end
