(*  Title:      ZF/AC/DC.thy
    ID:         $Id$
    Author:     Krzysztof Grabczewski

Theory file for the proofs concernind the Axiom of Dependent Choice
*)

DC  =  AC_Equiv + Hartog + Cardinal_aux + "DC_lemmas" + 

consts

  DC  :: i => o
  DC0 :: o
  ff  :: [i, i, i, i] => i

rules

  DC_def  "DC(a) == ALL X R. R<=Pow(X)*X &
           (ALL Y:Pow(X). Y lesspoll a --> (EX x:X. <Y,x> : R)) 
           --> (EX f:a->X. ALL b<a. <f``b,f`b> : R)"

  DC0_def "DC0 == ALL A B R. R <= A*B & R~=0 & range(R) <= domain(R) 
           --> (EX f:nat->domain(R). ALL n:nat. <f`n,f`succ(n)>:R)"

  ff_def  "ff(b, X, Q, R) == transrec(b, %c r. 
                             THE x. first(x, {x:X. <r``c, x> : R}, Q))"
  
end
