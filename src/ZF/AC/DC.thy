(*  Title:      ZF/AC/DC.thy
    ID:         $Id$
    Author:     Krzysztof Grabczewski

Theory file for the proofs concernind the Axiom of Dependent Choice
*)

DC  =  AC_Equiv + Hartog + Cardinal_aux + DC_lemmas + 

consts

  DC  :: i => o
  DC0 :: o
  ff  :: [i, i, i, i] => i

rules

  DC_def  "DC(a) ==
	     ALL X R. R<=Pow(X)*X &
             (ALL Y:Pow(X). Y lesspoll a --> (EX x:X. <Y,x> : R)) 
             --> (EX f:a->X. ALL b<a. <f``b,f`b> : R)"

  DC0_def "DC0 == ALL A B R. R <= A*B & R~=0 & range(R) <= domain(R) 
                  --> (EX f:nat->domain(R). ALL n:nat. <f`n,f`succ(n)>:R)"

  ff_def  "ff(b, X, Q, R) ==
	   transrec(b, %c r. THE x. first(x, {x:X. <r``c, x> : R}, Q))"
  

locale DC0_imp =
  fixes 
    XX	:: i
    RR	:: i
    X	:: i
    R	:: i

  assumes
    all_ex    "ALL Y:Pow(X). Y lesspoll nat --> (EX x:X. <Y, x> : R)"

  defines
    XX_def    "XX == (UN n:nat. {f:n->X. ALL k:n. <f``k, f`k> : R})"
    RR_def    "RR == {<z1,z2>:XX*XX. domain(z2)=succ(domain(z1))  
                                  & restrict(z2, domain(z1)) = z1}"


locale imp_DC0 =
  fixes 
    XX	:: i
    RR	:: i
    x	:: i
    R	:: i
    f	:: i
    allRR :: o

  defines
    XX_def    "XX == (UN n:nat.
		      {f:succ(n)->domain(R). ALL k:n. <f`k, f`succ(k)> : R})"
    RR_def
     "RR == {<z1,z2>:Fin(XX)*XX. 
              (domain(z2)=succ(UN f:z1. domain(f))  
                & (ALL f:z1. restrict(z2, domain(f)) = f))
	      | (~ (EX g:XX. domain(g)=succ(UN f:z1. domain(f))  
                 & (ALL f:z1. restrict(g, domain(f)) = f)) & z2={<0,x>})}"
    allRR_def
     "allRR == ALL b<nat.
                <f``b, f`b> :  
                 {<z1,z2>:Fin(XX)*XX. (domain(z2)=succ(UN f:z1. domain(f))  
                                    & (UN f:z1. domain(f)) = b  
                                    & (ALL f:z1. restrict(z2,domain(f)) = f))}"
end
