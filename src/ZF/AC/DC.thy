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
	     \\<forall>X R. R \\<subseteq> Pow(X)*X &
             (\\<forall>Y \\<in> Pow(X). Y lesspoll a --> (\\<exists>x \\<in> X. <Y,x> \\<in> R)) 
             --> (\\<exists>f \\<in> a->X. \\<forall>b<a. <f``b,f`b> \\<in> R)"

  DC0_def "DC0 == \\<forall>A B R. R \\<subseteq> A*B & R\\<noteq>0 & range(R) \\<subseteq> domain(R) 
                  --> (\\<exists>f \\<in> nat->domain(R). \\<forall>n \\<in> nat. <f`n,f`succ(n)>:R)"

  ff_def  "ff(b, X, Q, R) ==
	   transrec(b, %c r. THE x. first(x, {x \\<in> X. <r``c, x> \\<in> R}, Q))"
  

locale DC0_imp =
  fixes 
    XX	:: i
    RR	:: i
    X	:: i
    R	:: i

  assumes
    all_ex    "\\<forall>Y \\<in> Pow(X). Y lesspoll nat --> (\\<exists>x \\<in> X. <Y, x> \\<in> R)"

  defines
    XX_def    "XX == (\\<Union>n \\<in> nat. {f \\<in> n->X. \\<forall>k \\<in> n. <f``k, f`k> \\<in> R})"
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
    XX_def    "XX == (\\<Union>n \\<in> nat.
		      {f \\<in> succ(n)->domain(R). \\<forall>k \\<in> n. <f`k, f`succ(k)> \\<in> R})"
    RR_def
     "RR == {<z1,z2>:Fin(XX)*XX. 
              (domain(z2)=succ(\\<Union>f \\<in> z1. domain(f))  
                & (\\<forall>f \\<in> z1. restrict(z2, domain(f)) = f))
	      | (~ (\\<exists>g \\<in> XX. domain(g)=succ(\\<Union>f \\<in> z1. domain(f))  
                 & (\\<forall>f \\<in> z1. restrict(g, domain(f)) = f)) & z2={<0,x>})}"
    allRR_def
     "allRR == \\<forall>b<nat.
                <f``b, f`b> \\<in>  
                 {<z1,z2>:Fin(XX)*XX. (domain(z2)=succ(\\<Union>f \\<in> z1. domain(f))  
                                    & (\\<Union>f \\<in> z1. domain(f)) = b  
                                    & (\\<forall>f \\<in> z1. restrict(z2,domain(f)) = f))}"
end
