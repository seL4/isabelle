(*  Title: 	ZF/AC/AC_Equiv.thy
    ID:         $Id$
    Author: 	Krzysztof Grabczewski

Axioms AC1 -- AC19 come from "Equivalents of the Axiom of Choice, II"
by H. Rubin and J.E. Rubin, 1985.

Axiom AC0 comes from "Axiomatic Set Theory" by P. Suppes, 1972.

Some Isabelle proofs of equivalences of these axioms are formalizations of
proofs presented by the Rubins.  The others are based on the Rubins' proofs,
but slightly changed.
*)

AC_Equiv = CardinalArith + Univ + OrdQuant +

consts
  
(* Well Ordering Theorems *)
  WO1, WO2, WO3, WO5, WO6, WO7, WO8 :: "o"
  WO4                               :: "i => o"

(* Axioms of Choice *)  
  AC0, AC1, AC2, AC3, AC4, AC5, AC6, AC7, AC8, AC9,
  AC11, AC12, AC14, AC15, AC17, AC19 :: "o"
  AC10, AC13              :: "i => o"
  AC16                    :: "[i, i] => o"
  AC18                    :: "prop"       ("AC18")

(* Auxiliary definitions used in definitions *)
  pairwise_disjoint       :: "i => o"
  sets_of_size_between    :: "[i, i, i] => o"

defs

(* Well Ordering Theorems *)

  WO1_def "WO1 == ALL A. EX R. well_ord(A,R)"

  WO2_def "WO2 == ALL A. EX a. Ord(a) & A eqpoll a"

  WO3_def "WO3 == ALL A. EX a. Ord(a) & (EX b. b <= a & A eqpoll b)"

  WO4_def "WO4(m) == ALL A. EX a f. Ord(a) & domain(f)=a &   
	             (UN b<a. f`b) = A & (ALL b<a. f`b lepoll m)"

  WO5_def "WO5 == EX m:nat. 1 le m & WO4(m)"

  WO6_def "WO6 == ALL A. EX m:nat. 1 le m & (EX a f. Ord(a) & domain(f)=a   
	            & (UN b<a. f`b) = A & (ALL b<a. f`b lepoll m))"

  WO7_def "WO7 == ALL A. Finite(A) <-> (ALL R. well_ord(A,R) -->   
	            well_ord(A,converse(R)))"

  WO8_def "WO8 == ALL A. (EX f. f : (PROD X:A. X)) -->  
	            (EX R. well_ord(A,R))"

(* Axioms of Choice *)  

  AC0_def "AC0 == ALL A. EX f. f:(PROD X:Pow(A)-{0}. X)"

  AC1_def "AC1 == ALL A. 0~:A --> (EX f. f:(PROD X:A. X))"

  AC2_def "AC2 == ALL A. 0~:A & pairwise_disjoint(A)   
	            --> (EX C. ALL B:A. EX y. B Int C = {y})"

  AC3_def "AC3 == ALL A B. ALL f:A->B. EX g. g:(PROD x:{a:A. f`a~=0}. f`x)"

  AC4_def "AC4 == ALL R A B. (R<=A*B --> (EX f. f:(PROD x:domain(R). R``{x})))"

  AC5_def "AC5 == ALL A B. ALL f:A->B. EX g:range(f)->A.   
	            ALL x:domain(g). f`(g`x) = x"

  AC6_def "AC6 == ALL A. 0~:A --> (PROD B:A. B)~=0"

  AC7_def "AC7 == ALL A. 0~:A & (ALL B1:A. ALL B2:A. B1 eqpoll B2)   
	            --> (PROD B:A. B)~=0"

  AC8_def "AC8 == ALL A. (ALL B:A. EX B1 B2. B=<B1,B2> & B1 eqpoll B2)   
	            --> (EX f. ALL B:A. f`B : bij(fst(B),snd(B)))"

  AC9_def "AC9 == ALL A. (ALL B1:A. ALL B2:A. B1 eqpoll B2) -->   
	            (EX f. ALL B1:A. ALL B2:A. f`<B1,B2> : bij(B1,B2))"

  AC10_def "AC10(n) ==  ALL A. (ALL B:A. ~Finite(B)) -->   
	            (EX f. ALL B:A. (pairwise_disjoint(f`B) &   
	            sets_of_size_between(f`B, 2, succ(n)) & Union(f`B)=B))"

  AC11_def "AC11 == EX n:nat. 1 le n & AC10(n)"

  AC12_def "AC12 == ALL A. (ALL B:A. ~Finite(B)) -->   
	    (EX n:nat. 1 le n & (EX f. ALL B:A. (pairwise_disjoint(f`B) &   
	    sets_of_size_between(f`B, 2, succ(n)) & Union(f`B)=B)))"

  AC13_def "AC13(m) == ALL A. 0~:A --> (EX f. ALL B:A. f`B~=0 &   
	                                  f`B <= B & f`B lepoll m)"

  AC14_def "AC14 == EX m:nat. 1 le m & AC13(m)"

  AC15_def "AC15 == ALL A. 0~:A --> (EX m:nat. 1 le m & (EX f. ALL B:A.   
	                              f`B~=0 & f`B <= B & f`B lepoll m))"

  AC16_def "AC16(n, k)  == ALL A. ~Finite(A) -->   
	    (EX T. T <= {X:Pow(A). X eqpoll succ(n)} &   
	    (ALL X:{X:Pow(A). X eqpoll succ(k)}. EX! Y. Y:T & X <= Y))"

  AC17_def "AC17 == ALL A. ALL g: (Pow(A)-{0} -> A) -> Pow(A)-{0}.   
	            EX f: Pow(A)-{0} -> A. f`(g`f) : g`f"

  AC18_def "AC18 == (!!X A B. A~=0 & (ALL a:A. B(a) ~= 0) -->   
                 ((INT a:A. UN b:B(a). X(a,b)) =   
                 (UN f: PROD a:A. B(a). INT a:A. X(a, f`a))))"

  AC19_def "AC19 == ALL A. A~=0 & 0~:A --> ((INT a:A. UN b:a. b) =   
	            (UN f:(PROD B:A. B). INT a:A. f`a))"

(* Auxiliary definitions used in the above definitions *)

  pairwise_disjoint_def    "pairwise_disjoint(A)   
			    == ALL A1:A. ALL A2:A. A1 Int A2 ~= 0 --> A1=A2"

  sets_of_size_between_def "sets_of_size_between(A,m,n)   
			    == ALL B:A. m lepoll B & B lepoll n"
  
end
