(*  Title:      ZF/AC/AC_Equiv.thy
    ID:         $Id$
    Author:     Krzysztof Grabczewski

Axioms AC1 -- AC19 come from "Equivalents of the Axiom of Choice, II"
by H. Rubin and J.E. Rubin, 1985.

Axiom AC0 comes from "Axiomatic Set Theory" by P. Suppes, 1972.

Some Isabelle proofs of equivalences of these axioms are formalizations of
proofs presented by the Rubins.  The others are based on the Rubins' proofs,
but slightly changed.
*)


AC_Equiv = Main + (*obviously not Main_ZFC*)

consts
  
(* Well Ordering Theorems *)
  WO1, WO2, WO3, WO5, WO6, WO7, WO8 :: o
  WO4                               :: i => o

(* Axioms of Choice *)  
  AC0, AC1, AC2, AC3, AC4, AC5, AC6, AC7, AC8, AC9,
  AC11, AC12, AC14, AC15, AC17, AC19 :: o
  AC10, AC13              :: i => o
  AC16                    :: [i, i] => o
  AC18                    :: prop       ("AC18")

(* Auxiliary definitions used in definitions *)
  pairwise_disjoint       :: i => o
  sets_of_size_between    :: [i, i, i] => o

defs

(* Well Ordering Theorems *)

  WO1_def "WO1 == \\<forall>A. \\<exists>R. well_ord(A,R)"

  WO2_def "WO2 == \\<forall>A. \\<exists>a. Ord(a) & A eqpoll a"

  WO3_def "WO3 == \\<forall>A. \\<exists>a. Ord(a) & (\\<exists>b. b \\<subseteq> a & A eqpoll b)"

  WO4_def "WO4(m) == \\<forall>A. \\<exists>a f. Ord(a) & domain(f)=a &   
                     (\\<Union>b<a. f`b) = A & (\\<forall>b<a. f`b lepoll m)"

  WO5_def "WO5 == \\<exists>m \\<in> nat. 1 le m & WO4(m)"

  WO6_def "WO6 == \\<forall>A. \\<exists>m \\<in> nat. 1 le m & (\\<exists>a f. Ord(a) & domain(f)=a   
                    & (\\<Union>b<a. f`b) = A & (\\<forall>b<a. f`b lepoll m))"

  WO7_def "WO7 == \\<forall>A. Finite(A) <-> (\\<forall>R. well_ord(A,R) -->   
                    well_ord(A,converse(R)))"

  WO8_def "WO8 == \\<forall>A. (\\<exists>f. f \\<in> (\\<Pi>X \\<in> A. X)) --> (\\<exists>R. well_ord(A,R))"

(* Axioms of Choice *)  

  AC0_def "AC0 == \\<forall>A. \\<exists>f. f \\<in> (\\<Pi>X \\<in> Pow(A)-{0}. X)"

  AC1_def "AC1 == \\<forall>A. 0\\<notin>A --> (\\<exists>f. f \\<in> (\\<Pi>X \\<in> A. X))"

  AC2_def "AC2 == \\<forall>A. 0\\<notin>A & pairwise_disjoint(A)   
                    --> (\\<exists>C. \\<forall>B \\<in> A. \\<exists>y. B Int C = {y})"

  AC3_def "AC3 == \\<forall>A B. \\<forall>f \\<in> A->B. \\<exists>g. g \\<in> (\\<Pi>x \\<in> {a \\<in> A. f`a\\<noteq>0}. f`x)"

  AC4_def "AC4 == \\<forall>R A B. (R \\<subseteq> A*B --> (\\<exists>f. f \\<in> (\\<Pi>x \\<in> domain(R). R``{x})))"

  AC5_def "AC5 == \\<forall>A B. \\<forall>f \\<in> A->B. \\<exists>g \\<in> range(f)->A.   
                    \\<forall>x \\<in> domain(g). f`(g`x) = x"

  AC6_def "AC6 == \\<forall>A. 0\\<notin>A --> (\\<Pi>B \\<in> A. B)\\<noteq>0"

  AC7_def "AC7 == \\<forall>A. 0\\<notin>A & (\\<forall>B1 \\<in> A. \\<forall>B2 \\<in> A. B1 eqpoll B2)   
                    --> (\\<Pi>B \\<in> A. B)\\<noteq>0"

  AC8_def "AC8 == \\<forall>A. (\\<forall>B \\<in> A. \\<exists>B1 B2. B=<B1,B2> & B1 eqpoll B2)   
                    --> (\\<exists>f. \\<forall>B \\<in> A. f`B \\<in> bij(fst(B),snd(B)))"

  AC9_def "AC9 == \\<forall>A. (\\<forall>B1 \\<in> A. \\<forall>B2 \\<in> A. B1 eqpoll B2) -->   
                    (\\<exists>f. \\<forall>B1 \\<in> A. \\<forall>B2 \\<in> A. f`<B1,B2> \\<in> bij(B1,B2))"

  AC10_def "AC10(n) ==  \\<forall>A. (\\<forall>B \\<in> A. ~Finite(B)) -->   
                    (\\<exists>f. \\<forall>B \\<in> A. (pairwise_disjoint(f`B) &   
                    sets_of_size_between(f`B, 2, succ(n)) & Union(f`B)=B))"

  AC11_def "AC11 == \\<exists>n \\<in> nat. 1 le n & AC10(n)"

  AC12_def "AC12 == \\<forall>A. (\\<forall>B \\<in> A. ~Finite(B)) -->   
            (\\<exists>n \\<in> nat. 1 le n & (\\<exists>f. \\<forall>B \\<in> A. (pairwise_disjoint(f`B) &   
            sets_of_size_between(f`B, 2, succ(n)) & Union(f`B)=B)))"

  AC13_def "AC13(m) == \\<forall>A. 0\\<notin>A --> (\\<exists>f. \\<forall>B \\<in> A. f`B\\<noteq>0 &   
                                          f`B \\<subseteq> B & f`B lepoll m)"

  AC14_def "AC14 == \\<exists>m \\<in> nat. 1 le m & AC13(m)"

  AC15_def "AC15 == \\<forall>A. 0\\<notin>A --> (\\<exists>m \\<in> nat. 1 le m & (\\<exists>f. \\<forall>B \\<in> A.   
                                      f`B\\<noteq>0 & f`B \\<subseteq> B & f`B lepoll m))"

  AC16_def "AC16(n, k)  == \\<forall>A. ~Finite(A) -->   
            (\\<exists>T. T \\<subseteq> {X \\<in> Pow(A). X eqpoll succ(n)} &   
            (\\<forall>X \\<in> {X \\<in> Pow(A). X eqpoll succ(k)}. \\<exists>! Y. Y \\<in> T & X \\<subseteq> Y))"

  AC17_def "AC17 == \\<forall>A. \\<forall>g \\<in> (Pow(A)-{0} -> A) -> Pow(A)-{0}.   
                    \\<exists>f \\<in> Pow(A)-{0} -> A. f`(g`f) \\<in> g`f"

  AC18_def "AC18 == (!!X A B. A\\<noteq>0 & (\\<forall>a \\<in> A. B(a) \\<noteq> 0) -->   
                 ((\\<Inter>a \\<in> A. \\<Union>b \\<in> B(a). X(a,b)) =   
                 (\\<Union>f \\<in> \\<Pi>a \\<in> A. B(a). \\<Inter>a \\<in> A. X(a, f`a))))"

  AC19_def "AC19 == \\<forall>A. A\\<noteq>0 & 0\\<notin>A --> ((\\<Inter>a \\<in> A. \\<Union>b \\<in> a. b) =   
                    (\\<Union>f \\<in> (\\<Pi>B \\<in> A. B). \\<Inter>a \\<in> A. f`a))"

(* Auxiliary definitions used in the above definitions *)

  pairwise_disjoint_def    "pairwise_disjoint(A)   
                            == \\<forall>A1 \\<in> A. \\<forall>A2 \\<in> A. A1 Int A2 \\<noteq> 0 --> A1=A2"

  sets_of_size_between_def "sets_of_size_between(A,m,n)   
                            == \\<forall>B \\<in> A. m lepoll B & B lepoll n"
  
end
