(*  Title:      FOLP/ex/Classical.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Classical First-Order Logic.
*)

theory Classical
imports FOLP
begin

schematic_lemma "?p : (P --> Q | R) --> (P-->Q) | (P-->R)"
  by (tactic "fast_tac @{context} FOLP_cs 1")

(*If and only if*)
schematic_lemma "?p : (P<->Q) <-> (Q<->P)"
  by (tactic "fast_tac @{context} FOLP_cs 1")

schematic_lemma "?p : ~ (P <-> ~P)"
  by (tactic "fast_tac @{context} FOLP_cs 1")


(*Sample problems from 
  F. J. Pelletier, 
  Seventy-Five Problems for Testing Automatic Theorem Provers,
  J. Automated Reasoning 2 (1986), 191-216.
  Errata, JAR 4 (1988), 236-236.

The hardest problems -- judging by experience with several theorem provers,
including matrix ones -- are 34 and 43.
*)

text "Pelletier's examples"
(*1*)
schematic_lemma "?p : (P-->Q)  <->  (~Q --> ~P)"
  by (tactic "fast_tac @{context} FOLP_cs 1")

(*2*)
schematic_lemma "?p : ~ ~ P  <->  P"
  by (tactic "fast_tac @{context} FOLP_cs 1")

(*3*)
schematic_lemma "?p : ~(P-->Q) --> (Q-->P)"
  by (tactic "fast_tac @{context} FOLP_cs 1")

(*4*)
schematic_lemma "?p : (~P-->Q)  <->  (~Q --> P)"
  by (tactic "fast_tac @{context} FOLP_cs 1")

(*5*)
schematic_lemma "?p : ((P|Q)-->(P|R)) --> (P|(Q-->R))"
  by (tactic "fast_tac @{context} FOLP_cs 1")

(*6*)
schematic_lemma "?p : P | ~ P"
  by (tactic "fast_tac @{context} FOLP_cs 1")

(*7*)
schematic_lemma "?p : P | ~ ~ ~ P"
  by (tactic "fast_tac @{context} FOLP_cs 1")

(*8.  Peirce's law*)
schematic_lemma "?p : ((P-->Q) --> P)  -->  P"
  by (tactic "fast_tac @{context} FOLP_cs 1")

(*9*)
schematic_lemma "?p : ((P|Q) & (~P|Q) & (P| ~Q)) --> ~ (~P | ~Q)"
  by (tactic "fast_tac @{context} FOLP_cs 1")

(*10*)
schematic_lemma "?p : (Q-->R) & (R-->P&Q) & (P-->Q|R) --> (P<->Q)"
  by (tactic "fast_tac @{context} FOLP_cs 1")

(*11.  Proved in each direction (incorrectly, says Pelletier!!)  *)
schematic_lemma "?p : P<->P"
  by (tactic "fast_tac @{context} FOLP_cs 1")

(*12.  "Dijkstra's law"*)
schematic_lemma "?p : ((P <-> Q) <-> R)  <->  (P <-> (Q <-> R))"
  by (tactic "fast_tac @{context} FOLP_cs 1")

(*13.  Distributive law*)
schematic_lemma "?p : P | (Q & R)  <-> (P | Q) & (P | R)"
  by (tactic "fast_tac @{context} FOLP_cs 1")

(*14*)
schematic_lemma "?p : (P <-> Q) <-> ((Q | ~P) & (~Q|P))"
  by (tactic "fast_tac @{context} FOLP_cs 1")

(*15*)
schematic_lemma "?p : (P --> Q) <-> (~P | Q)"
  by (tactic "fast_tac @{context} FOLP_cs 1")

(*16*)
schematic_lemma "?p : (P-->Q) | (Q-->P)"
  by (tactic "fast_tac @{context} FOLP_cs 1")

(*17*)
schematic_lemma "?p : ((P & (Q-->R))-->S) <-> ((~P | Q | S) & (~P | ~R | S))"
  by (tactic "fast_tac @{context} FOLP_cs 1")


text "Classical Logic: examples with quantifiers"

schematic_lemma "?p : (ALL x. P(x) & Q(x)) <-> (ALL x. P(x))  &  (ALL x. Q(x))"
  by (tactic "fast_tac @{context} FOLP_cs 1")

schematic_lemma "?p : (EX x. P-->Q(x))  <->  (P --> (EX x. Q(x)))"
  by (tactic "fast_tac @{context} FOLP_cs 1")

schematic_lemma "?p : (EX x. P(x)-->Q)  <->  (ALL x. P(x)) --> Q"
  by (tactic "fast_tac @{context} FOLP_cs 1")

schematic_lemma "?p : (ALL x. P(x)) | Q  <->  (ALL x. P(x) | Q)"
  by (tactic "fast_tac @{context} FOLP_cs 1")


text "Problems requiring quantifier duplication"

(*Needs multiple instantiation of ALL.*)
schematic_lemma "?p : (ALL x. P(x)-->P(f(x)))  &  P(d)-->P(f(f(f(d))))"
  by (tactic "best_tac @{context} FOLP_dup_cs 1")

(*Needs double instantiation of the quantifier*)
schematic_lemma "?p : EX x. P(x) --> P(a) & P(b)"
  by (tactic "best_tac @{context} FOLP_dup_cs 1")

schematic_lemma "?p : EX z. P(z) --> (ALL x. P(x))"
  by (tactic "best_tac @{context} FOLP_dup_cs 1")


text "Hard examples with quantifiers"

text "Problem 18"
schematic_lemma "?p : EX y. ALL x. P(y)-->P(x)"
  by (tactic "best_tac @{context} FOLP_dup_cs 1")

text "Problem 19"
schematic_lemma "?p : EX x. ALL y z. (P(y)-->Q(z)) --> (P(x)-->Q(x))"
  by (tactic "best_tac @{context} FOLP_dup_cs 1")

text "Problem 20"
schematic_lemma "?p : (ALL x y. EX z. ALL w. (P(x)&Q(y)-->R(z)&S(w)))      
    --> (EX x y. P(x) & Q(y)) --> (EX z. R(z))"
  by (tactic "fast_tac @{context} FOLP_cs 1")

text "Problem 21"
schematic_lemma "?p : (EX x. P-->Q(x)) & (EX x. Q(x)-->P) --> (EX x. P<->Q(x))"
  by (tactic "best_tac @{context} FOLP_dup_cs 1")

text "Problem 22"
schematic_lemma "?p : (ALL x. P <-> Q(x))  -->  (P <-> (ALL x. Q(x)))"
  by (tactic "fast_tac @{context} FOLP_cs 1")

text "Problem 23"
schematic_lemma "?p : (ALL x. P | Q(x))  <->  (P | (ALL x. Q(x)))"
  by (tactic "best_tac @{context} FOLP_dup_cs 1")

text "Problem 24"
schematic_lemma "?p : ~(EX x. S(x)&Q(x)) & (ALL x. P(x) --> Q(x)|R(x)) &   
     (~(EX x. P(x)) --> (EX x. Q(x))) & (ALL x. Q(x)|R(x) --> S(x))   
    --> (EX x. P(x)&R(x))"
  by (tactic "fast_tac @{context} FOLP_cs 1")

text "Problem 25"
schematic_lemma "?p : (EX x. P(x)) &  
       (ALL x. L(x) --> ~ (M(x) & R(x))) &  
       (ALL x. P(x) --> (M(x) & L(x))) &   
       ((ALL x. P(x)-->Q(x)) | (EX x. P(x)&R(x)))  
   --> (EX x. Q(x)&P(x))"
  oops

text "Problem 26"
schematic_lemma "?u : ((EX x. p(x)) <-> (EX x. q(x))) &   
     (ALL x. ALL y. p(x) & q(y) --> (r(x) <-> s(y)))   
  --> ((ALL x. p(x)-->r(x)) <-> (ALL x. q(x)-->s(x)))"
  by (tactic "fast_tac @{context} FOLP_cs 1")

text "Problem 27"
schematic_lemma "?p : (EX x. P(x) & ~Q(x)) &    
              (ALL x. P(x) --> R(x)) &    
              (ALL x. M(x) & L(x) --> P(x)) &    
              ((EX x. R(x) & ~ Q(x)) --> (ALL x. L(x) --> ~ R(x)))   
          --> (ALL x. M(x) --> ~L(x))"
  by (tactic "fast_tac @{context} FOLP_cs 1")

text "Problem 28.  AMENDED"
schematic_lemma "?p : (ALL x. P(x) --> (ALL x. Q(x))) &    
        ((ALL x. Q(x)|R(x)) --> (EX x. Q(x)&S(x))) &   
        ((EX x. S(x)) --> (ALL x. L(x) --> M(x)))   
    --> (ALL x. P(x) & L(x) --> M(x))"
  by (tactic "fast_tac @{context} FOLP_cs 1")

text "Problem 29.  Essentially the same as Principia Mathematica *11.71"
schematic_lemma "?p : (EX x. P(x)) & (EX y. Q(y))   
    --> ((ALL x. P(x)-->R(x)) & (ALL y. Q(y)-->S(y))   <->      
         (ALL x y. P(x) & Q(y) --> R(x) & S(y)))"
  by (tactic "fast_tac @{context} FOLP_cs 1")

text "Problem 30"
schematic_lemma "?p : (ALL x. P(x) | Q(x) --> ~ R(x)) &  
        (ALL x. (Q(x) --> ~ S(x)) --> P(x) & R(x))   
    --> (ALL x. S(x))"
  by (tactic "fast_tac @{context} FOLP_cs 1")

text "Problem 31"
schematic_lemma "?p : ~(EX x. P(x) & (Q(x) | R(x))) &  
        (EX x. L(x) & P(x)) &  
        (ALL x. ~ R(x) --> M(x))   
    --> (EX x. L(x) & M(x))"
  by (tactic "fast_tac @{context} FOLP_cs 1")

text "Problem 32"
schematic_lemma "?p : (ALL x. P(x) & (Q(x)|R(x))-->S(x)) &  
        (ALL x. S(x) & R(x) --> L(x)) &  
        (ALL x. M(x) --> R(x))   
    --> (ALL x. P(x) & M(x) --> L(x))"
  by (tactic "best_tac @{context} FOLP_dup_cs 1")

text "Problem 33"
schematic_lemma "?p : (ALL x. P(a) & (P(x)-->P(b))-->P(c))  <->     
     (ALL x. (~P(a) | P(x) | P(c)) & (~P(a) | ~P(b) | P(c)))"
  by (tactic "best_tac @{context} FOLP_dup_cs 1")

text "Problem 35"
schematic_lemma "?p : EX x y. P(x,y) -->  (ALL u v. P(u,v))"
  by (tactic "best_tac @{context} FOLP_dup_cs 1")

text "Problem 36"
schematic_lemma
"?p : (ALL x. EX y. J(x,y)) &  
      (ALL x. EX y. G(x,y)) &  
      (ALL x y. J(x,y) | G(x,y) --> (ALL z. J(y,z) | G(y,z) --> H(x,z)))    
  --> (ALL x. EX y. H(x,y))"
  by (tactic "fast_tac @{context} FOLP_cs 1")

text "Problem 37"
schematic_lemma "?p : (ALL z. EX w. ALL x. EX y.  
           (P(x,z)-->P(y,w)) & P(y,z) & (P(y,w) --> (EX u. Q(u,w)))) &  
        (ALL x z. ~P(x,z) --> (EX y. Q(y,z))) &  
        ((EX x y. Q(x,y)) --> (ALL x. R(x,x)))   
    --> (ALL x. EX y. R(x,y))"
  by (tactic "fast_tac @{context} FOLP_cs 1")

text "Problem 39"
schematic_lemma "?p : ~ (EX x. ALL y. F(y,x) <-> ~F(y,y))"
  by (tactic "fast_tac @{context} FOLP_cs 1")

text "Problem 40.  AMENDED"
schematic_lemma "?p : (EX y. ALL x. F(x,y) <-> F(x,x)) -->   
              ~(ALL x. EX y. ALL z. F(z,y) <-> ~ F(z,x))"
  by (tactic "fast_tac @{context} FOLP_cs 1")

text "Problem 41"
schematic_lemma "?p : (ALL z. EX y. ALL x. f(x,y) <-> f(x,z) & ~ f(x,x))   
          --> ~ (EX z. ALL x. f(x,z))"
  by (tactic "best_tac @{context} FOLP_dup_cs 1")

text "Problem 44"
schematic_lemma "?p : (ALL x. f(x) -->                                     
              (EX y. g(y) & h(x,y) & (EX y. g(y) & ~ h(x,y))))  &        
              (EX x. j(x) & (ALL y. g(y) --> h(x,y)))                    
              --> (EX x. j(x) & ~f(x))"
  by (tactic "fast_tac @{context} FOLP_cs 1")

text "Problems (mainly) involving equality or functions"

text "Problem 48"
schematic_lemma "?p : (a=b | c=d) & (a=c | b=d) --> a=d | b=c"
  by (tactic "fast_tac @{context} FOLP_cs 1")

text "Problem 50"
(*What has this to do with equality?*)
schematic_lemma "?p : (ALL x. P(a,x) | (ALL y. P(x,y))) --> (EX x. ALL y. P(x,y))"
  by (tactic "best_tac @{context} FOLP_dup_cs 1")

text "Problem 56"
schematic_lemma
 "?p : (ALL x. (EX y. P(y) & x=f(y)) --> P(x)) <-> (ALL x. P(x) --> P(f(x)))"
  by (tactic "fast_tac @{context} FOLP_cs 1")

text "Problem 57"
schematic_lemma
"?p : P(f(a,b), f(b,c)) & P(f(b,c), f(a,c)) &  
      (ALL x y z. P(x,y) & P(y,z) --> P(x,z))    -->   P(f(a,b), f(a,c))"
  by (tactic "fast_tac @{context} FOLP_cs 1")

text "Problem 58  NOT PROVED AUTOMATICALLY"
schematic_lemma
  notes f_cong = subst_context [where t = f]
  shows "?p : (ALL x y. f(x)=g(y)) --> (ALL x y. f(f(x))=f(g(y)))"
  by (tactic {* fast_tac @{context} (FOLP_cs addSIs [@{thm f_cong}]) 1 *})

text "Problem 59"
schematic_lemma "?p : (ALL x. P(x) <-> ~P(f(x))) --> (EX x. P(x) & ~P(f(x)))"
  by (tactic "best_tac @{context} FOLP_dup_cs 1")

text "Problem 60"
schematic_lemma "?p : ALL x. P(x,f(x)) <-> (EX y. (ALL z. P(z,y) --> P(z,f(x))) & P(x,y))"
  by (tactic "fast_tac @{context} FOLP_cs 1")

end
