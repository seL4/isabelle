(*  Title:      Sequents/LK/Hard_Quantifiers.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Hard examples with quantifiers.  Can be read to test the LK system.
From  F. J. Pelletier,
  Seventy-Five Problems for Testing Automatic Theorem Provers,
  J. Automated Reasoning 2 (1986), 191-216.
  Errata, JAR 4 (1988), 236-236.

Uses pc_tac rather than fast_tac when the former is significantly faster.
*)

theory Hard_Quantifiers
imports LK
begin

lemma "|- (ALL x. P(x) & Q(x)) <-> (ALL x. P(x))  &  (ALL x. Q(x))"
  by fast

lemma "|- (EX x. P-->Q(x))  <->  (P --> (EX x. Q(x)))"
  by fast

lemma "|- (EX x. P(x)-->Q)  <->  (ALL x. P(x)) --> Q"
  by fast

lemma "|- (ALL x. P(x)) | Q  <->  (ALL x. P(x) | Q)"
  by fast


text "Problems requiring quantifier duplication"

(*Not provable by fast: needs multiple instantiation of ALL*)
lemma "|- (ALL x. P(x)-->P(f(x)))  &  P(d)-->P(f(f(f(d))))"
  by best_dup

(*Needs double instantiation of the quantifier*)
lemma "|- EX x. P(x) --> P(a) & P(b)"
  by fast_dup

lemma "|- EX z. P(z) --> (ALL x. P(x))"
  by best_dup


text "Hard examples with quantifiers"

text "Problem 18"
lemma "|- EX y. ALL x. P(y)-->P(x)"
  by best_dup

text "Problem 19"
lemma "|- EX x. ALL y z. (P(y)-->Q(z)) --> (P(x)-->Q(x))"
  by best_dup

text "Problem 20"
lemma "|- (ALL x y. EX z. ALL w. (P(x)&Q(y)-->R(z)&S(w)))      
    --> (EX x y. P(x) & Q(y)) --> (EX z. R(z))"
  by fast

text "Problem 21"
lemma "|- (EX x. P-->Q(x)) & (EX x. Q(x)-->P) --> (EX x. P<->Q(x))"
  by best_dup

text "Problem 22"
lemma "|- (ALL x. P <-> Q(x))  -->  (P <-> (ALL x. Q(x)))"
  by fast

text "Problem 23"
lemma "|- (ALL x. P | Q(x))  <->  (P | (ALL x. Q(x)))"
  by best

text "Problem 24"
lemma "|- ~(EX x. S(x)&Q(x)) & (ALL x. P(x) --> Q(x)|R(x)) &   
     ~(EX x. P(x)) --> (EX x. Q(x)) & (ALL x. Q(x)|R(x) --> S(x))   
    --> (EX x. P(x)&R(x))"
  by pc

text "Problem 25"
lemma "|- (EX x. P(x)) &   
        (ALL x. L(x) --> ~ (M(x) & R(x))) &   
        (ALL x. P(x) --> (M(x) & L(x))) &    
        ((ALL x. P(x)-->Q(x)) | (EX x. P(x)&R(x)))   
    --> (EX x. Q(x)&P(x))"
  by best

text "Problem 26"
lemma "|- ((EX x. p(x)) <-> (EX x. q(x))) &        
      (ALL x. ALL y. p(x) & q(y) --> (r(x) <-> s(y)))    
  --> ((ALL x. p(x)-->r(x)) <-> (ALL x. q(x)-->s(x)))"
  by pc

text "Problem 27"
lemma "|- (EX x. P(x) & ~Q(x)) &    
              (ALL x. P(x) --> R(x)) &    
              (ALL x. M(x) & L(x) --> P(x)) &    
              ((EX x. R(x) & ~ Q(x)) --> (ALL x. L(x) --> ~ R(x)))   
          --> (ALL x. M(x) --> ~L(x))"
  by pc

text "Problem 28.  AMENDED"
lemma "|- (ALL x. P(x) --> (ALL x. Q(x))) &    
        ((ALL x. Q(x)|R(x)) --> (EX x. Q(x)&S(x))) &   
        ((EX x. S(x)) --> (ALL x. L(x) --> M(x)))   
    --> (ALL x. P(x) & L(x) --> M(x))"
  by pc

text "Problem 29.  Essentially the same as Principia Mathematica *11.71"
lemma "|- (EX x. P(x)) & (EX y. Q(y))   
    --> ((ALL x. P(x)-->R(x)) & (ALL y. Q(y)-->S(y))   <->      
         (ALL x y. P(x) & Q(y) --> R(x) & S(y)))"
  by pc

text "Problem 30"
lemma "|- (ALL x. P(x) | Q(x) --> ~ R(x)) &  
        (ALL x. (Q(x) --> ~ S(x)) --> P(x) & R(x))   
    --> (ALL x. S(x))"
  by fast

text "Problem 31"
lemma "|- ~(EX x. P(x) & (Q(x) | R(x))) &  
        (EX x. L(x) & P(x)) &  
        (ALL x. ~ R(x) --> M(x))   
    --> (EX x. L(x) & M(x))"
  by fast

text "Problem 32"
lemma "|- (ALL x. P(x) & (Q(x)|R(x))-->S(x)) &  
        (ALL x. S(x) & R(x) --> L(x)) &  
        (ALL x. M(x) --> R(x))   
    --> (ALL x. P(x) & M(x) --> L(x))"
  by best

text "Problem 33"
lemma "|- (ALL x. P(a) & (P(x)-->P(b))-->P(c))  <->     
     (ALL x. (~P(a) | P(x) | P(c)) & (~P(a) | ~P(b) | P(c)))"
  by fast

text "Problem 34  AMENDED (TWICE!!)"
(*Andrews's challenge*)
lemma "|- ((EX x. ALL y. p(x) <-> p(y))  <->               
               ((EX x. q(x)) <-> (ALL y. p(y))))     <->         
              ((EX x. ALL y. q(x) <-> q(y))  <->                 
               ((EX x. p(x)) <-> (ALL y. q(y))))"
  by best_dup

text "Problem 35"
lemma "|- EX x y. P(x,y) -->  (ALL u v. P(u,v))"
  by best_dup

text "Problem 36"
lemma "|- (ALL x. EX y. J(x,y)) &  
         (ALL x. EX y. G(x,y)) &  
         (ALL x y. J(x,y) | G(x,y) -->    
         (ALL z. J(y,z) | G(y,z) --> H(x,z)))    
         --> (ALL x. EX y. H(x,y))"
  by fast

text "Problem 37"
lemma "|- (ALL z. EX w. ALL x. EX y.  
           (P(x,z)-->P(y,w)) & P(y,z) & (P(y,w) --> (EX u. Q(u,w)))) &  
        (ALL x z. ~P(x,z) --> (EX y. Q(y,z))) &  
        ((EX x y. Q(x,y)) --> (ALL x. R(x,x)))   
    --> (ALL x. EX y. R(x,y))"
  by pc

text "Problem 38"
lemma "|- (ALL x. p(a) & (p(x) --> (EX y. p(y) & r(x,y))) -->         
                 (EX z. EX w. p(z) & r(x,w) & r(w,z)))  <->          
         (ALL x. (~p(a) | p(x) | (EX z. EX w. p(z) & r(x,w) & r(w,z))) &     
                 (~p(a) | ~(EX y. p(y) & r(x,y)) |                           
                 (EX z. EX w. p(z) & r(x,w) & r(w,z))))"
  by pc

text "Problem 39"
lemma "|- ~ (EX x. ALL y. F(y,x) <-> ~F(y,y))"
  by fast

text "Problem 40.  AMENDED"
lemma "|- (EX y. ALL x. F(x,y) <-> F(x,x)) -->   
         ~(ALL x. EX y. ALL z. F(z,y) <-> ~ F(z,x))"
  by fast

text "Problem 41"
lemma "|- (ALL z. EX y. ALL x. f(x,y) <-> f(x,z) & ~ f(x,x))       
         --> ~ (EX z. ALL x. f(x,z))"
  by fast

text "Problem 42"
lemma "|- ~ (EX y. ALL x. p(x,y) <-> ~ (EX z. p(x,z) & p(z,x)))"
  oops

text "Problem 43"
lemma "|- (ALL x. ALL y. q(x,y) <-> (ALL z. p(z,x) <-> p(z,y)))  
          --> (ALL x. (ALL y. q(x,y) <-> q(y,x)))"
  oops

text "Problem 44"
lemma "|- (ALL x. f(x) -->                                         
                 (EX y. g(y) & h(x,y) & (EX y. g(y) & ~ h(x,y))))  &        
         (EX x. j(x) & (ALL y. g(y) --> h(x,y)))                    
         --> (EX x. j(x) & ~f(x))"
  by fast

text "Problem 45"
lemma "|- (ALL x. f(x) & (ALL y. g(y) & h(x,y) --> j(x,y))         
                      --> (ALL y. g(y) & h(x,y) --> k(y))) &     
      ~ (EX y. l(y) & k(y)) &                                    
      (EX x. f(x) & (ALL y. h(x,y) --> l(y))                     
                   & (ALL y. g(y) & h(x,y) --> j(x,y)))          
      --> (EX x. f(x) & ~ (EX y. g(y) & h(x,y)))"
  by best


text "Problems (mainly) involving equality or functions"

text "Problem 48"
lemma "|- (a=b | c=d) & (a=c | b=d) --> a=d | b=c"
  by (fast add!: subst)

text "Problem 50"
lemma "|- (ALL x. P(a,x) | (ALL y. P(x,y))) --> (EX x. ALL y. P(x,y))"
  by best_dup

text "Problem 51"
lemma "|- (EX z w. ALL x y. P(x,y) <->  (x=z & y=w)) -->   
         (EX z. ALL x. EX w. (ALL y. P(x,y) <-> y=w) <-> x=z)"
  by (fast add!: subst)

text "Problem 52"  (*Almost the same as 51. *)
lemma "|- (EX z w. ALL x y. P(x,y) <->  (x=z & y=w)) -->
         (EX w. ALL y. EX z. (ALL x. P(x,y) <-> x=z) <-> y=w)"
  by (fast add!: subst)

text "Problem 56"
lemma "|- (ALL x.(EX y. P(y) & x=f(y)) --> P(x)) <-> (ALL x. P(x) --> P(f(x)))"
  by (best add: symL subst)
  (*requires tricker to orient the equality properly*)

text "Problem 57"
lemma "|- P(f(a,b), f(b,c)) & P(f(b,c), f(a,c)) &  
         (ALL x y z. P(x,y) & P(y,z) --> P(x,z))    -->   P(f(a,b), f(a,c))"
  by fast

text "Problem 58!"
lemma "|- (ALL x y. f(x)=g(y)) --> (ALL x y. f(f(x))=f(g(y)))"
  by (fast add!: subst)

text "Problem 59"
(*Unification works poorly here -- the abstraction %sobj prevents efficient
  operation of the occurs check*)

lemma "|- (ALL x. P(x) <-> ~P(f(x))) --> (EX x. P(x) & ~P(f(x)))"
  by best_dup

text "Problem 60"
lemma "|- ALL x. P(x,f(x)) <-> (EX y. (ALL z. P(z,y) --> P(z,f(x))) & P(x,y))"
  by fast

text "Problem 62 as corrected in JAR 18 (1997), page 135"
lemma "|- (ALL x. p(a) & (p(x) --> p(f(x))) --> p(f(f(x))))  <->
      (ALL x. (~p(a) | p(x) | p(f(f(x)))) &                       
              (~p(a) | ~p(f(x)) | p(f(f(x)))))"
  by fast

(*18 June 92: loaded in 372 secs*)
(*19 June 92: loaded in 166 secs except #34, using repeat_goal_tac*)
(*29 June 92: loaded in 370 secs*)
(*18 September 2005: loaded in 1.809 secs*)

end
