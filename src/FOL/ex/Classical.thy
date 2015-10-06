(*  Title:      FOL/ex/Classical.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge
*)

section\<open>Classical Predicate Calculus Problems\<close>

theory Classical imports FOL begin

lemma "(P --> Q | R) --> (P-->Q) | (P-->R)"
by blast

text\<open>If and only if\<close>

lemma "(P<->Q) <-> (Q<->P)"
by blast

lemma "~ (P <-> ~P)"
by blast


text\<open>Sample problems from 
  F. J. Pelletier, 
  Seventy-Five Problems for Testing Automatic Theorem Provers,
  J. Automated Reasoning 2 (1986), 191-216.
  Errata, JAR 4 (1988), 236-236.

The hardest problems -- judging by experience with several theorem provers,
including matrix ones -- are 34 and 43.
\<close>

subsection\<open>Pelletier's examples\<close>

text\<open>1\<close>
lemma "(P-->Q)  <->  (~Q --> ~P)"
by blast

text\<open>2\<close>
lemma "~ ~ P  <->  P"
by blast

text\<open>3\<close>
lemma "~(P-->Q) --> (Q-->P)"
by blast

text\<open>4\<close>
lemma "(~P-->Q)  <->  (~Q --> P)"
by blast

text\<open>5\<close>
lemma "((P|Q)-->(P|R)) --> (P|(Q-->R))"
by blast

text\<open>6\<close>
lemma "P | ~ P"
by blast

text\<open>7\<close>
lemma "P | ~ ~ ~ P"
by blast

text\<open>8.  Peirce's law\<close>
lemma "((P-->Q) --> P)  -->  P"
by blast

text\<open>9\<close>
lemma "((P|Q) & (~P|Q) & (P| ~Q)) --> ~ (~P | ~Q)"
by blast

text\<open>10\<close>
lemma "(Q-->R) & (R-->P&Q) & (P-->Q|R) --> (P<->Q)"
by blast

text\<open>11.  Proved in each direction (incorrectly, says Pelletier!!)\<close>
lemma "P<->P"
by blast

text\<open>12.  "Dijkstra's law"\<close>
lemma "((P <-> Q) <-> R)  <->  (P <-> (Q <-> R))"
by blast

text\<open>13.  Distributive law\<close>
lemma "P | (Q & R)  <-> (P | Q) & (P | R)"
by blast

text\<open>14\<close>
lemma "(P <-> Q) <-> ((Q | ~P) & (~Q|P))"
by blast

text\<open>15\<close>
lemma "(P --> Q) <-> (~P | Q)"
by blast

text\<open>16\<close>
lemma "(P-->Q) | (Q-->P)"
by blast

text\<open>17\<close>
lemma "((P & (Q-->R))-->S) <-> ((~P | Q | S) & (~P | ~R | S))"
by blast

subsection\<open>Classical Logic: examples with quantifiers\<close>

lemma "(\<forall>x. P(x) & Q(x)) <-> (\<forall>x. P(x))  &  (\<forall>x. Q(x))"
by blast

lemma "(\<exists>x. P-->Q(x))  <->  (P --> (\<exists>x. Q(x)))"
by blast

lemma "(\<exists>x. P(x)-->Q)  <->  (\<forall>x. P(x)) --> Q"
by blast

lemma "(\<forall>x. P(x)) | Q  <->  (\<forall>x. P(x) | Q)"
by blast

text\<open>Discussed in Avron, Gentzen-Type Systems, Resolution and Tableaux,
  JAR 10 (265-281), 1993.  Proof is trivial!\<close>
lemma "~((\<exists>x.~P(x)) & ((\<exists>x. P(x)) | (\<exists>x. P(x) & Q(x))) & ~ (\<exists>x. P(x)))"
by blast

subsection\<open>Problems requiring quantifier duplication\<close>

text\<open>Theorem B of Peter Andrews, Theorem Proving via General Matings, 
  JACM 28 (1981).\<close>
lemma "(\<exists>x. \<forall>y. P(x) <-> P(y)) --> ((\<exists>x. P(x)) <-> (\<forall>y. P(y)))"
by blast

text\<open>Needs multiple instantiation of ALL.\<close>
lemma "(\<forall>x. P(x)-->P(f(x)))  &  P(d)-->P(f(f(f(d))))"
by blast

text\<open>Needs double instantiation of the quantifier\<close>
lemma "\<exists>x. P(x) --> P(a) & P(b)"
by blast

lemma "\<exists>z. P(z) --> (\<forall>x. P(x))"
by blast

lemma "\<exists>x. (\<exists>y. P(y)) --> P(x)"
by blast

text\<open>V. Lifschitz, What Is the Inverse Method?, JAR 5 (1989), 1--23.  NOT PROVED\<close>
lemma "\<exists>x x'. \<forall>y. \<exists>z z'.  
                (~P(y,y) | P(x,x) | ~S(z,x)) &  
                (S(x,y) | ~S(y,z) | Q(z',z'))  &  
                (Q(x',y) | ~Q(y,z') | S(x',x'))"
oops



subsection\<open>Hard examples with quantifiers\<close>

text\<open>18\<close>
lemma "\<exists>y. \<forall>x. P(y)-->P(x)"
by blast

text\<open>19\<close>
lemma "\<exists>x. \<forall>y z. (P(y)-->Q(z)) --> (P(x)-->Q(x))"
by blast

text\<open>20\<close>
lemma "(\<forall>x y. \<exists>z. \<forall>w. (P(x)&Q(y)-->R(z)&S(w)))      
    --> (\<exists>x y. P(x) & Q(y)) --> (\<exists>z. R(z))"
by blast

text\<open>21\<close>
lemma "(\<exists>x. P-->Q(x)) & (\<exists>x. Q(x)-->P) --> (\<exists>x. P<->Q(x))"
by blast

text\<open>22\<close>
lemma "(\<forall>x. P <-> Q(x))  -->  (P <-> (\<forall>x. Q(x)))"
by blast

text\<open>23\<close>
lemma "(\<forall>x. P | Q(x))  <->  (P | (\<forall>x. Q(x)))"
by blast

text\<open>24\<close>
lemma "~(\<exists>x. S(x)&Q(x)) & (\<forall>x. P(x) --> Q(x)|R(x)) &   
      (~(\<exists>x. P(x)) --> (\<exists>x. Q(x))) & (\<forall>x. Q(x)|R(x) --> S(x))   
    --> (\<exists>x. P(x)&R(x))"
by blast

text\<open>25\<close>
lemma "(\<exists>x. P(x)) &   
      (\<forall>x. L(x) --> ~ (M(x) & R(x))) &   
      (\<forall>x. P(x) --> (M(x) & L(x))) &    
      ((\<forall>x. P(x)-->Q(x)) | (\<exists>x. P(x)&R(x)))   
    --> (\<exists>x. Q(x)&P(x))"
by blast

text\<open>26\<close>
lemma "((\<exists>x. p(x)) <-> (\<exists>x. q(x))) &  
      (\<forall>x. \<forall>y. p(x) & q(y) --> (r(x) <-> s(y)))    
  --> ((\<forall>x. p(x)-->r(x)) <-> (\<forall>x. q(x)-->s(x)))"
by blast

text\<open>27\<close>
lemma "(\<exists>x. P(x) & ~Q(x)) &    
      (\<forall>x. P(x) --> R(x)) &    
      (\<forall>x. M(x) & L(x) --> P(x)) &    
      ((\<exists>x. R(x) & ~ Q(x)) --> (\<forall>x. L(x) --> ~ R(x)))   
  --> (\<forall>x. M(x) --> ~L(x))"
by blast

text\<open>28.  AMENDED\<close>
lemma "(\<forall>x. P(x) --> (\<forall>x. Q(x))) &    
        ((\<forall>x. Q(x)|R(x)) --> (\<exists>x. Q(x)&S(x))) &   
        ((\<exists>x. S(x)) --> (\<forall>x. L(x) --> M(x)))   
    --> (\<forall>x. P(x) & L(x) --> M(x))"
by blast

text\<open>29.  Essentially the same as Principia Mathematica *11.71\<close>
lemma "(\<exists>x. P(x)) & (\<exists>y. Q(y))   
    --> ((\<forall>x. P(x)-->R(x)) & (\<forall>y. Q(y)-->S(y))   <->      
         (\<forall>x y. P(x) & Q(y) --> R(x) & S(y)))"
by blast

text\<open>30\<close>
lemma "(\<forall>x. P(x) | Q(x) --> ~ R(x)) &  
      (\<forall>x. (Q(x) --> ~ S(x)) --> P(x) & R(x))   
    --> (\<forall>x. S(x))"
by blast

text\<open>31\<close>
lemma "~(\<exists>x. P(x) & (Q(x) | R(x))) &  
        (\<exists>x. L(x) & P(x)) &  
        (\<forall>x. ~ R(x) --> M(x))   
    --> (\<exists>x. L(x) & M(x))"
by blast

text\<open>32\<close>
lemma "(\<forall>x. P(x) & (Q(x)|R(x))-->S(x)) &  
      (\<forall>x. S(x) & R(x) --> L(x)) &  
      (\<forall>x. M(x) --> R(x))   
      --> (\<forall>x. P(x) & M(x) --> L(x))"
by blast

text\<open>33\<close>
lemma "(\<forall>x. P(a) & (P(x)-->P(b))-->P(c))  <->     
      (\<forall>x. (~P(a) | P(x) | P(c)) & (~P(a) | ~P(b) | P(c)))"
by blast

text\<open>34  AMENDED (TWICE!!).  Andrews's challenge\<close>
lemma "((\<exists>x. \<forall>y. p(x) <-> p(y))  <->                 
       ((\<exists>x. q(x)) <-> (\<forall>y. p(y))))     <->         
      ((\<exists>x. \<forall>y. q(x) <-> q(y))  <->                 
       ((\<exists>x. p(x)) <-> (\<forall>y. q(y))))"
by blast

text\<open>35\<close>
lemma "\<exists>x y. P(x,y) -->  (\<forall>u v. P(u,v))"
by blast

text\<open>36\<close>
lemma "(\<forall>x. \<exists>y. J(x,y)) &  
      (\<forall>x. \<exists>y. G(x,y)) &  
      (\<forall>x y. J(x,y) | G(x,y) --> (\<forall>z. J(y,z) | G(y,z) --> H(x,z)))    
  --> (\<forall>x. \<exists>y. H(x,y))"
by blast

text\<open>37\<close>
lemma "(\<forall>z. \<exists>w. \<forall>x. \<exists>y.  
           (P(x,z)-->P(y,w)) & P(y,z) & (P(y,w) --> (\<exists>u. Q(u,w)))) &  
      (\<forall>x z. ~P(x,z) --> (\<exists>y. Q(y,z))) &  
      ((\<exists>x y. Q(x,y)) --> (\<forall>x. R(x,x)))   
      --> (\<forall>x. \<exists>y. R(x,y))"
by blast

text\<open>38\<close>
lemma "(\<forall>x. p(a) & (p(x) --> (\<exists>y. p(y) & r(x,y))) -->         
             (\<exists>z. \<exists>w. p(z) & r(x,w) & r(w,z)))  <->          
      (\<forall>x. (~p(a) | p(x) | (\<exists>z. \<exists>w. p(z) & r(x,w) & r(w,z))) &     
              (~p(a) | ~(\<exists>y. p(y) & r(x,y)) |                           
              (\<exists>z. \<exists>w. p(z) & r(x,w) & r(w,z))))"
by blast

text\<open>39\<close>
lemma "~ (\<exists>x. \<forall>y. F(y,x) <-> ~F(y,y))"
by blast

text\<open>40.  AMENDED\<close>
lemma "(\<exists>y. \<forall>x. F(x,y) <-> F(x,x)) -->   
              ~(\<forall>x. \<exists>y. \<forall>z. F(z,y) <-> ~ F(z,x))"
by blast

text\<open>41\<close>
lemma "(\<forall>z. \<exists>y. \<forall>x. f(x,y) <-> f(x,z) & ~ f(x,x))         
          --> ~ (\<exists>z. \<forall>x. f(x,z))"
by blast

text\<open>42\<close>
lemma "~ (\<exists>y. \<forall>x. p(x,y) <-> ~ (\<exists>z. p(x,z) & p(z,x)))"
by blast

text\<open>43\<close>
lemma "(\<forall>x. \<forall>y. q(x,y) <-> (\<forall>z. p(z,x) <-> p(z,y)))      
          --> (\<forall>x. \<forall>y. q(x,y) <-> q(y,x))"
by blast

(*Other proofs: Can use auto, which cheats by using rewriting!  
  Deepen_tac alone requires 253 secs.  Or
  by (mini_tac @{context} 1 THEN Deepen_tac 5 1) *)

text\<open>44\<close>
lemma "(\<forall>x. f(x) --> (\<exists>y. g(y) & h(x,y) & (\<exists>y. g(y) & ~ h(x,y)))) &  
      (\<exists>x. j(x) & (\<forall>y. g(y) --> h(x,y)))                    
      --> (\<exists>x. j(x) & ~f(x))"
by blast

text\<open>45\<close>
lemma "(\<forall>x. f(x) & (\<forall>y. g(y) & h(x,y) --> j(x,y))   
                      --> (\<forall>y. g(y) & h(x,y) --> k(y))) &     
      ~ (\<exists>y. l(y) & k(y)) &                                    
      (\<exists>x. f(x) & (\<forall>y. h(x,y) --> l(y))                     
                  & (\<forall>y. g(y) & h(x,y) --> j(x,y)))           
      --> (\<exists>x. f(x) & ~ (\<exists>y. g(y) & h(x,y)))"
by blast


text\<open>46\<close>
lemma "(\<forall>x. f(x) & (\<forall>y. f(y) & h(y,x) --> g(y)) --> g(x)) &       
      ((\<exists>x. f(x) & ~g(x)) -->                                     
       (\<exists>x. f(x) & ~g(x) & (\<forall>y. f(y) & ~g(y) --> j(x,y)))) &     
      (\<forall>x y. f(x) & f(y) & h(x,y) --> ~j(y,x))                     
       --> (\<forall>x. f(x) --> g(x))"
by blast


subsection\<open>Problems (mainly) involving equality or functions\<close>

text\<open>48\<close>
lemma "(a=b | c=d) & (a=c | b=d) --> a=d | b=c"
by blast

text\<open>49  NOT PROVED AUTOMATICALLY.  Hard because it involves substitution
  for Vars
  the type constraint ensures that x,y,z have the same type as a,b,u.\<close>
lemma "(\<exists>x y::'a. \<forall>z. z=x | z=y) & P(a) & P(b) & a~=b  
                --> (\<forall>u::'a. P(u))"
apply safe
apply (rule_tac x = a in allE, assumption)
apply (rule_tac x = b in allE, assumption, fast)
       --\<open>blast's treatment of equality can't do it\<close>
done

text\<open>50.  (What has this to do with equality?)\<close>
lemma "(\<forall>x. P(a,x) | (\<forall>y. P(x,y))) --> (\<exists>x. \<forall>y. P(x,y))"
by blast

text\<open>51\<close>
lemma "(\<exists>z w. \<forall>x y. P(x,y) <->  (x=z & y=w)) -->   
      (\<exists>z. \<forall>x. \<exists>w. (\<forall>y. P(x,y) <-> y=w) <-> x=z)"
by blast

text\<open>52\<close>
text\<open>Almost the same as 51.\<close>
lemma "(\<exists>z w. \<forall>x y. P(x,y) <->  (x=z & y=w)) -->   
      (\<exists>w. \<forall>y. \<exists>z. (\<forall>x. P(x,y) <-> x=z) <-> y=w)"
by blast

text\<open>55\<close>

text\<open>Non-equational version, from Manthey and Bry, CADE-9 (Springer, 1988).
  fast DISCOVERS who killed Agatha.\<close>
schematic_goal "lives(agatha) & lives(butler) & lives(charles) &  
   (killed(agatha,agatha) | killed(butler,agatha) | killed(charles,agatha)) &  
   (\<forall>x y. killed(x,y) --> hates(x,y) & ~richer(x,y)) &  
   (\<forall>x. hates(agatha,x) --> ~hates(charles,x)) &  
   (hates(agatha,agatha) & hates(agatha,charles)) &  
   (\<forall>x. lives(x) & ~richer(x,agatha) --> hates(butler,x)) &  
   (\<forall>x. hates(agatha,x) --> hates(butler,x)) &  
   (\<forall>x. ~hates(x,agatha) | ~hates(x,butler) | ~hates(x,charles)) -->  
    killed(?who,agatha)"
by fast --\<open>MUCH faster than blast\<close>


text\<open>56\<close>
lemma "(\<forall>x. (\<exists>y. P(y) & x=f(y)) --> P(x)) <-> (\<forall>x. P(x) --> P(f(x)))"
by blast

text\<open>57\<close>
lemma "P(f(a,b), f(b,c)) & P(f(b,c), f(a,c)) &  
     (\<forall>x y z. P(x,y) & P(y,z) --> P(x,z))    -->   P(f(a,b), f(a,c))"
by blast

text\<open>58  NOT PROVED AUTOMATICALLY\<close>
lemma "(\<forall>x y. f(x)=g(y)) --> (\<forall>x y. f(f(x))=f(g(y)))"
by (slow elim: subst_context)


text\<open>59\<close>
lemma "(\<forall>x. P(x) <-> ~P(f(x))) --> (\<exists>x. P(x) & ~P(f(x)))"
by blast

text\<open>60\<close>
lemma "\<forall>x. P(x,f(x)) <-> (\<exists>y. (\<forall>z. P(z,y) --> P(z,f(x))) & P(x,y))"
by blast

text\<open>62 as corrected in JAR 18 (1997), page 135\<close>
lemma "(\<forall>x. p(a) & (p(x) --> p(f(x))) --> p(f(f(x))))  <->      
      (\<forall>x. (~p(a) | p(x) | p(f(f(x)))) &                       
              (~p(a) | ~p(f(x)) | p(f(f(x)))))"
by blast

text\<open>From Davis, Obvious Logical Inferences, IJCAI-81, 530-531
  fast indeed copes!\<close>
lemma "(\<forall>x. F(x) & ~G(x) --> (\<exists>y. H(x,y) & J(y))) &  
              (\<exists>x. K(x) & F(x) & (\<forall>y. H(x,y) --> K(y))) &    
              (\<forall>x. K(x) --> ~G(x))  -->  (\<exists>x. K(x) & J(x))"
by fast

text\<open>From Rudnicki, Obvious Inferences, JAR 3 (1987), 383-393.  
  It does seem obvious!\<close>
lemma "(\<forall>x. F(x) & ~G(x) --> (\<exists>y. H(x,y) & J(y))) &         
      (\<exists>x. K(x) & F(x) & (\<forall>y. H(x,y) --> K(y)))  &         
      (\<forall>x. K(x) --> ~G(x))   -->   (\<exists>x. K(x) --> ~G(x))"
by fast

text\<open>Halting problem: Formulation of Li Dafa (AAR Newsletter 27, Oct 1994.)
  author U. Egly\<close>
lemma "((\<exists>x. A(x) & (\<forall>y. C(y) --> (\<forall>z. D(x,y,z)))) -->                
   (\<exists>w. C(w) & (\<forall>y. C(y) --> (\<forall>z. D(w,y,z)))))                   
  &                                                                      
  (\<forall>w. C(w) & (\<forall>u. C(u) --> (\<forall>v. D(w,u,v))) -->                 
        (\<forall>y z.                                                        
            (C(y) &  P(y,z) --> Q(w,y,z) & OO(w,g)) &                    
            (C(y) & ~P(y,z) --> Q(w,y,z) & OO(w,b))))                    
  &                                                                      
  (\<forall>w. C(w) &                                                         
    (\<forall>y z.                                                            
        (C(y) & P(y,z) --> Q(w,y,z) & OO(w,g)) &                         
        (C(y) & ~P(y,z) --> Q(w,y,z) & OO(w,b))) -->                     
    (\<exists>v. C(v) &                                                        
          (\<forall>y. ((C(y) & Q(w,y,y)) & OO(w,g) --> ~P(v,y)) &            
                  ((C(y) & Q(w,y,y)) & OO(w,b) --> P(v,y) & OO(v,b)))))  
   -->                   
   ~ (\<exists>x. A(x) & (\<forall>y. C(y) --> (\<forall>z. D(x,y,z))))"
by (blast 12)
   --\<open>Needed because the search for depths below 12 is very slow\<close>


text\<open>Halting problem II: credited to M. Bruschi by Li Dafa in JAR 18(1), p.105\<close>
lemma "((\<exists>x. A(x) & (\<forall>y. C(y) --> (\<forall>z. D(x,y,z)))) -->        
   (\<exists>w. C(w) & (\<forall>y. C(y) --> (\<forall>z. D(w,y,z)))))           
  &                                                              
  (\<forall>w. C(w) & (\<forall>u. C(u) --> (\<forall>v. D(w,u,v))) -->         
        (\<forall>y z.                                                
            (C(y) &  P(y,z) --> Q(w,y,z) & OO(w,g)) &           
            (C(y) & ~P(y,z) --> Q(w,y,z) & OO(w,b))))          
  &                                                              
  ((\<exists>w. C(w) & (\<forall>y. (C(y) &  P(y,y) --> Q(w,y,y) & OO(w,g)) & 
                         (C(y) & ~P(y,y) --> Q(w,y,y) & OO(w,b))))  
   -->                                                             
   (\<exists>v. C(v) & (\<forall>y. (C(y) &  P(y,y) --> P(v,y) & OO(v,g)) &   
                         (C(y) & ~P(y,y) --> P(v,y) & OO(v,b)))))  
  -->                                                              
  ((\<exists>v. C(v) & (\<forall>y. (C(y) &  P(y,y) --> P(v,y) & OO(v,g)) &   
                         (C(y) & ~P(y,y) --> P(v,y) & OO(v,b))))   
   -->                                                             
   (\<exists>u. C(u) & (\<forall>y. (C(y) &  P(y,y) --> ~P(u,y)) &     
                         (C(y) & ~P(y,y) --> P(u,y) & OO(u,b)))))  
   -->                                                             
   ~ (\<exists>x. A(x) & (\<forall>y. C(y) --> (\<forall>z. D(x,y,z))))"
by blast

text\<open>Challenge found on info-hol\<close>
lemma "\<forall>x. \<exists>v w. \<forall>y z. P(x) & Q(y) --> (P(v) | R(w)) & (R(z) --> Q(v))"
by blast

text\<open>Attributed to Lewis Carroll by S. G. Pulman.  The first or last assumption
can be deleted.\<close>
lemma "(\<forall>x. honest(x) & industrious(x) --> healthy(x)) &  
      ~ (\<exists>x. grocer(x) & healthy(x)) &  
      (\<forall>x. industrious(x) & grocer(x) --> honest(x)) &  
      (\<forall>x. cyclist(x) --> industrious(x)) &  
      (\<forall>x. ~healthy(x) & cyclist(x) --> ~honest(x))   
      --> (\<forall>x. grocer(x) --> ~cyclist(x))"
by blast


(*Runtimes for old versions of this file:
Thu Jul 23 1992: loaded in 467s using iffE [on SPARC2] 
Mon Nov 14 1994: loaded in 144s [on SPARC10, with deepen_tac] 
Wed Nov 16 1994: loaded in 138s [after addition of norm_term_skip] 
Mon Nov 21 1994: loaded in 131s [DEPTH_FIRST suppressing repetitions] 

Further runtimes on a Sun-4
Tue Mar  4 1997: loaded in 93s (version 94-7) 
Tue Mar  4 1997: loaded in 89s
Thu Apr  3 1997: loaded in 44s--using mostly Blast_tac
Thu Apr  3 1997: loaded in 96s--addition of two Halting Probs
Thu Apr  3 1997: loaded in 98s--using lim-1 for all haz rules
Tue Dec  2 1997: loaded in 107s--added 46; new equalSubst
Fri Dec 12 1997: loaded in 91s--faster proof reconstruction
Thu Dec 18 1997: loaded in 94s--two new "obvious theorems" (??)
*)

end

