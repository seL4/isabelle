(*$Id$*)

header{*Theory Main: Everything Except AC*}

theory Main = List + IntDiv + CardinalArith:

(*The theory of "iterates" logically belongs to Nat, but can't go there because
  primrec isn't available into after Datatype.  The only theories defined
  after Datatype are List and the Integ theories.*)
subsection{* Iteration of the function @{term F} *}

consts  iterates :: "[i=>i,i,i] => i"   ("(_^_ '(_'))" [60,1000,1000] 60)

primrec
    "F^0 (x) = x"
    "F^(succ(n)) (x) = F(F^n (x))"

constdefs
  iterates_omega :: "[i=>i,i] => i"
    "iterates_omega(F,x) == \<Union>n\<in>nat. F^n (x)"

syntax (xsymbols)
  iterates_omega :: "[i=>i,i] => i"   ("(_^\<omega> '(_'))" [60,1000] 60)

lemma iterates_triv:
     "[| n\<in>nat;  F(x) = x |] ==> F^n (x) = x"  
by (induct n rule: nat_induct, simp_all)

lemma iterates_type [TC]:
     "[| n:nat;  a: A; !!x. x:A ==> F(x) : A |] 
      ==> F^n (a) : A"  
by (induct n rule: nat_induct, simp_all)

lemma iterates_omega_triv:
    "F(x) = x ==> F^\<omega> (x) = x" 
by (simp add: iterates_omega_def iterates_triv) 

lemma Ord_iterates [simp]:
     "[| n\<in>nat;  !!i. Ord(i) ==> Ord(F(i));  Ord(x) |] 
      ==> Ord(F^n (x))"  
by (induct n rule: nat_induct, simp_all)

lemma iterates_commute: "n \<in> nat ==> F(F^n (x)) = F^n (F(x))"
by (induct_tac n, simp_all)


subsection{* Transfinite Recursion *}

text{*Transfinite recursion for definitions based on the 
    three cases of ordinals*}

constdefs
  transrec3 :: "[i, i, [i,i]=>i, [i,i]=>i] =>i"
    "transrec3(k, a, b, c) ==                     
       transrec(k, \<lambda>x r.
         if x=0 then a
         else if Limit(x) then c(x, \<lambda>y\<in>x. r`y)
         else b(Arith.pred(x), r ` Arith.pred(x)))"

lemma transrec3_0 [simp]: "transrec3(0,a,b,c) = a"
by (rule transrec3_def [THEN def_transrec, THEN trans], simp)

lemma transrec3_succ [simp]:
     "transrec3(succ(i),a,b,c) = b(i, transrec3(i,a,b,c))"
by (rule transrec3_def [THEN def_transrec, THEN trans], simp)

lemma transrec3_Limit:
     "Limit(i) ==> 
      transrec3(i,a,b,c) = c(i, \<lambda>j\<in>i. transrec3(j,a,b,c))"
by (rule transrec3_def [THEN def_transrec, THEN trans], force)


subsection{* Remaining Declarations *}

(* belongs to theory IntDiv *)
lemmas posDivAlg_induct = posDivAlg_induct [consumes 2]
  and negDivAlg_induct = negDivAlg_induct [consumes 2]


end
