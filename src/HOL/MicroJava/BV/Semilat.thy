(*  Title:      HOL/BCV/Semilat.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TUM

Semilattices
*)

header "Semilattices"

theory Semilat = Main:

types 'a ord    = "'a => 'a => bool"
      'a binop  = "'a => 'a => 'a"
      'a sl     = "'a set * 'a ord * 'a binop"

consts
 "@lesub"   :: "'a => 'a ord => 'a => bool" ("(_ /<='__ _)" [50, 1000, 51] 50)
 "@lesssub" :: "'a => 'a ord => 'a => bool" ("(_ /<'__ _)" [50, 1000, 51] 50)
defs
lesub_def:   "x <=_r y == r x y"
lesssub_def: "x <_r y  == x <=_r y & x ~= y"

consts
 "@plussub" :: "'a => ('a => 'b => 'c) => 'b => 'c" ("(_ /+'__ _)" [65, 1000, 66] 65)
defs
plussub_def: "x +_f y == f x y"


constdefs
 ord :: "('a*'a)set => 'a ord"
"ord r == %x y. (x,y):r"

 order :: "'a ord => bool"
"order r == (!x. x <=_r x) &
            (!x y. x <=_r y & y <=_r x --> x=y) &
            (!x y z. x <=_r y & y <=_r z --> x <=_r z)"

 acc :: "'a ord => bool"
"acc r == wf{(y,x) . x <_r y}"

 top :: "'a ord => 'a => bool"
"top r T == !x. x <=_r T"

 closed :: "'a set => 'a binop => bool"
"closed A f == !x:A. !y:A. x +_f y : A"

 semilat :: "'a sl => bool"
"semilat == %(A,r,f). order r & closed A f &
                (!x:A. !y:A. x <=_r x +_f y)  &
                (!x:A. !y:A. y <=_r x +_f y)  &
                (!x:A. !y:A. !z:A. x <=_r z & y <=_r z --> x +_f y <=_r z)"

 is_ub :: "('a*'a)set => 'a => 'a => 'a => bool"
"is_ub r x y u == (x,u):r & (y,u):r"

 is_lub :: "('a*'a)set => 'a => 'a => 'a => bool"
"is_lub r x y u == is_ub r x y u & (!z. is_ub r x y z --> (u,z):r)"

 some_lub :: "('a*'a)set => 'a => 'a => 'a"
"some_lub r x y == SOME z. is_lub r x y z"


lemma order_refl [simp, intro]:
  "order r ==> x <=_r x";
  by (simp add: order_def)

lemma order_antisym:
  "[| order r; x <=_r y; y <=_r x |] ==> x = y"
apply (unfold order_def)
apply (simp (no_asm_simp))  
done

lemma order_trans:
   "[| order r; x <=_r y; y <=_r z |] ==> x <=_r z"
apply (unfold order_def)
apply blast
done 

lemma order_less_irrefl [intro, simp]:
   "order r ==> ~ x <_r x"
apply (unfold order_def lesssub_def)
apply blast
done 

lemma order_less_trans:
  "[| order r; x <_r y; y <_r z |] ==> x <_r z"
apply (unfold order_def lesssub_def)
apply blast
done 

lemma topD [simp, intro]:
  "top r T ==> x <=_r T"
  by (simp add: top_def)

lemma top_le_conv [simp]:
  "[| order r; top r T |] ==> (T <=_r x) = (x = T)"
  by (blast intro: order_antisym)

lemma semilat_Def:
"semilat(A,r,f) == order r & closed A f & 
                 (!x:A. !y:A. x <=_r x +_f y) & 
                 (!x:A. !y:A. y <=_r x +_f y) & 
                 (!x:A. !y:A. !z:A. x <=_r z & y <=_r z --> x +_f y <=_r z)"
apply (unfold semilat_def Product_Type.split [THEN eq_reflection])
apply (rule refl [THEN eq_reflection])
done

lemma semilatDorderI [simp, intro]:
  "semilat(A,r,f) ==> order r"
  by (simp add: semilat_Def)

lemma semilatDclosedI [simp, intro]:
  "semilat(A,r,f) ==> closed A f"
apply (unfold semilat_Def)
apply simp
done

lemma semilat_ub1 [simp]:
  "[| semilat(A,r,f); x:A; y:A |] ==> x <=_r x +_f y"
  by (unfold semilat_Def, simp)

lemma semilat_ub2 [simp]:
  "[| semilat(A,r,f); x:A; y:A |] ==> y <=_r x +_f y"
  by (unfold semilat_Def, simp)

lemma semilat_lub [simp]:
 "[| x <=_r z; y <=_r z; semilat(A,r,f); x:A; y:A; z:A |] ==> x +_f y <=_r z";
  by (unfold semilat_Def, simp)


lemma plus_le_conv [simp]:
  "[| x:A; y:A; z:A; semilat(A,r,f) |] 
  ==> (x +_f y <=_r z) = (x <=_r z & y <=_r z)"
apply (unfold semilat_Def)
apply (blast intro: semilat_ub1 semilat_ub2 semilat_lub order_trans)
done

lemma le_iff_plus_unchanged:
  "[| x:A; y:A; semilat(A,r,f) |] ==> (x <=_r y) = (x +_f y = y)"
apply (rule iffI)
 apply (intro semilatDorderI order_antisym semilat_lub order_refl semilat_ub2, assumption+)
apply (erule subst)
apply simp
done 

lemma le_iff_plus_unchanged2:
  "[| x:A; y:A; semilat(A,r,f) |] ==> (x <=_r y) = (y +_f x = y)"
apply (rule iffI)
 apply (intro semilatDorderI order_antisym semilat_lub order_refl semilat_ub1, assumption+)
apply (erule subst)
apply simp
done 

(*** closed ***)

lemma closedD:
  "[| closed A f; x:A; y:A |] ==> x +_f y : A"
apply (unfold closed_def)
apply blast
done 

lemma closed_UNIV [simp]: "closed UNIV f"
  by (simp add: closed_def)

(*** lub ***)

lemma is_lubD:
  "is_lub r x y u ==> is_ub r x y u & (!z. is_ub r x y z --> (u,z):r)"
  by (simp add: is_lub_def)

lemma is_ubI:
  "[| (x,u) : r; (y,u) : r |] ==> is_ub r x y u"
  by (simp add: is_ub_def)

lemma is_ubD:
  "is_ub r x y u ==> (x,u) : r & (y,u) : r"
  by (simp add: is_ub_def)


lemma is_lub_bigger1 [iff]:  
  "is_lub (r^* ) x y y = ((x,y):r^* )"
apply (unfold is_lub_def is_ub_def)
apply blast
done


lemma is_lub_bigger2 [iff]:
  "is_lub (r^* ) x y x = ((y,x):r^* )"
apply (unfold is_lub_def is_ub_def)
apply blast 
done 


lemma extend_lub:
  "[| single_valued r; is_lub (r^* ) x y u; (x',x) : r |] 
  ==> EX v. is_lub (r^* ) x' y v"
apply (unfold is_lub_def is_ub_def)
apply (case_tac "(y,x) : r^*")
 apply (case_tac "(y,x') : r^*")
  apply blast
 apply (blast intro: r_into_rtrancl elim: converse_rtranclE
               dest: single_valuedD)
apply (rule exI)
apply (rule conjI)
 apply (blast intro: rtrancl_into_rtrancl2 dest: single_valuedD)
apply (blast intro: rtrancl_into_rtrancl rtrancl_into_rtrancl2 
             elim: converse_rtranclE dest: single_valuedD)
done 

lemma single_valued_has_lubs [rule_format]:
  "[| single_valued r; (x,u) : r^* |] ==> (!y. (y,u) : r^* --> 
  (EX z. is_lub (r^* ) x y z))"
apply (erule converse_rtrancl_induct)
 apply clarify
 apply (erule converse_rtrancl_induct)
  apply blast
 apply (blast intro: rtrancl_into_rtrancl2)
apply (blast intro: extend_lub)
done

lemma some_lub_conv:
  "[| acyclic r; is_lub (r^* ) x y u |] ==> some_lub (r^* ) x y = u"
apply (unfold some_lub_def is_lub_def)
apply (rule someI2)
 apply assumption
apply (blast intro: antisymD dest!: acyclic_impl_antisym_rtrancl)
done 

lemma is_lub_some_lub:
  "[| single_valued r; acyclic r; (x,u):r^*; (y,u):r^* |] 
  ==> is_lub (r^* ) x y (some_lub (r^* ) x y)";
  by (fastsimp dest: single_valued_has_lubs simp add: some_lub_conv)

end
