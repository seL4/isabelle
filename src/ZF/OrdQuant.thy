(*  Title:      ZF/AC/OrdQuant.thy
    ID:         $Id$
    Authors:    Krzysztof Grabczewski and L C Paulson

Quantifiers and union operator for ordinals. 
*)

theory OrdQuant = Ordinal:

constdefs
  
  (* Ordinal Quantifiers *)
  oall :: "[i, i => o] => o"
    "oall(A, P) == ALL x. x<A --> P(x)"
  
  oex :: "[i, i => o] => o"
    "oex(A, P)  == EX x. x<A & P(x)"

  (* Ordinal Union *)
  OUnion :: "[i, i => i] => i"
    "OUnion(i,B) == {z: UN x:i. B(x). Ord(i)}"
  
syntax
  "@oall"     :: "[idt, i, o] => o"        ("(3ALL _<_./ _)" 10)
  "@oex"      :: "[idt, i, o] => o"        ("(3EX _<_./ _)" 10)
  "@OUNION"   :: "[idt, i, i] => i"        ("(3UN _<_./ _)" 10)

translations
  "ALL x<a. P"  == "oall(a, %x. P)"
  "EX x<a. P"   == "oex(a, %x. P)"
  "UN x<a. B"   == "OUnion(a, %x. B)"

syntax (xsymbols)
  "@oall"     :: "[idt, i, o] => o"        ("(3\<forall>_<_./ _)" 10)
  "@oex"      :: "[idt, i, o] => o"        ("(3\<exists>_<_./ _)" 10)
  "@OUNION"   :: "[idt, i, i] => i"        ("(3\<Union>_<_./ _)" 10)


(** simplification of the new quantifiers **)


(*MOST IMPORTANT that this is added to the simpset BEFORE Ord_atomize
  is proved.  Ord_atomize would convert this rule to 
    x < 0 ==> P(x) == True, which causes dire effects!*)
lemma [simp]: "(ALL x<0. P(x))"
by (simp add: oall_def) 

lemma [simp]: "~(EX x<0. P(x))"
by (simp add: oex_def) 

lemma [simp]: "(ALL x<succ(i). P(x)) <-> (Ord(i) --> P(i) & (ALL x<i. P(x)))"
apply (simp add: oall_def le_iff) 
apply (blast intro: lt_Ord2) 
done

lemma [simp]: "(EX x<succ(i). P(x)) <-> (Ord(i) & (P(i) | (EX x<i. P(x))))"
apply (simp add: oex_def le_iff) 
apply (blast intro: lt_Ord2) 
done

declare Ord_Un [intro,simp,TC]
declare Ord_UN [intro,simp,TC]
declare Ord_Union [intro,simp,TC]

(** Now some very basic ZF theorems **)

lemma [simp]: "((P-->Q) <-> (P-->R)) <-> (P --> (Q<->R))"
by blast

lemma [simp]: "cons(a,cons(a,B)) = cons(a,B)"
by blast

lemma trans_imp_trans_on: "trans(r) ==> trans[A](r)"
by (unfold trans_def trans_on_def, blast)

lemma image_is_UN: "[| function(g); x <= domain(g) |] ==> g``x = (UN k:x. {g`k})"
by (blast intro: function_apply_equality [THEN sym] function_apply_Pair) 

lemma functionI: 
     "[| !!x y y'. [| <x,y>:r; <x,y'>:r |] ==> y=y' |] ==> function(r)"
by (simp add: function_def, blast) 

lemma function_lam: "function (lam x:A. b(x))"
by (simp add: function_def lam_def) 

lemma relation_lam: "relation (lam x:A. b(x))"  
by (simp add: relation_def lam_def) 

lemma restrict_iff: "z \<in> restrict(r,A) \<longleftrightarrow> z \<in> r & (\<exists>x\<in>A. \<exists>y. z = \<langle>x, y\<rangle>)"
by (simp add: restrict_def) 

(** These mostly belong to theory Ordinal **)

lemma Union_upper_le:
     "[| j: J;  i\<le>j;  Ord(\<Union>(J)) |] ==> i \<le> \<Union>J"
apply (subst Union_eq_UN)  
apply (rule UN_upper_le, auto)
done

lemma zero_not_Limit [iff]: "~ Limit(0)"
by (simp add: Limit_def)

lemma Limit_has_1: "Limit(i) ==> 1 < i"
by (blast intro: Limit_has_0 Limit_has_succ)

lemma Limit_Union [rule_format]: "[| I \<noteq> 0;  \<forall>i\<in>I. Limit(i) |] ==> Limit(\<Union>I)"
apply (simp add: Limit_def lt_def)
apply (blast intro!: equalityI)
done

lemma increasing_LimitI: "[| 0<l; \<forall>x\<in>l. \<exists>y\<in>l. x<y |] ==> Limit(l)"
apply (simp add: Limit_def lt_Ord2, clarify)
apply (drule_tac i=y in ltD) 
apply (blast intro: lt_trans1 [OF _ ltI] lt_Ord2)
done

lemma UN_upper_lt:
     "[| a\<in>A;  i < b(a);  Ord(\<Union>x\<in>A. b(x)) |] ==> i < (\<Union>x\<in>A. b(x))"
by (unfold lt_def, blast) 

lemma lt_imp_0_lt: "j<i ==> 0<i"
by (blast intro: lt_trans1 Ord_0_le [OF lt_Ord]) 

lemma Ord_set_cases:
   "\<forall>i\<in>I. Ord(i) ==> I=0 \<or> \<Union>(I) \<in> I \<or> (\<Union>(I) \<notin> I \<and> Limit(\<Union>(I)))"
apply (clarify elim!: not_emptyE) 
apply (cases "\<Union>(I)" rule: Ord_cases) 
   apply (blast intro: Ord_Union)
  apply (blast intro: subst_elem)
 apply auto 
apply (clarify elim!: equalityE succ_subsetE)
apply (simp add: Union_subset_iff)
apply (subgoal_tac "B = succ(j)", blast )
apply (rule le_anti_sym) 
 apply (simp add: le_subset_iff) 
apply (simp add: ltI)
done

lemma Ord_Union_eq_succD: "[|\<forall>x\<in>X. Ord(x);  \<Union>X = succ(j)|] ==> succ(j) \<in> X"
by (drule Ord_set_cases, auto)

(*See also Transset_iff_Union_succ*)
lemma Ord_Union_succ_eq: "Ord(i) ==> \<Union>(succ(i)) = i"
by (blast intro: Ord_trans)

lemma lt_Union_iff: "\<forall>i\<in>A. Ord(i) ==> (j < \<Union>(A)) <-> (\<exists>i\<in>A. j<i)"
by (auto simp: lt_def Ord_Union)

lemma Un_upper1_lt: "[|k < i; Ord(j)|] ==> k < i Un j"
by (simp add: lt_def) 

lemma Un_upper2_lt: "[|k < j; Ord(i)|] ==> k < i Un j"
by (simp add: lt_def) 

lemma Ord_OUN [intro,simp]:
     "[| !!x. x<A ==> Ord(B(x)) |] ==> Ord(\<Union>x<A. B(x))"
by (simp add: OUnion_def ltI Ord_UN) 

lemma OUN_upper_lt:
     "[| a<A;  i < b(a);  Ord(\<Union>x<A. b(x)) |] ==> i < (\<Union>x<A. b(x))"
by (unfold OUnion_def lt_def, blast )

lemma OUN_upper_le:
     "[| a<A;  i\<le>b(a);  Ord(\<Union>x<A. b(x)) |] ==> i \<le> (\<Union>x<A. b(x))"
apply (unfold OUnion_def, auto)
apply (rule UN_upper_le )
apply (auto simp add: lt_def) 
done

lemma Limit_OUN_eq: "Limit(i) ==> (UN x<i. x) = i"
by (simp add: OUnion_def Limit_Union_eq Limit_is_Ord)

(* No < version; consider (UN i:nat.i)=nat *)
lemma OUN_least:
     "(!!x. x<A ==> B(x) \<subseteq> C) ==> (UN x<A. B(x)) \<subseteq> C"
by (simp add: OUnion_def UN_least ltI)

(* No < version; consider (UN i:nat.i)=nat *)
lemma OUN_least_le:
     "[| Ord(i);  !!x. x<A ==> b(x) \<le> i |] ==> (UN x<A. b(x)) \<le> i"
by (simp add: OUnion_def UN_least_le ltI Ord_0_le)

lemma le_implies_OUN_le_OUN:
     "[| !!x. x<A ==> c(x) \<le> d(x) |] ==> (UN x<A. c(x)) \<le> (UN x<A. d(x))"
by (blast intro: OUN_least_le OUN_upper_le le_Ord2 Ord_OUN)

lemma OUN_UN_eq:
     "(!!x. x:A ==> Ord(B(x)))
      ==> (UN z < (UN x:A. B(x)). C(z)) = (UN  x:A. UN z < B(x). C(z))"
by (simp add: OUnion_def) 

lemma OUN_Union_eq:
     "(!!x. x:X ==> Ord(x))
      ==> (UN z < Union(X). C(z)) = (UN x:X. UN z < x. C(z))"
by (simp add: OUnion_def) 

(*So that rule_format will get rid of ALL x<A...*)
lemma atomize_oall [symmetric, rulify]:
     "(!!x. x<A ==> P(x)) == Trueprop (ALL x<A. P(x))"
by (simp add: oall_def atomize_all atomize_imp)

(*** universal quantifier for ordinals ***)

lemma oallI [intro!]:
    "[| !!x. x<A ==> P(x) |] ==> ALL x<A. P(x)"
by (simp add: oall_def) 

lemma ospec: "[| ALL x<A. P(x);  x<A |] ==> P(x)"
by (simp add: oall_def) 

lemma oallE:
    "[| ALL x<A. P(x);  P(x) ==> Q;  ~x<A ==> Q |] ==> Q"
apply (simp add: oall_def, blast) 
done

lemma rev_oallE [elim]:
    "[| ALL x<A. P(x);  ~x<A ==> Q;  P(x) ==> Q |] ==> Q"
apply (simp add: oall_def, blast)  
done


(*Trival rewrite rule;   (ALL x<a.P)<->P holds only if a is not 0!*)
lemma oall_simp [simp]: "(ALL x<a. True) <-> True"
by blast

(*Congruence rule for rewriting*)
lemma oall_cong [cong]:
    "[| a=a';  !!x. x<a' ==> P(x) <-> P'(x) |] ==> oall(a,P) <-> oall(a',P')"
by (simp add: oall_def)


(*** existential quantifier for ordinals ***)

lemma oexI [intro]:
    "[| P(x);  x<A |] ==> EX x<A. P(x)"
apply (simp add: oex_def, blast) 
done

(*Not of the general form for such rules; ~EX has become ALL~ *)
lemma oexCI:
   "[| ALL x<A. ~P(x) ==> P(a);  a<A |] ==> EX x<A. P(x)"
apply (simp add: oex_def, blast) 
done

lemma oexE [elim!]:
    "[| EX x<A. P(x);  !!x. [| x<A; P(x) |] ==> Q |] ==> Q"
apply (simp add: oex_def, blast) 
done

lemma oex_cong [cong]:
    "[| a=a';  !!x. x<a' ==> P(x) <-> P'(x) |] ==> oex(a,P) <-> oex(a',P')"
apply (simp add: oex_def cong add: conj_cong)
done


(*** Rules for Ordinal-Indexed Unions ***)

lemma OUN_I [intro]: "[| a<i;  b: B(a) |] ==> b: (UN z<i. B(z))"
by (unfold OUnion_def lt_def, blast)

lemma OUN_E [elim!]:
    "[| b : (UN z<i. B(z));  !!a.[| b: B(a);  a<i |] ==> R |] ==> R"
apply (unfold OUnion_def lt_def, blast)
done

lemma OUN_iff: "b : (UN x<i. B(x)) <-> (EX x<i. b : B(x))"
by (unfold OUnion_def oex_def lt_def, blast)

lemma OUN_cong [cong]:
    "[| i=j;  !!x. x<j ==> C(x)=D(x) |] ==> (UN x<i. C(x)) = (UN x<j. D(x))"
by (simp add: OUnion_def lt_def OUN_iff)

declare ltD [THEN beta, simp]


lemma lt_induct: 
    "[| i<k;  !!x.[| x<k;  ALL y<x. P(y) |] ==> P(x) |]  ==>  P(i)"
apply (simp add: lt_def oall_def)
apply (erule conjE) 
apply (erule Ord_induct, assumption, blast) 
done

ML
{*
val oall_def = thm "oall_def"
val oex_def = thm "oex_def"
val OUnion_def = thm "OUnion_def"

val oallI = thm "oallI";
val ospec = thm "ospec";
val oallE = thm "oallE";
val rev_oallE = thm "rev_oallE";
val oall_simp = thm "oall_simp";
val oall_cong = thm "oall_cong";
val oexI = thm "oexI";
val oexCI = thm "oexCI";
val oexE = thm "oexE";
val oex_cong = thm "oex_cong";
val OUN_I = thm "OUN_I";
val OUN_E = thm "OUN_E";
val OUN_iff = thm "OUN_iff";
val OUN_cong = thm "OUN_cong";
val lt_induct = thm "lt_induct";

val Ord_atomize =
    atomize (("OrdQuant.oall", [ospec])::ZF_conn_pairs, ZF_mem_pairs);
simpset_ref() := simpset() setmksimps (map mk_eq o Ord_atomize o gen_all);
*}

end
