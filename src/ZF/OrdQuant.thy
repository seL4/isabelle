(*  Title:      ZF/AC/OrdQuant.thy
    ID:         $Id$
    Authors:    Krzysztof Grabczewski and L C Paulson
*)

header {*Special quantifiers*}

theory OrdQuant = Ordinal:

subsection {*Quantifiers and union operator for ordinals*}

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

(** Union over ordinals **)

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
by (simp add: oall_def, blast)

lemma rev_oallE [elim]:
    "[| ALL x<A. P(x);  ~x<A ==> Q;  P(x) ==> Q |] ==> Q"
by (simp add: oall_def, blast)


(*Trival rewrite rule;   (ALL x<a.P)<->P holds only if a is not 0!*)
lemma oall_simp [simp]: "(ALL x<a. True) <-> True"
by blast

(*Congruence rule for rewriting*)
lemma oall_cong [cong]:
    "[| a=a';  !!x. x<a' ==> P(x) <-> P'(x) |]
     ==> oall(a, %x. P(x)) <-> oall(a', %x. P'(x))"
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
    "[| a=a';  !!x. x<a' ==> P(x) <-> P'(x) |]
     ==> oex(a, %x. P(x)) <-> oex(a', %x. P'(x))"
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

lemma lt_induct:
    "[| i<k;  !!x.[| x<k;  ALL y<x. P(y) |] ==> P(x) |]  ==>  P(i)"
apply (simp add: lt_def oall_def)
apply (erule conjE)
apply (erule Ord_induct, assumption, blast)
done


subsection {*Quantification over a class*}

constdefs
  "rall"     :: "[i=>o, i=>o] => o"
    "rall(M, P) == ALL x. M(x) --> P(x)"

  "rex"      :: "[i=>o, i=>o] => o"
    "rex(M, P) == EX x. M(x) & P(x)"

syntax
  "@rall"     :: "[pttrn, i=>o, o] => o"        ("(3ALL _[_]./ _)" 10)
  "@rex"      :: "[pttrn, i=>o, o] => o"        ("(3EX _[_]./ _)" 10)

syntax (xsymbols)
  "@rall"     :: "[pttrn, i=>o, o] => o"        ("(3\<forall>_[_]./ _)" 10)
  "@rex"      :: "[pttrn, i=>o, o] => o"        ("(3\<exists>_[_]./ _)" 10)

translations
  "ALL x[M]. P"  == "rall(M, %x. P)"
  "EX x[M]. P"   == "rex(M, %x. P)"


subsubsection{*Relativized universal quantifier*}

lemma rallI [intro!]: "[| !!x. M(x) ==> P(x) |] ==> ALL x[M]. P(x)"
by (simp add: rall_def)

lemma rspec: "[| ALL x[M]. P(x); M(x) |] ==> P(x)"
by (simp add: rall_def)

(*Instantiates x first: better for automatic theorem proving?*)
lemma rev_rallE [elim]:
    "[| ALL x[M]. P(x);  ~ M(x) ==> Q;  P(x) ==> Q |] ==> Q"
by (simp add: rall_def, blast)

lemma rallE: "[| ALL x[M]. P(x);  P(x) ==> Q;  ~ M(x) ==> Q |] ==> Q"
by blast

(*Trival rewrite rule;   (ALL x[M].P)<->P holds only if A is nonempty!*)
lemma rall_triv [simp]: "(ALL x[M]. P) <-> ((EX x. M(x)) --> P)"
by (simp add: rall_def)

(*Congruence rule for rewriting*)
lemma rall_cong [cong]:
    "(!!x. M(x) ==> P(x) <-> P'(x))
     ==> rall(M, %x. P(x)) <-> rall(M, %x. P'(x))"
by (simp add: rall_def)


subsubsection{*Relativized existential quantifier*}

lemma rexI [intro]: "[| P(x); M(x) |] ==> EX x[M]. P(x)"
by (simp add: rex_def, blast)

(*The best argument order when there is only one M(x)*)
lemma rev_rexI: "[| M(x);  P(x) |] ==> EX x[M]. P(x)"
by blast

(*Not of the general form for such rules; ~EX has become ALL~ *)
lemma rexCI: "[| ALL x[M]. ~P(x) ==> P(a); M(a) |] ==> EX x[M]. P(x)"
by blast

lemma rexE [elim!]: "[| EX x[M]. P(x);  !!x. [| M(x); P(x) |] ==> Q |] ==> Q"
by (simp add: rex_def, blast)

(*We do not even have (EX x[M]. True) <-> True unless A is nonempty!!*)
lemma rex_triv [simp]: "(EX x[M]. P) <-> ((EX x. M(x)) & P)"
by (simp add: rex_def)

lemma rex_cong [cong]:
    "(!!x. M(x) ==> P(x) <-> P'(x))
     ==> rex(M, %x. P(x)) <-> rex(M, %x. P'(x))"
by (simp add: rex_def cong: conj_cong)

lemma rall_is_ball [simp]: "(\<forall>x[%z. z\<in>A]. P(x)) <-> (\<forall>x\<in>A. P(x))"
by blast

lemma rex_is_bex [simp]: "(\<exists>x[%z. z\<in>A]. P(x)) <-> (\<exists>x\<in>A. P(x))"
by blast

lemma atomize_rall: "(!!x. M(x) ==> P(x)) == Trueprop (ALL x[M]. P(x))";
by (simp add: rall_def atomize_all atomize_imp)

declare atomize_rall [symmetric, rulify]

lemma rall_simps1:
     "(ALL x[M]. P(x) & Q)   <-> (ALL x[M]. P(x)) & ((ALL x[M]. False) | Q)"
     "(ALL x[M]. P(x) | Q)   <-> ((ALL x[M]. P(x)) | Q)"
     "(ALL x[M]. P(x) --> Q) <-> ((EX x[M]. P(x)) --> Q)"
     "(~(ALL x[M]. P(x))) <-> (EX x[M]. ~P(x))"
by blast+

lemma rall_simps2:
     "(ALL x[M]. P & Q(x))   <-> ((ALL x[M]. False) | P) & (ALL x[M]. Q(x))"
     "(ALL x[M]. P | Q(x))   <-> (P | (ALL x[M]. Q(x)))"
     "(ALL x[M]. P --> Q(x)) <-> (P --> (ALL x[M]. Q(x)))"
by blast+

lemmas rall_simps [simp] = rall_simps1 rall_simps2

lemma rall_conj_distrib:
    "(ALL x[M]. P(x) & Q(x)) <-> ((ALL x[M]. P(x)) & (ALL x[M]. Q(x)))"
by blast

lemma rex_simps1:
     "(EX x[M]. P(x) & Q) <-> ((EX x[M]. P(x)) & Q)"
     "(EX x[M]. P(x) | Q) <-> (EX x[M]. P(x)) | ((EX x[M]. True) & Q)"
     "(EX x[M]. P(x) --> Q) <-> ((ALL x[M]. P(x)) --> ((EX x[M]. True) & Q))"
     "(~(EX x[M]. P(x))) <-> (ALL x[M]. ~P(x))"
by blast+

lemma rex_simps2:
     "(EX x[M]. P & Q(x)) <-> (P & (EX x[M]. Q(x)))"
     "(EX x[M]. P | Q(x)) <-> ((EX x[M]. True) & P) | (EX x[M]. Q(x))"
     "(EX x[M]. P --> Q(x)) <-> (((ALL x[M]. False) | P) --> (EX x[M]. Q(x)))"
by blast+

lemmas rex_simps [simp] = rex_simps1 rex_simps2

lemma rex_disj_distrib:
    "(EX x[M]. P(x) | Q(x)) <-> ((EX x[M]. P(x)) | (EX x[M]. Q(x)))"
by blast


subsubsection{*One-point rule for bounded quantifiers*}

lemma rex_triv_one_point1 [simp]: "(EX x[M]. x=a) <-> ( M(a))"
by blast

lemma rex_triv_one_point2 [simp]: "(EX x[M]. a=x) <-> ( M(a))"
by blast

lemma rex_one_point1 [simp]: "(EX x[M]. x=a & P(x)) <-> ( M(a) & P(a))"
by blast

lemma rex_one_point2 [simp]: "(EX x[M]. a=x & P(x)) <-> ( M(a) & P(a))"
by blast

lemma rall_one_point1 [simp]: "(ALL x[M]. x=a --> P(x)) <-> ( M(a) --> P(a))"
by blast

lemma rall_one_point2 [simp]: "(ALL x[M]. a=x --> P(x)) <-> ( M(a) --> P(a))"
by blast


subsubsection{*Sets as Classes*}

constdefs setclass :: "[i,i] => o"       ("**_")
   "setclass(A,x) == x : A"

declare setclass_def [simp]

lemma rall_setclass_is_ball [simp]: "(\<forall>x[**A]. P(x)) <-> (\<forall>x\<in>A. P(x))"
by auto

lemma rex_setclass_is_bex [simp]: "(\<exists>x[**A]. P(x)) <-> (\<exists>x\<in>A. P(x))"
by auto


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

val rall_def = thm "rall_def"
val rex_def = thm "rex_def"

val rallI = thm "rallI";
val rspec = thm "rspec";
val rallE = thm "rallE";
val rev_oallE = thm "rev_oallE";
val rall_cong = thm "rall_cong";
val rexI = thm "rexI";
val rexCI = thm "rexCI";
val rexE = thm "rexE";
val rex_cong = thm "rex_cong";

val Ord_atomize =
    atomize ([("OrdQuant.oall", [ospec]),("OrdQuant.rall", [rspec])]@
                 ZF_conn_pairs,
             ZF_mem_pairs);
simpset_ref() := simpset() setmksimps (map mk_eq o Ord_atomize o gen_all);
*}

text{*Setting up the one-point-rule simproc*}
ML
{*

let
val ex_pattern = Thm.read_cterm (Theory.sign_of (the_context ()))
                                ("EX x[M]. P(x) & Q(x)", FOLogic.oT)

val prove_rex_tac = rewtac rex_def THEN
                    Quantifier1.prove_one_point_ex_tac;

val rearrange_bex = Quantifier1.rearrange_bex prove_rex_tac;

val all_pattern = Thm.read_cterm (Theory.sign_of (the_context ()))
                                 ("ALL x[M]. P(x) --> Q(x)", FOLogic.oT)

val prove_rall_tac = rewtac rall_def THEN
                     Quantifier1.prove_one_point_all_tac;

val rearrange_ball = Quantifier1.rearrange_ball prove_rall_tac;

val defREX_regroup = mk_simproc "defined REX" [ex_pattern] rearrange_bex;
val defRALL_regroup = mk_simproc "defined RALL" [all_pattern] rearrange_ball;
in

Addsimprocs [defRALL_regroup,defREX_regroup]

end;
*}

end
