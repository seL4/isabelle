(*  Title:      Tests.thy
    Author:     Daniel Matichuk, NICTA/UNSW
*)

section \<open>Miscellaneous Eisbach tests\<close>

theory Tests
imports Main Eisbach_Tools
begin


section \<open>Named Theorems Tests\<close>

named_theorems foo

method foo declares foo = (rule foo)

lemma
  assumes A [foo]: A
  shows A
  apply foo
  done


section \<open>Match Tests\<close>

notepad
begin
  have dup: "\<And>A. A \<Longrightarrow> A \<Longrightarrow> A" by simp

  fix A y
  have "(\<And>x. A x) \<Longrightarrow> A y"
    apply (rule dup, match premises in Y: "\<And>B. P B" for P \<Rightarrow> \<open>match (P) in A \<Rightarrow> \<open>print_fact Y, rule Y\<close>\<close>)
    apply (rule dup, match premises in Y: "\<And>B :: 'a. P B" for P \<Rightarrow> \<open>match (P) in A \<Rightarrow> \<open>print_fact Y, rule Y\<close>\<close>)
    apply (rule dup, match premises in Y: "\<And>B :: 'a. P B" for P \<Rightarrow> \<open>match conclusion in "P y" for y \<Rightarrow> \<open>print_fact Y, print_term y, rule Y[where B=y]\<close>\<close>)
    apply (rule dup, match premises in Y: "\<And>B :: 'a. P B" for P \<Rightarrow> \<open>match conclusion in "P z" for z \<Rightarrow> \<open>print_fact Y, print_term y, rule Y[where B=z]\<close>\<close>)
    apply (rule dup, match conclusion in "P y" for P \<Rightarrow> \<open>match premises in Y: "\<And>z. P z" \<Rightarrow> \<open>print_fact Y, rule Y[where z=y]\<close>\<close>)
    apply (match premises in Y: "\<And>z :: 'a. P z" for P \<Rightarrow> \<open>match conclusion in "P y" \<Rightarrow> \<open>print_fact Y, rule Y[where z=y]\<close>\<close>)
    done

  assume X: "\<And>x. A x" "A y"
  have "A y"
    apply (match X in Y:"\<And>B. A B" and Y':"B ?x" for B \<Rightarrow> \<open>print_fact Y[where B=y], print_term B\<close>)
    apply (match X in Y:"B ?x" and Y':"B ?x" for B \<Rightarrow> \<open>print_fact Y, print_term B\<close>)
    apply (match X in Y:"B x" and Y':"B x" for B x \<Rightarrow> \<open>print_fact Y, print_term B, print_term x\<close>)
    apply (insert X)
    apply (match premises in Y:"\<And>B. A B" and Y':"B y" for B and y :: 'a \<Rightarrow> \<open>print_fact Y[where B=y], print_term B\<close>)
    apply (match premises in Y:"B ?x" and Y':"B ?x" for B \<Rightarrow> \<open>print_fact Y, print_term B\<close>)
    apply (match premises in Y:"B x" and Y':"B x" for B x \<Rightarrow> \<open>print_fact Y, print_term B\<close>)
    apply (match conclusion in "P x" and "P y" for P x \<Rightarrow> \<open>print_term P, print_term x\<close>)
    apply assumption
    done

  {
   fix B x y
   assume X: "\<And>x y. B x x y"
   have "B x x y"
     by (match X in Y:"\<And>y. B y y z" for z \<Rightarrow> \<open>rule Y[where y=x]\<close>)

   fix A B
   have "(\<And>x y. A (B x) y) \<Longrightarrow> A (B x) y"
     by (match premises in Y: "\<And>xx. ?H (B xx)" \<Rightarrow> \<open>rule Y\<close>)
  }

  (* match focusing retains prems *)
  fix B x
  have "(\<And>x. A x) \<Longrightarrow> (\<And>z. B z) \<Longrightarrow> A y \<Longrightarrow> B x"
    apply (match premises in Y: "\<And>z :: 'a. A z"  \<Rightarrow> \<open>match premises in Y': "\<And>z :: 'b. B z" \<Rightarrow> \<open>print_fact Y, print_fact Y', rule Y'[where z=x]\<close>\<close>)
    done

  (*Attributes *)
  fix C
  have "(\<And>x :: 'a. A x)  \<Longrightarrow> (\<And>z. B z) \<Longrightarrow> A y \<Longrightarrow> B x \<and> B x \<and> A y"
    apply (intro conjI)
    apply (match premises in Y: "\<And>z :: 'a. A z" and Y'[intro]:"\<And>z :: 'b. B z" \<Rightarrow> \<open>fastforce\<close>)
    apply (match premises in Y: "\<And>z :: 'a. A z"  \<Rightarrow> \<open>match premises in Y'[intro]:"\<And>z :: 'b. B z" \<Rightarrow> \<open>fastforce\<close>\<close>)
    apply (match premises in Y[thin]: "\<And>z :: 'a. A z"  \<Rightarrow> \<open>(match premises in Y':"\<And>z :: 'a. A z" \<Rightarrow> \<open>print_fact Y,fail\<close> \<bar> Y': "?H" \<Rightarrow> \<open>-\<close>)\<close>)
    apply assumption
    done

  fix A B C D
  have "\<And>uu'' uu''' uu uu'. (\<And>x :: 'a. A uu' x)  \<Longrightarrow> D uu y \<Longrightarrow> (\<And>z. B uu z) \<Longrightarrow> C uu y \<Longrightarrow> (\<And>z y. C uu z)  \<Longrightarrow> B uu x \<and> B uu x \<and> C uu y"
    apply (match premises in Y[thin]: "\<And>z :: 'a. A ?zz' z" and
                          Y'[thin]: "\<And>rr :: 'b. B ?zz rr" \<Rightarrow>
          \<open>print_fact Y, print_fact Y', intro conjI, rule Y', insert Y', insert Y'[where rr=x]\<close>)
    apply (match premises in Y:"B ?u ?x" \<Rightarrow> \<open>rule Y\<close>)
    apply (insert TrueI)
    apply (match premises in Y'[thin]: "\<And>ff. B uu ff" for uu \<Rightarrow> \<open>insert Y', drule meta_spec[where x=x]\<close>)
    apply assumption
    done


  (* Multi-matches. As many facts as match are bound. *)
  fix A B C x
  have "(\<And>x :: 'a. A x) \<Longrightarrow> (\<And>y :: 'a. B y) \<Longrightarrow> C y \<Longrightarrow> (A x \<and> B y \<and> C y)"
    apply (match premises in Y[thin]: "\<And>z :: 'a. ?A z" (multi) \<Rightarrow> \<open>intro conjI, (rule Y)+\<close>)
    apply (match premises in Y[thin]: "\<And>z :: 'a. ?A z" (multi) \<Rightarrow> \<open>fail\<close> \<bar> "C y" \<Rightarrow> \<open>-\<close>) (* multi-match must bind something *)
    apply (match premises in Y: "C y" \<Rightarrow> \<open>rule Y\<close>)
    done

  fix A B C x
  have "(\<And>x :: 'a. A x) \<Longrightarrow> (\<And>y :: 'a. B y) \<Longrightarrow> C y \<Longrightarrow> (A x \<and> B y \<and> C y)"
    apply (match premises in Y[thin]: "\<And>z. ?A z" (multi) \<Rightarrow> \<open>intro conjI, (rule Y)+\<close>)
    apply (match premises in Y[thin]: "\<And>z. ?A z" (multi) \<Rightarrow> \<open>fail\<close> \<bar> "C y" \<Rightarrow> \<open>-\<close>) (* multi-match must bind something *)
    apply (match premises in Y: "C y" \<Rightarrow> \<open>rule Y\<close>)
    done


  (*We may use for-fixes in multi-matches too. All bound facts must agree on the fixed term *)
  fix A B C x
  have "(\<And>y :: 'a. B y \<and> C y) \<Longrightarrow> (\<And>x :: 'a. A x \<and> B x) \<Longrightarrow> (\<And>y :: 'a. A y \<and> C y) \<Longrightarrow> C y \<Longrightarrow> (A x \<and> B y \<and> C y)"
    apply (match premises in Y: "\<And>x :: 'a. P x \<and> ?U x" (multi) for P \<Rightarrow> \<open>intro conjI Y[THEN conjunct1]\<close>)
    apply (match premises in Y: "\<And>z :: 'a. ?A z \<longrightarrow> False" (multi) \<Rightarrow> \<open>print_fact Y, fail\<close> \<bar> "C y" \<Rightarrow> \<open>print_term C\<close>) (* multi-match must bind something *)
    apply (match premises in Y: "\<And>x. B x \<and> C x" \<Rightarrow> \<open>intro conjI Y[THEN conjunct1]\<close>)
    apply (match premises in Y: "C ?x" \<Rightarrow> \<open>rule Y\<close>)
    done

  (* Attributes *)
  fix A B C x
  have "(\<And>x :: 'a. A x \<and> B x) \<Longrightarrow> (\<And>y :: 'a. A y \<and> C y) \<Longrightarrow> (\<And>y :: 'a. B y \<and> C y) \<Longrightarrow> C y \<Longrightarrow> (A x \<and> B y \<and> C y)"
    apply (match premises in Y: "\<And>x :: 'a. P x \<and> ?U x" (multi) for P \<Rightarrow> \<open>match Y[THEN conjunct1]  in Y':"?H"  (multi) \<Rightarrow> \<open>intro conjI,rule Y'\<close>\<close>)
    apply (match premises in Y: "\<And>x :: 'a. P x \<and> ?U x" (multi) for P \<Rightarrow> \<open>match Y[THEN conjunct2]  in Y':"?H"  (multi) \<Rightarrow> \<open>rule Y'\<close>\<close>)
    apply assumption
    done

(* Removed feature for now *)
(*
  fix A B C x
  have "(\<And>x :: 'a. A x \<and> B x) \<Longrightarrow> (\<And>y :: 'a. A y \<and> C y) \<Longrightarrow> (\<And>y :: 'a. B y \<and> C y) \<Longrightarrow> C y \<Longrightarrow> (A x \<and> B y \<and> C y)"
  apply (match prems in Y: "\<And>x :: 'a. P x \<and> ?U x" (multi) for P \<Rightarrow> \<open>match \<open>K @{thms Y TrueI}\<close> in Y':"?H"  (multi) \<Rightarrow> \<open>rule conjI; (rule Y')?\<close>\<close>)
  apply (match prems in Y: "\<And>x :: 'a. P x \<and> ?U x" (multi) for P \<Rightarrow> \<open>match \<open>K [@{thm Y}]\<close> in Y':"?H"  (multi) \<Rightarrow> \<open>rule Y'\<close>\<close>)
  done
*)
  (* Testing THEN_ALL_NEW within match *)
  fix A B C x
  have "(\<And>x :: 'a. A x \<and> B x) \<Longrightarrow> (\<And>y :: 'a. A y \<and> C y) \<Longrightarrow> (\<And>y :: 'a. B y \<and> C y) \<Longrightarrow> C y \<Longrightarrow> (A x \<and> B y \<and> C y)"
    apply (match premises in Y: "\<And>x :: 'a. P x \<and> ?U x" (multi) for P \<Rightarrow> \<open>intro conjI ; ((rule Y[THEN conjunct1])?); rule Y[THEN conjunct2] \<close>)
    done

  (* Cut tests *)
  fix A B C

  have "D \<and> C  \<Longrightarrow> A \<and> B  \<Longrightarrow> A \<longrightarrow> C \<Longrightarrow> D \<longrightarrow> True \<Longrightarrow> C"
    by (((match premises in I: "P \<and> Q" (cut)
              and I': "P \<longrightarrow> ?U" for P Q \<Rightarrow> \<open>rule mp [OF I' I[THEN conjunct1]]\<close>)?), simp)

  have "A \<and> B \<Longrightarrow> A \<longrightarrow> C \<Longrightarrow> C"
    by (((match premises in I: "P \<and> Q" (cut)
              and I': "P \<longrightarrow> ?U" for P Q \<Rightarrow> \<open>rule mp [OF I' I[THEN conjunct1]]\<close>)?, simp) | simp)

  fix f x y
  have "f x y \<Longrightarrow> f x y"
    by (match conclusion in "f x y" for f x y  \<Rightarrow> \<open>print_term f\<close>)

  fix A B C
  assume X: "A \<and> B" "A \<and> C" C
  have "A \<and> B \<and> C"
    by (match X in H: "A \<and> ?H" (multi,cut) \<Rightarrow>
          \<open>match H in "A \<and> C" and "A \<and> B" \<Rightarrow> \<open>fail\<close>\<close>
        | simp add: X)

end

(* Testing inner focusing. This fails if we don't smash flex-flex pairs produced
   by retrofitting. This needs to be done more carefully to avoid smashing
   legitimate pairs.*)

schematic_lemma "?A x \<Longrightarrow> A x"
  apply (match conclusion in "H" for H \<Rightarrow> \<open>match conclusion in Y for Y \<Rightarrow> \<open>print_term Y\<close>\<close>)
  apply assumption
  done

(* Ensure short-circuit after first match failure *)
lemma
  assumes A: "P \<and> Q"
  shows "P"
  by ((match A in "P \<and> Q" \<Rightarrow> \<open>fail\<close> \<bar> "?H" \<Rightarrow> \<open>-\<close>) | simp add: A)

lemma
  assumes A: "D \<and> C" "A \<and> B" "A \<longrightarrow> B"
  shows "A"
  apply ((match A in U: "P \<and> Q" (cut) and "P' \<longrightarrow> Q'" for P Q P' Q' \<Rightarrow>
      \<open>simp add: U\<close> \<bar> "?H" \<Rightarrow> \<open>-\<close>) | -)
  apply (simp add: A)
  done


subsection \<open>Uses Tests\<close>

ML \<open>
  fun test_internal_fact ctxt factnm =
    (case try (Proof_Context.get_thms ctxt) factnm of
      NONE => ()
    | SOME _ => error "Found internal fact")\<close>

method uses_test\<^sub>1 uses uses_test\<^sub>1_uses = (rule uses_test\<^sub>1_uses)

lemma assumes A shows A by (uses_test\<^sub>1 uses_test\<^sub>1_uses: assms)

ML \<open>test_internal_fact @{context} "uses_test\<^sub>1_uses"\<close>

ML \<open>test_internal_fact @{context} "Tests.uses_test\<^sub>1_uses"\<close>
ML \<open>test_internal_fact @{context} "Tests.uses_test\<^sub>1.uses_test\<^sub>1_uses"\<close>


(* Testing term and fact passing in recursion *)

method recursion_example for x :: bool uses facts =
  (match (x) in
    "A \<and> B" for A B \<Rightarrow> \<open>(recursion_example A facts: facts, recursion_example B facts: facts)\<close>
  \<bar> "?H" \<Rightarrow> \<open>match facts in U: "x" \<Rightarrow> \<open>insert U\<close>\<close>)

lemma
  assumes asms: "A" "B" "C" "D"
  shows "(A \<and> B) \<and> (C \<and> D)"
  apply (recursion_example "(A \<and> B) \<and> (C \<and> D)" facts: asms)
  apply simp
  done

(*Method.sections in existing method*)
method my_simp\<^sub>1 uses my_simp\<^sub>1_facts = (simp add: my_simp\<^sub>1_facts)
lemma assumes A shows A by (my_simp\<^sub>1 my_simp\<^sub>1_facts: assms)

(*Method.sections via Eisbach argument parser*)
method uses_test\<^sub>2 uses uses_test\<^sub>2_uses = (uses_test\<^sub>1 uses_test\<^sub>1_uses: uses_test\<^sub>2_uses)
lemma assumes A shows A by (uses_test\<^sub>2 uses_test\<^sub>2_uses: assms)


subsection \<open>Declaration Tests\<close>

named_theorems declare_facts\<^sub>1

method declares_test\<^sub>1 declares declare_facts\<^sub>1 = (rule declare_facts\<^sub>1)

lemma assumes A shows A by (declares_test\<^sub>1 declare_facts\<^sub>1: assms)

lemma assumes A[declare_facts\<^sub>1]: A shows A by declares_test\<^sub>1


subsection \<open>Rule Instantiation Tests\<close>

method my_allE\<^sub>1 for x :: 'a and P :: "'a \<Rightarrow> bool" =
  (erule allE [where x = x and P = P])

lemma "\<forall>x. Q x \<Longrightarrow> Q x" by (my_allE\<^sub>1 x Q)

method my_allE\<^sub>2 for x :: 'a and P :: "'a \<Rightarrow> bool" =
  (erule allE [of P x])

lemma "\<forall>x. Q x \<Longrightarrow> Q x" by (my_allE\<^sub>2 x Q)

method my_allE\<^sub>3 for x :: 'a and P :: "'a \<Rightarrow> bool" =
  (match allE [where 'a = 'a] in X: "\<And>(x :: 'a) P R. \<forall>x. P x \<Longrightarrow> (P x \<Longrightarrow> R) \<Longrightarrow> R" \<Rightarrow>
    \<open>erule X [where x = x and P = P]\<close>)

lemma "\<forall>x. Q x \<Longrightarrow> Q x" by (my_allE\<^sub>3 x Q)

method my_allE\<^sub>4 for x :: 'a and P :: "'a \<Rightarrow> bool" =
  (match allE [where 'a = 'a] in X: "\<And>(x :: 'a) P R. \<forall>x. P x \<Longrightarrow> (P x \<Longrightarrow> R) \<Longrightarrow> R" \<Rightarrow>
    \<open>erule X [of x P]\<close>)

lemma "\<forall>x. Q x \<Longrightarrow> Q x" by (my_allE\<^sub>4 x Q)



(* Polymorphism test *)

axiomatization foo' :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool"
axiomatization where foo'_ax1: "foo' x y z \<Longrightarrow> z \<and> y"
axiomatization where foo'_ax2: "foo' x y y \<Longrightarrow> x \<and> z"

lemmas my_thms = foo'_ax1 foo'_ax2

definition first_id where "first_id x = x"

lemmas my_thms' = my_thms[of "first_id x" for x]

method print_conclusion = (match conclusion in concl for concl \<Rightarrow> \<open>print_term concl\<close>)

lemma
  assumes foo: "\<And>x (y :: bool). foo' (A x) B (A x)"
  shows "\<And>z. A z \<and> B"
  apply
    (match conclusion in "f x y" for f y and x :: "'d :: type" \<Rightarrow> \<open>
      match my_thms' in R:"\<And>(x :: 'f :: type). ?P (first_id x) \<Longrightarrow> ?R"
                     and R':"\<And>(x :: 'f :: type). ?P' (first_id x) \<Longrightarrow> ?R'" \<Rightarrow> \<open>
        match (x) in "q :: 'f" for q \<Rightarrow> \<open>
          rule R[of q,simplified first_id_def],
          print_conclusion,
          rule foo
      \<close>\<close>\<close>)
  done


ML {*
structure Data = Generic_Data
(
  type T = thm list;
  val empty: T = [];
  val extend = I;
  fun merge data : T = Thm.merge_thms data;
);
*}

local_setup \<open>Local_Theory.add_thms_dynamic (@{binding test_dyn}, Data.get)\<close>

setup \<open>Context.theory_map (Data.put @{thms TrueI})\<close>

method dynamic_thms_test = (rule test_dyn)

locale foo =
  fixes A
  assumes A : "A"
begin

local_setup
  \<open>Local_Theory.declaration {pervasive = false, syntax = false}
    (fn phi => Data.put (Morphism.fact phi @{thms A}))\<close>

lemma A by dynamic_thms_test

end

(* Method name internalization test *)

method test2 = (simp)

method simp = fail

lemma "A \<Longrightarrow> A" by test2

end
