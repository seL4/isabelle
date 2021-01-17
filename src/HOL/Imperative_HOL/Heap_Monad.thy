(*  Title:      HOL/Imperative_HOL/Heap_Monad.thy
    Author:     John Matthews, Galois Connections; Alexander Krauss, Lukas Bulwahn & Florian Haftmann, TU Muenchen
*)

section \<open>A monad with a polymorphic heap and primitive reasoning infrastructure\<close>

theory Heap_Monad
imports
  Heap
  "HOL-Library.Monad_Syntax"
begin

subsection \<open>The monad\<close>

subsubsection \<open>Monad construction\<close>

text \<open>Monadic heap actions either produce values
  and transform the heap, or fail\<close>
datatype 'a Heap = Heap "heap \<Rightarrow> ('a \<times> heap) option"

declare [[code drop: "Code_Evaluation.term_of :: 'a::typerep Heap \<Rightarrow> Code_Evaluation.term"]]

primrec execute :: "'a Heap \<Rightarrow> heap \<Rightarrow> ('a \<times> heap) option" where
  [code del]: "execute (Heap f) = f"

lemma Heap_cases [case_names succeed fail]:
  fixes f and h
  assumes succeed: "\<And>x h'. execute f h = Some (x, h') \<Longrightarrow> P"
  assumes fail: "execute f h = None \<Longrightarrow> P"
  shows P
  using assms by (cases "execute f h") auto

lemma Heap_execute [simp]:
  "Heap (execute f) = f" by (cases f) simp_all

lemma Heap_eqI:
  "(\<And>h. execute f h = execute g h) \<Longrightarrow> f = g"
    by (cases f, cases g) (auto simp: fun_eq_iff)

named_theorems execute_simps "simplification rules for execute"

lemma execute_Let [execute_simps]:
  "execute (let x = t in f x) = (let x = t in execute (f x))"
  by (simp add: Let_def)


subsubsection \<open>Specialised lifters\<close>

definition tap :: "(heap \<Rightarrow> 'a) \<Rightarrow> 'a Heap" where
  [code del]: "tap f = Heap (\<lambda>h. Some (f h, h))"

lemma execute_tap [execute_simps]:
  "execute (tap f) h = Some (f h, h)"
  by (simp add: tap_def)

definition heap :: "(heap \<Rightarrow> 'a \<times> heap) \<Rightarrow> 'a Heap" where
  [code del]: "heap f = Heap (Some \<circ> f)"

lemma execute_heap [execute_simps]:
  "execute (heap f) = Some \<circ> f"
  by (simp add: heap_def)

definition guard :: "(heap \<Rightarrow> bool) \<Rightarrow> (heap \<Rightarrow> 'a \<times> heap) \<Rightarrow> 'a Heap" where
  [code del]: "guard P f = Heap (\<lambda>h. if P h then Some (f h) else None)"

lemma execute_guard [execute_simps]:
  "\<not> P h \<Longrightarrow> execute (guard P f) h = None"
  "P h \<Longrightarrow> execute (guard P f) h = Some (f h)"
  by (simp_all add: guard_def)


subsubsection \<open>Predicate classifying successful computations\<close>

definition success :: "'a Heap \<Rightarrow> heap \<Rightarrow> bool" where
  "success f h \<longleftrightarrow> execute f h \<noteq> None"

lemma successI:
  "execute f h \<noteq> None \<Longrightarrow> success f h"
  by (simp add: success_def)

lemma successE:
  assumes "success f h"
  obtains r h' where "execute f h = Some (r, h')"
  using assms by (auto simp: success_def)

named_theorems success_intros "introduction rules for success"

lemma success_tapI [success_intros]:
  "success (tap f) h"
  by (rule successI) (simp add: execute_simps)

lemma success_heapI [success_intros]:
  "success (heap f) h"
  by (rule successI) (simp add: execute_simps)

lemma success_guardI [success_intros]:
  "P h \<Longrightarrow> success (guard P f) h"
  by (rule successI) (simp add: execute_guard)

lemma success_LetI [success_intros]:
  "x = t \<Longrightarrow> success (f x) h \<Longrightarrow> success (let x = t in f x) h"
  by (simp add: Let_def)

lemma success_ifI:
  "(c \<Longrightarrow> success t h) \<Longrightarrow> (\<not> c \<Longrightarrow> success e h) \<Longrightarrow>
    success (if c then t else e) h"
  by (simp add: success_def)


subsubsection \<open>Predicate for a simple relational calculus\<close>

text \<open>
  The \<open>effect\<close> predicate states that when a computation \<open>c\<close>
  runs with the heap \<open>h\<close> will result in return value \<open>r\<close>
  and a heap \<open>h'\<close>, i.e.~no exception occurs.
\<close>  

definition effect :: "'a Heap \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> 'a \<Rightarrow> bool" where
  effect_def: "effect c h h' r \<longleftrightarrow> execute c h = Some (r, h')"

lemma effectI:
  "execute c h = Some (r, h') \<Longrightarrow> effect c h h' r"
  by (simp add: effect_def)

lemma effectE:
  assumes "effect c h h' r"
  obtains "r = fst (the (execute c h))"
    and "h' = snd (the (execute c h))"
    and "success c h"
proof (rule that)
  from assms have *: "execute c h = Some (r, h')" by (simp add: effect_def)
  then show "success c h" by (simp add: success_def)
  from * have "fst (the (execute c h)) = r" and "snd (the (execute c h)) = h'"
    by simp_all
  then show "r = fst (the (execute c h))"
    and "h' = snd (the (execute c h))" by simp_all
qed

lemma effect_success:
  "effect c h h' r \<Longrightarrow> success c h"
  by (simp add: effect_def success_def)

lemma success_effectE:
  assumes "success c h"
  obtains r h' where "effect c h h' r"
  using assms by (auto simp add: effect_def success_def)

lemma effect_deterministic:
  assumes "effect f h h' a"
    and "effect f h h'' b"
  shows "a = b" and "h' = h''"
  using assms unfolding effect_def by auto

named_theorems effect_intros "introduction rules for effect"
  and effect_elims "elimination rules for effect"

lemma effect_LetI [effect_intros]:
  assumes "x = t" "effect (f x) h h' r"
  shows "effect (let x = t in f x) h h' r"
  using assms by simp

lemma effect_LetE [effect_elims]:
  assumes "effect (let x = t in f x) h h' r"
  obtains "effect (f t) h h' r"
  using assms by simp

lemma effect_ifI:
  assumes "c \<Longrightarrow> effect t h h' r"
    and "\<not> c \<Longrightarrow> effect e h h' r"
  shows "effect (if c then t else e) h h' r"
  by (cases c) (simp_all add: assms)

lemma effect_ifE:
  assumes "effect (if c then t else e) h h' r"
  obtains "c" "effect t h h' r"
    | "\<not> c" "effect e h h' r"
  using assms by (cases c) simp_all

lemma effect_tapI [effect_intros]:
  assumes "h' = h" "r = f h"
  shows "effect (tap f) h h' r"
  by (rule effectI) (simp add: assms execute_simps)

lemma effect_tapE [effect_elims]:
  assumes "effect (tap f) h h' r"
  obtains "h' = h" and "r = f h"
  using assms by (rule effectE) (auto simp add: execute_simps)

lemma effect_heapI [effect_intros]:
  assumes "h' = snd (f h)" "r = fst (f h)"
  shows "effect (heap f) h h' r"
  by (rule effectI) (simp add: assms execute_simps)

lemma effect_heapE [effect_elims]:
  assumes "effect (heap f) h h' r"
  obtains "h' = snd (f h)" and "r = fst (f h)"
  using assms by (rule effectE) (simp add: execute_simps)

lemma effect_guardI [effect_intros]:
  assumes "P h" "h' = snd (f h)" "r = fst (f h)"
  shows "effect (guard P f) h h' r"
  by (rule effectI) (simp add: assms execute_simps)

lemma effect_guardE [effect_elims]:
  assumes "effect (guard P f) h h' r"
  obtains "h' = snd (f h)" "r = fst (f h)" "P h"
  using assms by (rule effectE)
    (auto simp add: execute_simps elim!: successE, cases "P h", auto simp add: execute_simps)


subsubsection \<open>Monad combinators\<close>

definition return :: "'a \<Rightarrow> 'a Heap" where
  [code del]: "return x = heap (Pair x)"

lemma execute_return [execute_simps]:
  "execute (return x) = Some \<circ> Pair x"
  by (simp add: return_def execute_simps)

lemma success_returnI [success_intros]:
  "success (return x) h"
  by (rule successI) (simp add: execute_simps)

lemma effect_returnI [effect_intros]:
  "h = h' \<Longrightarrow> effect (return x) h h' x"
  by (rule effectI) (simp add: execute_simps)

lemma effect_returnE [effect_elims]:
  assumes "effect (return x) h h' r"
  obtains "r = x" "h' = h"
  using assms by (rule effectE) (simp add: execute_simps)

definition raise :: "String.literal \<Rightarrow> 'a Heap" \<comment> \<open>the literal is just decoration\<close>
  where "raise s = Heap (\<lambda>_. None)"

code_datatype raise \<comment> \<open>avoid \<^const>\<open>Heap\<close> formally\<close>

lemma execute_raise [execute_simps]:
  "execute (raise s) = (\<lambda>_. None)"
  by (simp add: raise_def)

lemma effect_raiseE [effect_elims]:
  assumes "effect (raise x) h h' r"
  obtains "False"
  using assms by (rule effectE) (simp add: success_def execute_simps)

definition bind :: "'a Heap \<Rightarrow> ('a \<Rightarrow> 'b Heap) \<Rightarrow> 'b Heap" where
  [code del]: "bind f g = Heap (\<lambda>h. case execute f h of
                  Some (x, h') \<Rightarrow> execute (g x) h'
                | None \<Rightarrow> None)"

adhoc_overloading
  Monad_Syntax.bind Heap_Monad.bind

lemma execute_bind [execute_simps]:
  "execute f h = Some (x, h') \<Longrightarrow> execute (f \<bind> g) h = execute (g x) h'"
  "execute f h = None \<Longrightarrow> execute (f \<bind> g) h = None"
  by (simp_all add: bind_def)

lemma execute_bind_case:
  "execute (f \<bind> g) h = (case (execute f h) of
    Some (x, h') \<Rightarrow> execute (g x) h' | None \<Rightarrow> None)"
  by (simp add: bind_def)

lemma execute_bind_success:
  "success f h \<Longrightarrow> execute (f \<bind> g) h = execute (g (fst (the (execute f h)))) (snd (the (execute f h)))"
  by (cases f h rule: Heap_cases) (auto elim: successE simp add: bind_def)

lemma success_bind_executeI:
  "execute f h = Some (x, h') \<Longrightarrow> success (g x) h' \<Longrightarrow> success (f \<bind> g) h"
  by (auto intro!: successI elim: successE simp add: bind_def)

lemma success_bind_effectI [success_intros]:
  "effect f h h' x \<Longrightarrow> success (g x) h' \<Longrightarrow> success (f \<bind> g) h"
  by (auto simp add: effect_def success_def bind_def)

lemma effect_bindI [effect_intros]:
  assumes "effect f h h' r" "effect (g r) h' h'' r'"
  shows "effect (f \<bind> g) h h'' r'"
  using assms
  apply (auto intro!: effectI elim!: effectE successE)
  apply (subst execute_bind, simp_all)
  done

lemma effect_bindE [effect_elims]:
  assumes "effect (f \<bind> g) h h'' r'"
  obtains h' r where "effect f h h' r" "effect (g r) h' h'' r'"
  using assms by (auto simp add: effect_def bind_def split: option.split_asm)

lemma execute_bind_eq_SomeI:
  assumes "execute f h = Some (x, h')"
    and "execute (g x) h' = Some (y, h'')"
  shows "execute (f \<bind> g) h = Some (y, h'')"
  using assms by (simp add: bind_def)

lemma return_bind [simp]: "return x \<bind> f = f x"
  by (rule Heap_eqI) (simp add: execute_simps)

lemma bind_return [simp]: "f \<bind> return = f"
  by (rule Heap_eqI) (simp add: bind_def execute_simps split: option.splits)

lemma bind_bind [simp]: "(f \<bind> g) \<bind> k = (f :: 'a Heap) \<bind> (\<lambda>x. g x \<bind> k)"
  by (rule Heap_eqI) (simp add: bind_def execute_simps split: option.splits)

lemma raise_bind [simp]: "raise e \<bind> f = raise e"
  by (rule Heap_eqI) (simp add: execute_simps)


subsection \<open>Generic combinators\<close>

subsubsection \<open>Assertions\<close>

definition assert :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a Heap" where
  "assert P x = (if P x then return x else raise STR ''assert'')"

lemma execute_assert [execute_simps]:
  "P x \<Longrightarrow> execute (assert P x) h = Some (x, h)"
  "\<not> P x \<Longrightarrow> execute (assert P x) h = None"
  by (simp_all add: assert_def execute_simps)

lemma success_assertI [success_intros]:
  "P x \<Longrightarrow> success (assert P x) h"
  by (rule successI) (simp add: execute_assert)

lemma effect_assertI [effect_intros]:
  "P x \<Longrightarrow> h' = h \<Longrightarrow> r = x \<Longrightarrow> effect (assert P x) h h' r"
  by (rule effectI) (simp add: execute_assert)
 
lemma effect_assertE [effect_elims]:
  assumes "effect (assert P x) h h' r"
  obtains "P x" "r = x" "h' = h"
  using assms by (rule effectE) (cases "P x", simp_all add: execute_assert success_def)

lemma assert_cong [fundef_cong]:
  assumes "P = P'"
  assumes "\<And>x. P' x \<Longrightarrow> f x = f' x"
  shows "(assert P x \<bind> f) = (assert P' x \<bind> f')"
  by (rule Heap_eqI) (insert assms, simp add: assert_def)


subsubsection \<open>Plain lifting\<close>

definition lift :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b Heap" where
  "lift f = return o f"

lemma lift_collapse [simp]:
  "lift f x = return (f x)"
  by (simp add: lift_def)

lemma bind_lift:
  "(f \<bind> lift g) = (f \<bind> (\<lambda>x. return (g x)))"
  by (simp add: lift_def comp_def)


subsubsection \<open>Iteration -- warning: this is rarely useful!\<close>

primrec fold_map :: "('a \<Rightarrow> 'b Heap) \<Rightarrow> 'a list \<Rightarrow> 'b list Heap" where
  "fold_map f [] = return []"
| "fold_map f (x # xs) = do {
     y \<leftarrow> f x;
     ys \<leftarrow> fold_map f xs;
     return (y # ys)
   }"

lemma fold_map_append:
  "fold_map f (xs @ ys) = fold_map f xs \<bind> (\<lambda>xs. fold_map f ys \<bind> (\<lambda>ys. return (xs @ ys)))"
  by (induct xs) simp_all

lemma execute_fold_map_unchanged_heap [execute_simps]:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> \<exists>y. execute (f x) h = Some (y, h)"
  shows "execute (fold_map f xs) h =
    Some (List.map (\<lambda>x. fst (the (execute (f x) h))) xs, h)"
using assms proof (induct xs)
  case Nil show ?case by (simp add: execute_simps)
next
  case (Cons x xs)
  from Cons.prems obtain y
    where y: "execute (f x) h = Some (y, h)" by auto
  moreover from Cons.prems Cons.hyps have "execute (fold_map f xs) h =
    Some (map (\<lambda>x. fst (the (execute (f x) h))) xs, h)" by auto
  ultimately show ?case by (simp, simp only: execute_bind(1), simp add: execute_simps)
qed


subsection \<open>Partial function definition setup\<close>

definition Heap_ord :: "'a Heap \<Rightarrow> 'a Heap \<Rightarrow> bool" where
  "Heap_ord = img_ord execute (fun_ord option_ord)"

definition Heap_lub :: "'a Heap set \<Rightarrow> 'a Heap" where
  "Heap_lub = img_lub execute Heap (fun_lub (flat_lub None))"

lemma Heap_lub_empty: "Heap_lub {} = Heap Map.empty"
by(simp add: Heap_lub_def img_lub_def fun_lub_def flat_lub_def)

lemma heap_interpretation: "partial_function_definitions Heap_ord Heap_lub"
proof -
  have "partial_function_definitions (fun_ord option_ord) (fun_lub (flat_lub None))"
    by (rule partial_function_lift) (rule flat_interpretation)
  then have "partial_function_definitions (img_ord execute (fun_ord option_ord))
      (img_lub execute Heap (fun_lub (flat_lub None)))"
    by (rule partial_function_image) (auto intro: Heap_eqI)
  then show "partial_function_definitions Heap_ord Heap_lub"
    by (simp only: Heap_ord_def Heap_lub_def)
qed

interpretation heap: partial_function_definitions Heap_ord Heap_lub
  rewrites "Heap_lub {} \<equiv> Heap Map.empty"
by (fact heap_interpretation)(simp add: Heap_lub_empty)

lemma heap_step_admissible: 
  "option.admissible
      (\<lambda>f:: 'a => ('b * 'c) option. \<forall>h h' r. f h = Some (r, h') \<longrightarrow> P x h h' r)"
proof (rule ccpo.admissibleI)
  fix A :: "('a \<Rightarrow> ('b * 'c) option) set"
  assume ch: "Complete_Partial_Order.chain option.le_fun A"
    and IH: "\<forall>f\<in>A. \<forall>h h' r. f h = Some (r, h') \<longrightarrow> P x h h' r"
  from ch have ch': "\<And>x. Complete_Partial_Order.chain option_ord {y. \<exists>f\<in>A. y = f x}" by (rule chain_fun)
  show "\<forall>h h' r. option.lub_fun A h = Some (r, h') \<longrightarrow> P x h h' r"
  proof (intro allI impI)
    fix h h' r assume "option.lub_fun A h = Some (r, h')"
    from flat_lub_in_chain[OF ch' this[unfolded fun_lub_def]]
    have "Some (r, h') \<in> {y. \<exists>f\<in>A. y = f h}" by simp
    then have "\<exists>f\<in>A. f h = Some (r, h')" by auto
    with IH show "P x h h' r" by auto
  qed
qed

lemma admissible_heap: 
  "heap.admissible (\<lambda>f. \<forall>x h h' r. effect (f x) h h' r \<longrightarrow> P x h h' r)"
proof (rule admissible_fun[OF heap_interpretation])
  fix x
  show "ccpo.admissible Heap_lub Heap_ord (\<lambda>a. \<forall>h h' r. effect a h h' r \<longrightarrow> P x h h' r)"
    unfolding Heap_ord_def Heap_lub_def
  proof (intro admissible_image partial_function_lift flat_interpretation)
    show "option.admissible ((\<lambda>a. \<forall>h h' r. effect a h h' r \<longrightarrow> P x h h' r) \<circ> Heap)"
      unfolding comp_def effect_def execute.simps
      by (rule heap_step_admissible)
  qed (auto simp add: Heap_eqI)
qed

lemma fixp_induct_heap:
  fixes F :: "'c \<Rightarrow> 'c" and
    U :: "'c \<Rightarrow> 'b \<Rightarrow> 'a Heap" and
    C :: "('b \<Rightarrow> 'a Heap) \<Rightarrow> 'c" and
    P :: "'b \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> 'a \<Rightarrow> bool"
  assumes mono: "\<And>x. monotone (fun_ord Heap_ord) Heap_ord (\<lambda>f. U (F (C f)) x)"
  assumes eq: "f \<equiv> C (ccpo.fixp (fun_lub Heap_lub) (fun_ord Heap_ord) (\<lambda>f. U (F (C f))))"
  assumes inverse2: "\<And>f. U (C f) = f"
  assumes step: "\<And>f x h h' r. (\<And>x h h' r. effect (U f x) h h' r \<Longrightarrow> P x h h' r) 
    \<Longrightarrow> effect (U (F f) x) h h' r \<Longrightarrow> P x h h' r"
  assumes defined: "effect (U f x) h h' r"
  shows "P x h h' r"
  using step defined heap.fixp_induct_uc[of U F C, OF mono eq inverse2 admissible_heap, of P]
  unfolding effect_def execute.simps
  by blast

declaration \<open>Partial_Function.init "heap" \<^term>\<open>heap.fixp_fun\<close>
  \<^term>\<open>heap.mono_body\<close> @{thm heap.fixp_rule_uc} @{thm heap.fixp_induct_uc}
  (SOME @{thm fixp_induct_heap})\<close>


abbreviation "mono_Heap \<equiv> monotone (fun_ord Heap_ord) Heap_ord"

lemma Heap_ordI:
  assumes "\<And>h. execute x h = None \<or> execute x h = execute y h"
  shows "Heap_ord x y"
  using assms unfolding Heap_ord_def img_ord_def fun_ord_def flat_ord_def
  by blast

lemma Heap_ordE:
  assumes "Heap_ord x y"
  obtains "execute x h = None" | "execute x h = execute y h"
  using assms unfolding Heap_ord_def img_ord_def fun_ord_def flat_ord_def
  by atomize_elim blast

lemma bind_mono [partial_function_mono]:
  assumes mf: "mono_Heap B" and mg: "\<And>y. mono_Heap (\<lambda>f. C y f)"
  shows "mono_Heap (\<lambda>f. B f \<bind> (\<lambda>y. C y f))"
proof (rule monotoneI)
  fix f g :: "'a \<Rightarrow> 'b Heap" assume fg: "fun_ord Heap_ord f g"
  from mf
  have 1: "Heap_ord (B f) (B g)" by (rule monotoneD) (rule fg)
  from mg
  have 2: "\<And>y'. Heap_ord (C y' f) (C y' g)" by (rule monotoneD) (rule fg)

  have "Heap_ord (B f \<bind> (\<lambda>y. C y f)) (B g \<bind> (\<lambda>y. C y f))"
    (is "Heap_ord ?L ?R")
  proof (rule Heap_ordI)
    fix h
    from 1 show "execute ?L h = None \<or> execute ?L h = execute ?R h"
      by (rule Heap_ordE[where h = h]) (auto simp: execute_bind_case)
  qed
  also
  have "Heap_ord (B g \<bind> (\<lambda>y'. C y' f)) (B g \<bind> (\<lambda>y'. C y' g))"
    (is "Heap_ord ?L ?R")
  proof (rule Heap_ordI)
    fix h
    show "execute ?L h = None \<or> execute ?L h = execute ?R h"
    proof (cases "execute (B g) h")
      case None
      then have "execute ?L h = None" by (auto simp: execute_bind_case)
      thus ?thesis ..
    next
      case Some
      then obtain r h' where "execute (B g) h = Some (r, h')"
        by (metis surjective_pairing)
      then have "execute ?L h = execute (C r f) h'"
        "execute ?R h = execute (C r g) h'"
        by (auto simp: execute_bind_case)
      with 2[of r] show ?thesis by (auto elim: Heap_ordE)
    qed
  qed
  finally (heap.leq_trans)
  show "Heap_ord (B f \<bind> (\<lambda>y. C y f)) (B g \<bind> (\<lambda>y'. C y' g))" .
qed


subsection \<open>Code generator setup\<close>

subsubsection \<open>SML and OCaml\<close>

code_printing type_constructor Heap \<rightharpoonup> (SML) "(unit/ ->/ _)"
code_printing constant bind \<rightharpoonup> (SML) "!(fn/ f'_/ =>/ fn/ ()/ =>/ f'_/ (_/ ())/ ())"
code_printing constant return \<rightharpoonup> (SML) "!(fn/ ()/ =>/ _)"
code_printing constant Heap_Monad.raise \<rightharpoonup> (SML) "!(raise/ Fail/ _)"

code_printing type_constructor Heap \<rightharpoonup> (OCaml) "(unit/ ->/ _)"
code_printing constant bind \<rightharpoonup> (OCaml) "!(fun/ f'_/ ()/ ->/ f'_/ (_/ ())/ ())"
code_printing constant return \<rightharpoonup> (OCaml) "!(fun/ ()/ ->/ _)"
code_printing constant Heap_Monad.raise \<rightharpoonup> (OCaml) "failwith"


subsubsection \<open>Haskell\<close>

text \<open>Adaption layer\<close>

code_printing code_module "Heap" \<rightharpoonup> (Haskell)
\<open>
module Heap(ST, RealWorld, STRef, newSTRef, readSTRef, writeSTRef,
  STArray, newArray, newListArray, newFunArray, lengthArray, readArray, writeArray) where

import Control.Monad(liftM)
import Control.Monad.ST(RealWorld, ST)
import Data.STRef(STRef, newSTRef, readSTRef, writeSTRef)
import qualified Data.Array.ST

type STArray s a = Data.Array.ST.STArray s Integer a

newArray :: Integer -> a -> ST s (STArray s a)
newArray k = Data.Array.ST.newArray (0, k - 1)

newListArray :: [a] -> ST s (STArray s a)
newListArray xs = Data.Array.ST.newListArray (0, (fromInteger . toInteger . length) xs - 1) xs

newFunArray :: Integer -> (Integer -> a) -> ST s (STArray s a)
newFunArray k f = Data.Array.ST.newListArray (0, k - 1) (map f [0..k-1])

lengthArray :: STArray s a -> ST s Integer
lengthArray a = liftM (\(_, l) -> l + 1) (Data.Array.ST.getBounds a)

readArray :: STArray s a -> Integer -> ST s a
readArray = Data.Array.ST.readArray

writeArray :: STArray s a -> Integer -> a -> ST s ()
writeArray = Data.Array.ST.writeArray\<close>

code_reserved Haskell Heap

text \<open>Monad\<close>

code_printing type_constructor Heap \<rightharpoonup> (Haskell) "Heap.ST/ Heap.RealWorld/ _"
code_monad bind Haskell
code_printing constant return \<rightharpoonup> (Haskell) "return"
code_printing constant Heap_Monad.raise \<rightharpoonup> (Haskell) "error"


subsubsection \<open>Scala\<close>

code_printing code_module "Heap" \<rightharpoonup> (Scala)
\<open>object Heap {
  def bind[A, B](f: Unit => A, g: A => Unit => B): Unit => B = (_: Unit) => g(f(()))(())
}

class Ref[A](x: A) {
  var value = x
}

object Ref {
  def apply[A](x: A): Ref[A] =
    new Ref[A](x)
  def lookup[A](r: Ref[A]): A =
    r.value
  def update[A](r: Ref[A], x: A): Unit =
    { r.value = x }
}

object Array {
  class T[A](n: Int)
  {
    val array: Array[AnyRef] = new Array[AnyRef](n)
    def apply(i: Int): A = array(i).asInstanceOf[A]
    def update(i: Int, x: A): Unit = array(i) = x.asInstanceOf[AnyRef]
    def length: Int = array.length
    def toList: List[A] = array.toList.asInstanceOf[List[A]]
    override def toString: String = array.mkString("Array.T(", ",", ")")
  }
  def make[A](n: BigInt)(f: BigInt => A): T[A] =
  {
    val m = n.toInt
    val a = new T[A](m)
    for (i <- 0 until m) a(i) = f(i)
    a
  }
  def alloc[A](n: BigInt)(x: A): T[A] = make(n)(_ => x)
  def len[A](a: T[A]): BigInt = BigInt(a.length)
  def nth[A](a: T[A], n: BigInt): A = a(n.toInt)
  def upd[A](a: T[A], n: BigInt, x: A): Unit = a.update(n.toInt, x)
  def freeze[A](a: T[A]): List[A] = a.toList
}

\<close>

code_reserved Scala Heap Ref Array

code_printing type_constructor Heap \<rightharpoonup> (Scala) "(Unit/ =>/ _)"
code_printing constant bind \<rightharpoonup> (Scala) "Heap.bind"
code_printing constant return \<rightharpoonup> (Scala) "('_: Unit)/ =>/ _"
code_printing constant Heap_Monad.raise \<rightharpoonup> (Scala) "!sys.error((_))"


subsubsection \<open>Target variants with less units\<close>

setup \<open>

let

open Code_Thingol;

val imp_program =
  let
    val is_bind = curry (=) \<^const_name>\<open>bind\<close>;
    val is_return = curry (=) \<^const_name>\<open>return\<close>;
    val dummy_name = "";
    val dummy_case_term = IVar NONE;
    (*assumption: dummy values are not relevant for serialization*)
    val unitT = \<^type_name>\<open>unit\<close> `%% [];
    val unitt =
      IConst { sym = Code_Symbol.Constant \<^const_name>\<open>Unity\<close>, typargs = [], dicts = [], dom = [],
        annotation = NONE };
    fun dest_abs ((v, ty) `|=> t, _) = ((v, ty), t)
      | dest_abs (t, ty) =
          let
            val vs = fold_varnames cons t [];
            val v = singleton (Name.variant_list vs) "x";
            val ty' = (hd o fst o unfold_fun) ty;
          in ((SOME v, ty'), t `$ IVar (SOME v)) end;
    fun force (t as IConst { sym = Code_Symbol.Constant c, ... } `$ t') = if is_return c
          then t' else t `$ unitt
      | force t = t `$ unitt;
    fun tr_bind'' [(t1, _), (t2, ty2)] =
      let
        val ((v, ty), t) = dest_abs (t2, ty2);
      in ICase { term = force t1, typ = ty, clauses = [(IVar v, tr_bind' t)], primitive = dummy_case_term } end
    and tr_bind' t = case unfold_app t
     of (IConst { sym = Code_Symbol.Constant c, dom = ty1 :: ty2 :: _, ... }, [x1, x2]) => if is_bind c
          then tr_bind'' [(x1, ty1), (x2, ty2)]
          else force t
      | _ => force t;
    fun imp_monad_bind'' ts = (SOME dummy_name, unitT) `|=>
      ICase { term = IVar (SOME dummy_name), typ = unitT, clauses = [(unitt, tr_bind'' ts)], primitive = dummy_case_term }
    fun imp_monad_bind' (const as { sym = Code_Symbol.Constant c, dom = dom, ... }) ts = if is_bind c then case (ts, dom)
       of ([t1, t2], ty1 :: ty2 :: _) => imp_monad_bind'' [(t1, ty1), (t2, ty2)]
        | ([t1, t2, t3], ty1 :: ty2 :: _) => imp_monad_bind'' [(t1, ty1), (t2, ty2)] `$ t3
        | (ts, _) => imp_monad_bind (eta_expand 2 (const, ts))
      else IConst const `$$ map imp_monad_bind ts
    and imp_monad_bind (IConst const) = imp_monad_bind' const []
      | imp_monad_bind (t as IVar _) = t
      | imp_monad_bind (t as _ `$ _) = (case unfold_app t
         of (IConst const, ts) => imp_monad_bind' const ts
          | (t, ts) => imp_monad_bind t `$$ map imp_monad_bind ts)
      | imp_monad_bind (v_ty `|=> t) = v_ty `|=> imp_monad_bind t
      | imp_monad_bind (ICase { term = t, typ = ty, clauses = clauses, primitive = t0 }) =
          ICase { term = imp_monad_bind t, typ = ty,
            clauses = (map o apply2) imp_monad_bind clauses, primitive = imp_monad_bind t0 };

  in (Code_Symbol.Graph.map o K o map_terms_stmt) imp_monad_bind end;

in

Code_Target.add_derived_target ("SML_imp", [("SML", imp_program)])
#> Code_Target.add_derived_target ("OCaml_imp", [("OCaml", imp_program)])
#> Code_Target.add_derived_target ("Scala_imp", [("Scala", imp_program)])

end

\<close>

hide_const (open) Heap heap guard fold_map

end

