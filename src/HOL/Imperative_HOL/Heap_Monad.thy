(*  Title:      HOL/Imperative_HOL/Heap_Monad.thy
    Author:     John Matthews, Galois Connections; Alexander Krauss, Lukas Bulwahn & Florian Haftmann, TU Muenchen
*)

header {* A monad with a polymorphic heap and primitive reasoning infrastructure *}

theory Heap_Monad
imports
  Heap
  "~~/src/HOL/Library/Monad_Syntax"
  "~~/src/HOL/Library/Code_Natural"
begin

subsection {* The monad *}

subsubsection {* Monad construction *}

text {* Monadic heap actions either produce values
  and transform the heap, or fail *}
datatype 'a Heap = Heap "heap \<Rightarrow> ('a \<times> heap) option"

lemma [code, code del]:
  "(Code_Evaluation.term_of :: 'a::typerep Heap \<Rightarrow> Code_Evaluation.term) = Code_Evaluation.term_of"
  ..

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

ML {* structure Execute_Simps = Named_Thms
(
  val name = @{binding execute_simps}
  val description = "simplification rules for execute"
) *}

setup Execute_Simps.setup

lemma execute_Let [execute_simps]:
  "execute (let x = t in f x) = (let x = t in execute (f x))"
  by (simp add: Let_def)


subsubsection {* Specialised lifters *}

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


subsubsection {* Predicate classifying successful computations *}

definition success :: "'a Heap \<Rightarrow> heap \<Rightarrow> bool" where
  "success f h \<longleftrightarrow> execute f h \<noteq> None"

lemma successI:
  "execute f h \<noteq> None \<Longrightarrow> success f h"
  by (simp add: success_def)

lemma successE:
  assumes "success f h"
  obtains r h' where "r = fst (the (execute c h))"
    and "h' = snd (the (execute c h))"
    and "execute f h \<noteq> None"
  using assms by (simp add: success_def)

ML {* structure Success_Intros = Named_Thms
(
  val name = @{binding success_intros}
  val description = "introduction rules for success"
) *}

setup Success_Intros.setup

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


subsubsection {* Predicate for a simple relational calculus *}

text {*
  The @{text effect} predicate states that when a computation @{text c}
  runs with the heap @{text h} will result in return value @{text r}
  and a heap @{text "h'"}, i.e.~no exception occurs.
*}  

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

ML {* structure Crel_Intros = Named_Thms
(
  val name = @{binding effect_intros}
  val description = "introduction rules for effect"
) *}

ML {* structure Crel_Elims = Named_Thms
(
  val name = @{binding effect_elims}
  val description = "elimination rules for effect"
) *}

setup "Crel_Intros.setup #> Crel_Elims.setup"

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


subsubsection {* Monad combinators *}

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

definition raise :: "string \<Rightarrow> 'a Heap" where -- {* the string is just decoration *}
  [code del]: "raise s = Heap (\<lambda>_. None)"

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

setup {*
  Adhoc_Overloading.add_variant 
    @{const_name Monad_Syntax.bind} @{const_name Heap_Monad.bind}
*}

lemma execute_bind [execute_simps]:
  "execute f h = Some (x, h') \<Longrightarrow> execute (f \<guillemotright>= g) h = execute (g x) h'"
  "execute f h = None \<Longrightarrow> execute (f \<guillemotright>= g) h = None"
  by (simp_all add: bind_def)

lemma execute_bind_case:
  "execute (f \<guillemotright>= g) h = (case (execute f h) of
    Some (x, h') \<Rightarrow> execute (g x) h' | None \<Rightarrow> None)"
  by (simp add: bind_def)

lemma execute_bind_success:
  "success f h \<Longrightarrow> execute (f \<guillemotright>= g) h = execute (g (fst (the (execute f h)))) (snd (the (execute f h)))"
  by (cases f h rule: Heap_cases) (auto elim!: successE simp add: bind_def)

lemma success_bind_executeI:
  "execute f h = Some (x, h') \<Longrightarrow> success (g x) h' \<Longrightarrow> success (f \<guillemotright>= g) h"
  by (auto intro!: successI elim!: successE simp add: bind_def)

lemma success_bind_effectI [success_intros]:
  "effect f h h' x \<Longrightarrow> success (g x) h' \<Longrightarrow> success (f \<guillemotright>= g) h"
  by (auto simp add: effect_def success_def bind_def)

lemma effect_bindI [effect_intros]:
  assumes "effect f h h' r" "effect (g r) h' h'' r'"
  shows "effect (f \<guillemotright>= g) h h'' r'"
  using assms
  apply (auto intro!: effectI elim!: effectE successE)
  apply (subst execute_bind, simp_all)
  done

lemma effect_bindE [effect_elims]:
  assumes "effect (f \<guillemotright>= g) h h'' r'"
  obtains h' r where "effect f h h' r" "effect (g r) h' h'' r'"
  using assms by (auto simp add: effect_def bind_def split: option.split_asm)

lemma execute_bind_eq_SomeI:
  assumes "execute f h = Some (x, h')"
    and "execute (g x) h' = Some (y, h'')"
  shows "execute (f \<guillemotright>= g) h = Some (y, h'')"
  using assms by (simp add: bind_def)

lemma return_bind [simp]: "return x \<guillemotright>= f = f x"
  by (rule Heap_eqI) (simp add: execute_bind execute_simps)

lemma bind_return [simp]: "f \<guillemotright>= return = f"
  by (rule Heap_eqI) (simp add: bind_def execute_simps split: option.splits)

lemma bind_bind [simp]: "(f \<guillemotright>= g) \<guillemotright>= k = (f :: 'a Heap) \<guillemotright>= (\<lambda>x. g x \<guillemotright>= k)"
  by (rule Heap_eqI) (simp add: bind_def execute_simps split: option.splits)

lemma raise_bind [simp]: "raise e \<guillemotright>= f = raise e"
  by (rule Heap_eqI) (simp add: execute_simps)


subsection {* Generic combinators *}

subsubsection {* Assertions *}

definition assert :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a Heap" where
  "assert P x = (if P x then return x else raise ''assert'')"

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
  shows "(assert P x >>= f) = (assert P' x >>= f')"
  by (rule Heap_eqI) (insert assms, simp add: assert_def)


subsubsection {* Plain lifting *}

definition lift :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b Heap" where
  "lift f = return o f"

lemma lift_collapse [simp]:
  "lift f x = return (f x)"
  by (simp add: lift_def)

lemma bind_lift:
  "(f \<guillemotright>= lift g) = (f \<guillemotright>= (\<lambda>x. return (g x)))"
  by (simp add: lift_def comp_def)


subsubsection {* Iteration -- warning: this is rarely useful! *}

primrec fold_map :: "('a \<Rightarrow> 'b Heap) \<Rightarrow> 'a list \<Rightarrow> 'b list Heap" where
  "fold_map f [] = return []"
| "fold_map f (x # xs) = do {
     y \<leftarrow> f x;
     ys \<leftarrow> fold_map f xs;
     return (y # ys)
   }"

lemma fold_map_append:
  "fold_map f (xs @ ys) = fold_map f xs \<guillemotright>= (\<lambda>xs. fold_map f ys \<guillemotright>= (\<lambda>ys. return (xs @ ys)))"
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


subsection {* Partial function definition setup *}

definition Heap_ord :: "'a Heap \<Rightarrow> 'a Heap \<Rightarrow> bool" where
  "Heap_ord = img_ord execute (fun_ord option_ord)"

definition Heap_lub :: "'a Heap set \<Rightarrow> 'a Heap" where
  "Heap_lub = img_lub execute Heap (fun_lub (flat_lub None))"

interpretation heap!: partial_function_definitions Heap_ord Heap_lub
proof -
  have "partial_function_definitions (fun_ord option_ord) (fun_lub (flat_lub None))"
    by (rule partial_function_lift) (rule flat_interpretation)
  then have "partial_function_definitions (img_ord execute (fun_ord option_ord))
      (img_lub execute Heap (fun_lub (flat_lub None)))"
    by (rule partial_function_image) (auto intro: Heap_eqI)
  then show "partial_function_definitions Heap_ord Heap_lub"
    by (simp only: Heap_ord_def Heap_lub_def)
qed

declaration {* Partial_Function.init "heap" @{term heap.fixp_fun}
  @{term heap.mono_body} @{thm heap.fixp_rule_uc} NONE *}


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

lemma bind_mono[partial_function_mono]:
  assumes mf: "mono_Heap B" and mg: "\<And>y. mono_Heap (\<lambda>f. C y f)"
  shows "mono_Heap (\<lambda>f. B f \<guillemotright>= (\<lambda>y. C y f))"
proof (rule monotoneI)
  fix f g :: "'a \<Rightarrow> 'b Heap" assume fg: "fun_ord Heap_ord f g"
  from mf
  have 1: "Heap_ord (B f) (B g)" by (rule monotoneD) (rule fg)
  from mg
  have 2: "\<And>y'. Heap_ord (C y' f) (C y' g)" by (rule monotoneD) (rule fg)

  have "Heap_ord (B f \<guillemotright>= (\<lambda>y. C y f)) (B g \<guillemotright>= (\<lambda>y. C y f))"
    (is "Heap_ord ?L ?R")
  proof (rule Heap_ordI)
    fix h
    from 1 show "execute ?L h = None \<or> execute ?L h = execute ?R h"
      by (rule Heap_ordE[where h = h]) (auto simp: execute_bind_case)
  qed
  also
  have "Heap_ord (B g \<guillemotright>= (\<lambda>y'. C y' f)) (B g \<guillemotright>= (\<lambda>y'. C y' g))"
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
  show "Heap_ord (B f \<guillemotright>= (\<lambda>y. C y f)) (B g \<guillemotright>= (\<lambda>y'. C y' g))" .
qed


subsection {* Code generator setup *}

subsubsection {* Logical intermediate layer *}

definition raise' :: "String.literal \<Rightarrow> 'a Heap" where
  [code del]: "raise' s = raise (explode s)"

lemma [code_post]: "raise' (STR s) = raise s"
unfolding raise'_def by (simp add: STR_inverse)

lemma raise_raise' [code_unfold]:
  "raise s = raise' (STR s)"
  unfolding raise'_def by (simp add: STR_inverse)

code_datatype raise' -- {* avoid @{const "Heap"} formally *}


subsubsection {* SML and OCaml *}

code_type Heap (SML "unit/ ->/ _")
code_const bind (SML "!(fn/ f'_/ =>/ fn/ ()/ =>/ f'_/ (_/ ())/ ())")
code_const return (SML "!(fn/ ()/ =>/ _)")
code_const Heap_Monad.raise' (SML "!(raise/ Fail/ _)")

code_type Heap (OCaml "unit/ ->/ _")
code_const bind (OCaml "!(fun/ f'_/ ()/ ->/ f'_/ (_/ ())/ ())")
code_const return (OCaml "!(fun/ ()/ ->/ _)")
code_const Heap_Monad.raise' (OCaml "failwith")


subsubsection {* Haskell *}

text {* Adaption layer *}

code_include Haskell "Heap"
{*import qualified Control.Monad;
import qualified Control.Monad.ST;
import qualified Data.STRef;
import qualified Data.Array.ST;

import Natural;

type RealWorld = Control.Monad.ST.RealWorld;
type ST s a = Control.Monad.ST.ST s a;
type STRef s a = Data.STRef.STRef s a;
type STArray s a = Data.Array.ST.STArray s Natural a;

newSTRef = Data.STRef.newSTRef;
readSTRef = Data.STRef.readSTRef;
writeSTRef = Data.STRef.writeSTRef;

newArray :: Natural -> a -> ST s (STArray s a);
newArray k = Data.Array.ST.newArray (0, k);

newListArray :: [a] -> ST s (STArray s a);
newListArray xs = Data.Array.ST.newListArray (0, (fromInteger . toInteger . length) xs) xs;

newFunArray :: Natural -> (Natural -> a) -> ST s (STArray s a);
newFunArray k f = Data.Array.ST.newListArray (0, k) (map f [0..k-1]);

lengthArray :: STArray s a -> ST s Natural;
lengthArray a = Control.Monad.liftM snd (Data.Array.ST.getBounds a);

readArray :: STArray s a -> Natural -> ST s a;
readArray = Data.Array.ST.readArray;

writeArray :: STArray s a -> Natural -> a -> ST s ();
writeArray = Data.Array.ST.writeArray;*}

code_reserved Haskell Heap

text {* Monad *}

code_type Heap (Haskell "Heap.ST/ Heap.RealWorld/ _")
code_monad bind Haskell
code_const return (Haskell "return")
code_const Heap_Monad.raise' (Haskell "error")


subsubsection {* Scala *}

code_include Scala "Heap"
{*object Heap {
  def bind[A, B](f: Unit => A, g: A => Unit => B): Unit => B = (_: Unit) => g (f ()) ()
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
  import collection.mutable.ArraySeq
  def alloc[A](n: Natural)(x: A): ArraySeq[A] =
    ArraySeq.fill(n.as_Int)(x)
  def make[A](n: Natural)(f: Natural => A): ArraySeq[A] =
    ArraySeq.tabulate(n.as_Int)((k: Int) => f(Natural(k)))
  def len[A](a: ArraySeq[A]): Natural =
    Natural(a.length)
  def nth[A](a: ArraySeq[A], n: Natural): A =
    a(n.as_Int)
  def upd[A](a: ArraySeq[A], n: Natural, x: A): Unit =
    a.update(n.as_Int, x)
  def freeze[A](a: ArraySeq[A]): List[A] =
    a.toList
}
*}

code_reserved Scala Heap Ref Array

code_type Heap (Scala "Unit/ =>/ _")
code_const bind (Scala "Heap.bind")
code_const return (Scala "('_: Unit)/ =>/ _")
code_const Heap_Monad.raise' (Scala "!error((_))")


subsubsection {* Target variants with less units *}

setup {*

let

open Code_Thingol;

fun imp_program naming =
  let
    fun is_const c = case lookup_const naming c
     of SOME c' => (fn c'' => c' = c'')
      | NONE => K false;
    val is_bind = is_const @{const_name bind};
    val is_return = is_const @{const_name return};
    val dummy_name = "";
    val dummy_case_term = IVar NONE;
    (*assumption: dummy values are not relevant for serialization*)
    val (unitt, unitT) = case lookup_const naming @{const_name Unity}
     of SOME unit' =>
        let val unitT = the (lookup_tyco naming @{type_name unit}) `%% []
        in (IConst (unit', ((([], []), ([], unitT)), false)), unitT) end
      | NONE => error ("Must include " ^ @{const_name Unity} ^ " in generated constants.");
    fun dest_abs ((v, ty) `|=> t, _) = ((v, ty), t)
      | dest_abs (t, ty) =
          let
            val vs = fold_varnames cons t [];
            val v = singleton (Name.variant_list vs) "x";
            val ty' = (hd o fst o unfold_fun) ty;
          in ((SOME v, ty'), t `$ IVar (SOME v)) end;
    fun force (t as IConst (c, _) `$ t') = if is_return c
          then t' else t `$ unitt
      | force t = t `$ unitt;
    fun tr_bind'' [(t1, _), (t2, ty2)] =
      let
        val ((v, ty), t) = dest_abs (t2, ty2);
      in ICase (((force t1, ty), [(IVar v, tr_bind' t)]), dummy_case_term) end
    and tr_bind' t = case unfold_app t
     of (IConst (c, ((_, (ty1 :: ty2 :: _, _)), _)), [x1, x2]) => if is_bind c
          then tr_bind'' [(x1, ty1), (x2, ty2)]
          else force t
      | _ => force t;
    fun imp_monad_bind'' ts = (SOME dummy_name, unitT) `|=> ICase (((IVar (SOME dummy_name), unitT),
      [(unitt, tr_bind'' ts)]), dummy_case_term)
    fun imp_monad_bind' (const as (c, ((_, (tys, _)), _))) ts = if is_bind c then case (ts, tys)
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
      | imp_monad_bind (ICase (((t, ty), pats), t0)) = ICase
          (((imp_monad_bind t, ty),
            (map o pairself) imp_monad_bind pats),
              imp_monad_bind t0);

  in (Graph.map o K o map_terms_stmt) imp_monad_bind end;

in

Code_Target.extend_target ("SML_imp", ("SML", imp_program))
#> Code_Target.extend_target ("OCaml_imp", ("OCaml", imp_program))
#> Code_Target.extend_target ("Scala_imp", ("Scala", imp_program))

end

*}

hide_const (open) Heap heap guard raise' fold_map

end
