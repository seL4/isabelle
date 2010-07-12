theory Relational 
imports Array Ref
begin

lemma crel_assert_eq: "(\<And>h h' r. crel f h h' r \<Longrightarrow> P r) \<Longrightarrow> f \<guillemotright>= assert P = f"
unfolding crel_def bind_def Let_def assert_def
  raise_def return_def prod_case_beta
apply (cases f)
apply simp
apply (simp add: expand_fun_eq split_def)
apply (auto split: option.split)
done

lemma crel_option_caseI:
  assumes "\<And>y. x = Some y \<Longrightarrow> crel (s y) h h' r"
  assumes "x = None \<Longrightarrow> crel n h h' r"
  shows "crel (case x of None \<Rightarrow> n | Some y \<Rightarrow> s y) h h' r"
using assms
by (auto split: option.split)

lemma crelI2:
  assumes "\<exists>h' rs'. crel f h h' rs' \<and> (\<exists>h'' rs. crel (g rs') h' h'' rs)"
  shows "\<exists>h'' rs. crel (f\<guillemotright>= g) h h'' rs"
  oops

lemma crel_ifI2:
  assumes "c \<Longrightarrow> \<exists>h' r. crel t h h' r"
  "\<not> c \<Longrightarrow> \<exists>h' r. crel e h h' r"
  shows "\<exists> h' r. crel (if c then t else e) h h' r"
  oops

lemma crel_option_case:
  assumes "crel (case x of None \<Rightarrow> n | Some y \<Rightarrow> s y) h h' r"
  obtains "x = None" "crel n h h' r"
        | y where "x = Some y" "crel (s y) h h' r" 
  using assms unfolding crel_def by (auto split: option.splits)

lemma crel_fold_map:
  assumes "crel (Heap_Monad.fold_map f xs) h h' r"
  assumes "\<And>h h'. P f [] h h' []"
  assumes "\<And>h h1 h' x xs y ys. \<lbrakk> crel (f x) h h1 y; crel (Heap_Monad.fold_map f xs) h1 h' ys; P f xs h1 h' ys \<rbrakk> \<Longrightarrow> P f (x#xs) h h' (y#ys)"
  shows "P f xs h h' r"
using assms(1)
proof (induct xs arbitrary: h h' r)
  case Nil  with assms(2) show ?case
    by (auto elim: crel_returnE)
next
  case (Cons x xs)
  from Cons(2) obtain h1 y ys where crel_f: "crel (f x) h h1 y"
    and crel_fold_map: "crel (Heap_Monad.fold_map f xs) h1 h' ys"
    and r_def: "r = y#ys"
    unfolding fold_map.simps
    by (auto elim!: crel_bindE crel_returnE)
  from Cons(1)[OF crel_fold_map] crel_fold_map crel_f assms(3) r_def
  show ?case by auto
qed

lemma upt_conv_Cons':
  assumes "Suc a \<le> b"
  shows "[b - Suc a..<b] = (b - Suc a)#[b - a..<b]"
proof -
  from assms have l: "b - Suc a < b" by arith
  from assms have "Suc (b - Suc a) = b - a" by arith
  with l show ?thesis by (simp add: upt_conv_Cons)
qed

lemma crel_fold_map_nth:
  assumes
  "crel (Heap_Monad.fold_map (Array.nth a) [Array.length a h - n..<Array.length a h]) h h' xs"
  assumes "n \<le> Array.length a h"
  shows "h = h' \<and> xs = drop (Array.length a h - n) (get_array a h)"
using assms
proof (induct n arbitrary: xs h h')
  case 0 thus ?case
    by (auto elim!: crel_returnE simp add: Array.length_def)
next
  case (Suc n)
  from Suc(3) have "[Array.length a h - Suc n..<Array.length a h] = (Array.length a h - Suc n)#[Array.length a h - n..<Array.length a h]"
    by (simp add: upt_conv_Cons')
  with Suc(2) obtain r where
    crel_fold_map: "crel (Heap_Monad.fold_map (Array.nth a) [Array.length a h - n..<Array.length a h]) h h' r"
    and xs_def: "xs = get_array a h ! (Array.length a h - Suc n) # r"
    by (auto elim!: crel_bindE crel_nthE crel_returnE)
  from Suc(3) have "Array.length a h - n = Suc (Array.length a h - Suc n)" 
    by arith
  with Suc.hyps[OF crel_fold_map] xs_def show ?case
    unfolding Array.length_def
    by (auto simp add: nth_drop')
qed

lemma crel_fold_map_map_entry_remains:
  assumes "crel (Heap_Monad.fold_map (\<lambda>n. map_entry n f a) [Array.length a h - n..<Array.length a h]) h h' r"
  assumes "i < Array.length a h - n"
  shows "get_array a h ! i = get_array a h' ! i"
using assms
proof (induct n arbitrary: h h' r)
  case 0
  thus ?case
    by (auto elim: crel_returnE)
next
  case (Suc n)
  let ?h1 = "Array.change a (Array.length a h - Suc n) (f (get_array a h ! (Array.length a h - Suc n))) h"
  from Suc(3) have "[Array.length a h - Suc n..<Array.length a h] = (Array.length a h - Suc n)#[Array.length a h - n..<Array.length a h]"
    by (simp add: upt_conv_Cons')
  from Suc(2) this obtain r where
    crel_fold_map: "crel (Heap_Monad.fold_map (\<lambda>n. map_entry n f a) [Array.length a h - n..<Array.length a h]) ?h1 h' r"
    by (auto simp add: elim!: crel_bindE crel_map_entryE crel_returnE)
  have length_remains: "Array.length a ?h1 = Array.length a h" by simp
  from crel_fold_map have crel_fold_map': "crel (Heap_Monad.fold_map (\<lambda>n. map_entry n f a) [Array.length a ?h1 - n..<Array.length a ?h1]) ?h1 h' r"
    by simp
  from Suc(1)[OF this] length_remains Suc(3) show ?case by simp
qed

lemma crel_fold_map_map_entry_changes:
  assumes "crel (Heap_Monad.fold_map (\<lambda>n. map_entry n f a) [Array.length a h - n..<Array.length a h]) h h' r"
  assumes "n \<le> Array.length a h"  
  assumes "i \<ge> Array.length a h - n"
  assumes "i < Array.length a h"
  shows "get_array a h' ! i = f (get_array a h ! i)"
using assms
proof (induct n arbitrary: h h' r)
  case 0
  thus ?case
    by (auto elim!: crel_returnE)
next
  case (Suc n)
  let ?h1 = "Array.change a (Array.length a h - Suc n) (f (get_array a h ! (Array.length a h - Suc n))) h"
  from Suc(3) have "[Array.length a h - Suc n..<Array.length a h] = (Array.length a h - Suc n)#[Array.length a h - n..<Array.length a h]"
    by (simp add: upt_conv_Cons')
  from Suc(2) this obtain r where
    crel_fold_map: "crel (Heap_Monad.fold_map (\<lambda>n. map_entry n f a) [Array.length a h - n..<Array.length a h]) ?h1 h' r"
    by (auto simp add: elim!: crel_bindE crel_map_entryE crel_returnE)
  have length_remains: "Array.length a ?h1 = Array.length a h" by simp
  from Suc(3) have less: "Array.length a h - Suc n < Array.length a h - n" by arith
  from Suc(3) have less2: "Array.length a h - Suc n < Array.length a h" by arith
  from Suc(4) length_remains have cases: "i = Array.length a ?h1 - Suc n \<or> i \<ge> Array.length a ?h1 - n" by arith
  from crel_fold_map have crel_fold_map': "crel (Heap_Monad.fold_map (\<lambda>n. map_entry n f a) [Array.length a ?h1 - n..<Array.length a ?h1]) ?h1 h' r"
    by simp
  from Suc(1)[OF this] cases Suc(3) Suc(5) length_remains
    crel_fold_map_map_entry_remains[OF this, of "Array.length a h - Suc n", symmetric] less less2
  show ?case
    by (auto simp add: nth_list_update_eq Array.length_def)
qed

lemma crel_fold_map_map_entry_length:
  assumes "crel (Heap_Monad.fold_map (\<lambda>n. map_entry n f a) [Array.length a h - n..<Array.length a h]) h h' r"
  assumes "n \<le> Array.length a h"
  shows "Array.length a h' = Array.length a h"
using assms
proof (induct n arbitrary: h h' r)
  case 0
  thus ?case by (auto elim!: crel_returnE)
next
  case (Suc n)
  let ?h1 = "Array.change a (Array.length a h - Suc n) (f (get_array a h ! (Array.length a h - Suc n))) h"
  from Suc(3) have "[Array.length a h - Suc n..<Array.length a h] = (Array.length a h - Suc n)#[Array.length a h - n..<Array.length a h]"
    by (simp add: upt_conv_Cons')
  from Suc(2) this obtain r where 
    crel_fold_map: "crel (Heap_Monad.fold_map (\<lambda>n. map_entry n f a) [Array.length a h - n..<Array.length a h]) ?h1 h' r"
    by (auto elim!: crel_bindE crel_map_entryE crel_returnE)
  have length_remains: "Array.length a ?h1 = Array.length a h" by simp
  from crel_fold_map have crel_fold_map': "crel (Heap_Monad.fold_map (\<lambda>n. map_entry n f a) [Array.length a ?h1 - n..<Array.length a ?h1]) ?h1 h' r"
    by simp
  from Suc(1)[OF this] length_remains Suc(3) show ?case by simp
qed

lemma crel_fold_map_map_entry:
assumes "crel (Heap_Monad.fold_map (\<lambda>n. map_entry n f a) [0..<Array.length a h]) h h' r"
  shows "get_array a h' = List.map f (get_array a h)"
proof -
  from assms have "crel (Heap_Monad.fold_map (\<lambda>n. map_entry n f a) [Array.length a h - Array.length a h..<Array.length a h]) h h' r" by simp
  from crel_fold_map_map_entry_length[OF this]
  crel_fold_map_map_entry_changes[OF this] show ?thesis
    unfolding Array.length_def
    by (auto intro: nth_equalityI)
qed

lemma success_fold_map_map_entry:
  assumes "n \<le> Array.length a h"
  shows "success (Heap_Monad.fold_map (\<lambda>n. map_entry n f a) [Array.length a h - n..<Array.length a h]) h"
using assms
proof (induct n arbitrary: h)
  case 0
  thus ?case by (auto intro: success_returnI)
next
  case (Suc n)
  from Suc.prems have "[Array.length a h - Suc n..<Array.length a h] =
    (Array.length a h - Suc n) # [Array.length a h - n..<Array.length a h]"
    by (simp add: upt_conv_Cons')
  with Suc.hyps [of "(Array.change a (Array.length a h - Suc n) (f (get_array a h ! (Array.length a h - Suc n))) h)"] Suc.prems show ?case apply -
    apply (auto simp add: execute_simps execute_bind_success intro!: successI success_returnI success_map_entryI elim: crel_map_entryE)
    apply (subst execute_bind) apply (auto simp add: execute_simps execute_bind_success intro: execute_bind)
    done
qed

lemma MREC_induct:
  assumes "crel (MREC f g x) h h' r"
  assumes "\<And> x h h' r. crel (f x) h h' (Inl r) \<Longrightarrow> P x h h' r"
  assumes "\<And> x h h1 h2 h' s z r. crel (f x) h h1 (Inr s) \<Longrightarrow> crel (MREC f g s) h1 h2 z \<Longrightarrow> P s h1 h2 z
    \<Longrightarrow> crel (g x s z) h2 h' r \<Longrightarrow> P x h h' r"
  shows "P x h h' r"
proof (rule MREC_pinduct[OF assms(1) [unfolded crel_def]])
  fix x h h1 h2 h' s z r
  assume "Heap_Monad.execute (f x) h = Some (Inr s, h1)"
    "Heap_Monad.execute (MREC f g s) h1 = Some (z, h2)"
    "P s h1 h2 z"
    "Heap_Monad.execute (g x s z) h2 = Some (r, h')"
  from assms(3) [unfolded crel_def, OF this(1) this(2) this(3) this(4)]
  show "P x h h' r" .
next
qed (auto simp add: assms(2)[unfolded crel_def])

end
