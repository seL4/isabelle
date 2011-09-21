(* Author: Tobias Nipkow *)

theory AbsInt2
imports AbsInt1_ivl
begin

subsection "Widening and Narrowing"

text{* The assumptions about widen and narrow are merely sanity checks for
us. Normaly, they serve two purposes. Together with a further assumption that
certain chains become stationary, they permit to prove termination of the
fixed point iteration, which we do not --- we limit the number of iterations
as before. The second purpose of the narrowing assumptions is to prove that
the narrowing iteration keeps on producing post-fixed points and that it goes
down. However, this requires the function being iterated to be
monotone. Unfortunately, abstract interpretation with widening is not
monotone. Hence the (recursive) abstract interpretation of a loop body that
again contains a loop may result in a non-monotone function. Therefore our
narrowing interation needs to check at every step that a post-fixed point is
maintained, and we cannot prove that the precision increases. *}

class WN = SL_top +
fixes widen :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<nabla>" 65)
assumes widen: "y \<sqsubseteq> x \<nabla> y"
fixes narrow :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<triangle>" 65)
assumes narrow1: "y \<sqsubseteq> x \<Longrightarrow> y \<sqsubseteq> x \<triangle> y"
assumes narrow2: "y \<sqsubseteq> x \<Longrightarrow> x \<triangle> y \<sqsubseteq> x"
begin

fun iter_up :: "('a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a" where
"iter_up f 0 x = Top" |
"iter_up f (Suc n) x =
  (let fx = f x in if fx \<sqsubseteq> x then x else iter_up f n (x \<nabla> fx))"

lemma iter_up_pfp: "f(iter_up f n x) \<sqsubseteq> iter_up f n x"
apply (induction n arbitrary: x)
 apply (simp)
apply (simp add: Let_def)
done

fun iter_down :: "('a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a" where
"iter_down f 0 x = x" |
"iter_down f (Suc n) x =
  (let y = x \<triangle> f x in if f y \<sqsubseteq> y then iter_down f n y else x)"

lemma iter_down_pfp: "f x \<sqsubseteq> x \<Longrightarrow> f(iter_down f n x) \<sqsubseteq> iter_down f n x"
apply (induction n arbitrary: x)
 apply (simp)
apply (simp add: Let_def)
done

definition iter' :: "nat \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
"iter' m n f x =
  (let f' = (\<lambda>y. x \<squnion> f y) in iter_down f' n (iter_up f' m x))"

lemma iter'_pfp_above:
shows "f(iter' m n f x0) \<sqsubseteq> iter' m n f x0"
and "x0 \<sqsubseteq> iter' m n f x0"
using iter_up_pfp[of "\<lambda>x. x0 \<squnion> f x"] iter_down_pfp[of "\<lambda>x. x0 \<squnion> f x"]
by(auto simp add: iter'_def Let_def)

end


instantiation ivl :: WN
begin

definition "widen_ivl ivl1 ivl2 =
  ((*if is_empty ivl1 then ivl2 else if is_empty ivl2 then ivl1 else*)
     case (ivl1,ivl2) of (I l1 h1, I l2 h2) \<Rightarrow>
       I (if le_option False l2 l1 \<and> l2 \<noteq> l1 then None else l2)
         (if le_option True h1 h2 \<and> h1 \<noteq> h2 then None else h2))"

definition "narrow_ivl ivl1 ivl2 =
  ((*if is_empty ivl1 \<or> is_empty ivl2 then empty else*)
     case (ivl1,ivl2) of (I l1 h1, I l2 h2) \<Rightarrow>
       I (if l1 = None then l2 else l1)
         (if h1 = None then h2 else h1))"

instance
proof qed
  (auto simp add: widen_ivl_def narrow_ivl_def le_option_def le_ivl_def empty_def split: ivl.split option.split if_splits)

end

instantiation astate :: (WN)WN
begin

definition "widen_astate F1 F2 =
  FunDom (\<lambda>x. fun F1 x \<nabla> fun F2 x) (inter_list (dom F1) (dom F2))"

definition "narrow_astate F1 F2 =
  FunDom (\<lambda>x. fun F1 x \<triangle> fun F2 x) (inter_list (dom F1) (dom F2))"

instance
proof
  case goal1 thus ?case
    by(simp add: widen_astate_def le_astate_def lookup_def widen)
next
  case goal2 thus ?case
    by(auto simp: narrow_astate_def le_astate_def lookup_def narrow1)
next
  case goal3 thus ?case
    by(auto simp: narrow_astate_def le_astate_def lookup_def narrow2)
qed

end

instantiation up :: (WN)WN
begin

fun widen_up where
"widen_up bot x = x" |
"widen_up x bot = x" |
"widen_up (Up x) (Up y) = Up(x \<nabla> y)"

fun narrow_up where
"narrow_up bot x = bot" |
"narrow_up x bot = bot" |
"narrow_up (Up x) (Up y) = Up(x \<triangle> y)"

instance
proof
  case goal1 show ?case
    by(induct x y rule: widen_up.induct) (simp_all add: widen)
next
  case goal2 thus ?case
    by(induct x y rule: narrow_up.induct) (simp_all add: narrow1)
next
  case goal3 thus ?case
    by(induct x y rule: narrow_up.induct) (simp_all add: narrow2)
qed

end

interpretation
  Abs_Int1 rep_ivl num_ivl plus_ivl inv_plus_ivl inv_less_ivl "(iter' 3 2)"
defines afilter_ivl' is afilter
and bfilter_ivl' is bfilter
and AI_ivl' is AI
and aval_ivl' is aval'
proof qed (auto simp: iter'_pfp_above)

value [code] "list_up(AI_ivl' test3_ivl Top)"
value [code] "list_up(AI_ivl' test4_ivl Top)"

end
