(* Author: Tobias Nipkow *)

theory Abs_Int2
imports Abs_Int1_ivl
begin


subsection "Widening and Narrowing"

class WN = SL_top +
fixes widen :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<nabla>" 65)
assumes widen: "y \<sqsubseteq> x \<nabla> y"
fixes narrow :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<triangle>" 65)
assumes narrow1: "y \<sqsubseteq> x \<Longrightarrow> y \<sqsubseteq> x \<triangle> y"
assumes narrow2: "y \<sqsubseteq> x \<Longrightarrow> x \<triangle> y \<sqsubseteq> x"


instantiation ivl :: WN
begin

definition "widen_ivl ivl1 ivl2 =
  ((*if is_empty ivl1 then ivl2 else
   if is_empty ivl2 then ivl1 else*)
     case (ivl1,ivl2) of (I l1 h1, I l2 h2) \<Rightarrow>
       I (if le_option False l2 l1 \<and> l2 \<noteq> l1 then None else l1)
         (if le_option True h1 h2 \<and> h1 \<noteq> h2 then None else h1))"

definition "narrow_ivl ivl1 ivl2 =
  ((*if is_empty ivl1 \<or> is_empty ivl2 then empty else*)
     case (ivl1,ivl2) of (I l1 h1, I l2 h2) \<Rightarrow>
       I (if l1 = None then l2 else l1)
         (if h1 = None then h2 else h1))"

instance
proof qed
  (auto simp add: widen_ivl_def narrow_ivl_def le_option_def le_ivl_def empty_def split: ivl.split option.split if_splits)

end

instantiation st :: (WN)WN
begin

definition "widen_st F1 F2 =
  FunDom (\<lambda>x. fun F1 x \<nabla> fun F2 x) (inter_list (dom F1) (dom F2))"

definition "narrow_st F1 F2 =
  FunDom (\<lambda>x. fun F1 x \<triangle> fun F2 x) (inter_list (dom F1) (dom F2))"

instance
proof
  case goal1 thus ?case
    by(simp add: widen_st_def le_st_def lookup_def widen)
next
  case goal2 thus ?case
    by(auto simp: narrow_st_def le_st_def lookup_def narrow1)
next
  case goal3 thus ?case
    by(auto simp: narrow_st_def le_st_def lookup_def narrow2)
qed

end

instantiation up :: (WN)WN
begin

fun widen_up where
"widen_up Bot x = x" |
"widen_up x Bot = x" |
"widen_up (Up x) (Up y) = Up(x \<nabla> y)"

fun narrow_up where
"narrow_up Bot x = Bot" |
"narrow_up x Bot = Bot" |
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

fun map2_acom :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a acom \<Rightarrow> 'a acom \<Rightarrow> 'a acom" where
"map2_acom f (SKIP {a1}) (SKIP {a2}) = (SKIP {f a1 a2})" |
"map2_acom f (x ::= e {a1}) (x' ::= e' {a2}) = (x ::= e {f a1 a2})" |
"map2_acom f (c1;c2) (c1';c2') = (map2_acom f c1 c1'; map2_acom f c2 c2')" |
"map2_acom f (IF b THEN c1 ELSE c2 {a1}) (IF b' THEN c1' ELSE c2' {a2}) =
  (IF b THEN map2_acom f c1 c1' ELSE map2_acom f c2 c2' {f a1 a2})" |
"map2_acom f ({a1} WHILE b DO c {a2}) ({a3} WHILE b' DO c' {a4}) =
  ({f a1 a3} WHILE b DO map2_acom f c c' {f a2 a4})"

abbreviation widen_acom :: "('a::WN)acom \<Rightarrow> 'a acom \<Rightarrow> 'a acom" (infix "\<nabla>\<^sub>c" 65)
where "widen_acom == map2_acom (op \<nabla>)"

abbreviation narrow_acom :: "('a::WN)acom \<Rightarrow> 'a acom \<Rightarrow> 'a acom" (infix "\<triangle>\<^sub>c" 65)
where "narrow_acom == map2_acom (op \<triangle>)"

lemma narrow1_acom: "y \<sqsubseteq> x \<Longrightarrow> y \<sqsubseteq> x \<triangle>\<^sub>c y"
by(induct y x rule: le_acom.induct) (simp_all add: narrow1)

lemma narrow2_acom: "y \<sqsubseteq> x \<Longrightarrow> x \<triangle>\<^sub>c y \<sqsubseteq> x"
by(induct y x rule: le_acom.induct) (simp_all add: narrow2)

fun iter_up :: "(('a::WN)acom \<Rightarrow> 'a acom) \<Rightarrow> nat \<Rightarrow> 'a acom \<Rightarrow> 'a acom" where
"iter_up f 0 x = \<top>\<^sub>c (strip x)" |
"iter_up f (Suc n) x =
  (let fx = f x in if fx \<sqsubseteq> x then x else iter_up f n (x \<nabla>\<^sub>c fx))"

abbreviation
  iter_down :: "(('a::WN)acom \<Rightarrow> 'a acom) \<Rightarrow> nat \<Rightarrow> 'a acom \<Rightarrow> 'a acom" where
"iter_down f n x == ((\<lambda>x. x \<triangle>\<^sub>c f x)^^n) x"

definition
  iter' :: "nat \<Rightarrow> nat \<Rightarrow> (('a::WN)acom \<Rightarrow> 'a acom) \<Rightarrow> 'a acom \<Rightarrow> 'a acom" where
"iter' m n f x = iter_down f n (iter_up f m x)"

lemma strip_map2_acom:
 "strip c1 = strip c2 \<Longrightarrow> strip(map2_acom f c1 c2) = strip c1"
by(induct f c1 c2 rule: map2_acom.induct) simp_all

lemma strip_iter_up: assumes "\<forall>c. strip(f c) = strip c"
shows "strip(iter_up f n c) = strip c"
apply (induction n arbitrary: c)
 apply (metis iter_up.simps(1) strip_Top_acom snd_conv)
apply (simp add:Let_def)
by (metis assms strip_map2_acom)

lemma iter_up_pfp: assumes "\<forall>c. strip(f c) = strip c"
shows "f(iter_up f n c) \<sqsubseteq> iter_up f n c"
apply (induction n arbitrary: c)
 apply(simp add: assms)
apply (simp add:Let_def)
done

lemma strip_iter_down: assumes "\<forall>c. strip(f c) = strip c"
shows "strip(iter_down f n c) = strip c"
apply (induction n arbitrary: c)
 apply(simp)
apply (simp add: strip_map2_acom assms)
done

lemma iter_down_pfp: assumes "mono f" and "f x0 \<sqsubseteq> x0" 
defines "x n == iter_down f n x0"
shows "f(x n) \<sqsubseteq> x n"
proof (induction n)
  case 0 show ?case by (simp add: x_def assms(2))
next
  case (Suc n)
  have "f (x (Suc n)) = f(x n \<triangle>\<^sub>c f(x n))" by(simp add: x_def)
  also have "\<dots> \<sqsubseteq> f(x n)" by(rule monoD[OF `mono f` narrow2_acom[OF Suc]])
  also have "\<dots> \<sqsubseteq> x n \<triangle>\<^sub>c f(x n)" by(rule narrow1_acom[OF Suc])
  also have "\<dots> = x(Suc n)" by(simp add: x_def)
  finally show ?case .
qed

lemma iter_down_down: assumes "mono f" and "f x0 \<sqsubseteq> x0" 
defines "x n == iter_down f n x0"
shows "x n \<sqsubseteq> x0"
proof (induction n)
  case 0 show ?case by(simp add: x_def)
next
  case (Suc n)
  have "x(Suc n) = x n \<triangle>\<^sub>c f(x n)" by(simp add: x_def)
  also have "\<dots> \<sqsubseteq> x n" unfolding x_def
    by(rule narrow2_acom[OF iter_down_pfp[OF assms(1), OF assms(2)]])
  also have "\<dots> \<sqsubseteq> x0" by(rule Suc)
  finally show ?case .
qed


lemma iter'_pfp: assumes "\<forall>c. strip (f c) = strip c" and "mono f"
shows "f (iter' m n f c) \<sqsubseteq> iter' m n f c"
using iter_up_pfp[of f] iter_down_pfp[of f]
by(auto simp add: iter'_def Let_def assms)

lemma strip_iter': assumes "\<forall>c. strip(f c) = strip c"
shows "strip(iter' m n f c) = strip c"
by(simp add: iter'_def strip_iter_down strip_iter_up assms)


interpretation
  Abs_Int1 rep_ivl num_ivl plus_ivl filter_plus_ivl filter_less_ivl "(iter' 20 5)"
defines afilter_ivl' is afilter
and bfilter_ivl' is bfilter
and step_ivl' is step
and AI_ivl' is AI
and aval_ivl' is aval'
proof qed (auto simp: iter'_pfp strip_iter')

value [code] "show_acom (AI_ivl test3_ivl)"
value [code] "show_acom (AI_ivl' test3_ivl)"

definition "step_up n = ((\<lambda>c. c \<nabla>\<^sub>c step_ivl \<top> c)^^n)"
definition "step_down n = ((\<lambda>c. c \<triangle>\<^sub>c step_ivl \<top> c)^^n)"

value [code] "show_acom (step_up 1 (\<bottom>\<^sub>c test3_ivl))"
value [code] "show_acom (step_up 2 (\<bottom>\<^sub>c test3_ivl))"
value [code] "show_acom (step_up 3 (\<bottom>\<^sub>c test3_ivl))"
value [code] "show_acom (step_up 4 (\<bottom>\<^sub>c test3_ivl))"
value [code] "show_acom (step_up 5 (\<bottom>\<^sub>c test3_ivl))"
value [code] "show_acom (step_down 1 (step_up 5 (\<bottom>\<^sub>c test3_ivl)))"
value [code] "show_acom (step_down 2 (step_up 5 (\<bottom>\<^sub>c test3_ivl)))"
value [code] "show_acom (step_down 3 (step_up 5 (\<bottom>\<^sub>c test3_ivl)))"

value [code] "show_acom (AI_ivl' test4_ivl)"
value [code] "show_acom (AI_ivl' test5_ivl)"
value [code] "show_acom (AI_ivl' test6_ivl)"

end
