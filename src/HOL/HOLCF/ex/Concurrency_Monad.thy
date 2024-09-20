(*  Title:      HOL/HOLCF/ex/Concurrency_Monad.thy
    Author:     Brian Huffman
*)

theory Concurrency_Monad
imports HOLCF
begin

text \<open>This file contains the concurrency monad example from
  Chapter 7 of the author's PhD thesis.\<close>

subsection \<open>State/nondeterminism monad, as a type synonym\<close>

type_synonym ('s, 'a) N = "'s \<rightarrow> ('a u \<otimes> 's u)\<natural>"

definition mapN :: "('a \<rightarrow> 'b) \<rightarrow> ('s, 'a) N \<rightarrow> ('s, 'b) N"
  where "mapN = (\<Lambda> f. cfun_map\<cdot>ID\<cdot>(convex_map\<cdot>(sprod_map\<cdot>(u_map\<cdot>f)\<cdot>ID)))"

definition unitN :: "'a \<rightarrow> ('s, 'a) N"
  where "unitN = (\<Lambda> x. (\<Lambda> s. convex_unit\<cdot>(:up\<cdot>x, up\<cdot>s:)))"

definition bindN :: "('s, 'a) N \<rightarrow> ('a \<rightarrow> ('s, 'b) N) \<rightarrow> ('s, 'b) N"
  where "bindN = (\<Lambda> c k. (\<Lambda> s. convex_bind\<cdot>(c\<cdot>s)\<cdot>(\<Lambda> (:up\<cdot>x, up\<cdot>s':). k\<cdot>x\<cdot>s')))"

definition plusN :: "('s, 'a) N \<rightarrow> ('s, 'a) N \<rightarrow> ('s, 'a) N"
  where "plusN = (\<Lambda> a b. (\<Lambda> s. convex_plus\<cdot>(a\<cdot>s)\<cdot>(b\<cdot>s)))"

lemma mapN_ID: "mapN\<cdot>ID = ID"
by (simp add: mapN_def domain_map_ID)

lemma mapN_mapN: "mapN\<cdot>f\<cdot>(mapN\<cdot>g\<cdot>m) = mapN\<cdot>(\<Lambda> x. f\<cdot>(g\<cdot>x))\<cdot>m"
unfolding mapN_def ID_def
by (simp add: cfun_map_map convex_map_map sprod_map_map u_map_map eta_cfun)

lemma mapN_unitN: "mapN\<cdot>f\<cdot>(unitN\<cdot>x) = unitN\<cdot>(f\<cdot>x)"
unfolding mapN_def unitN_def
by (simp add: cfun_map_def)

lemma bindN_unitN: "bindN\<cdot>(unitN\<cdot>a)\<cdot>f = f\<cdot>a"
by (simp add: unitN_def bindN_def eta_cfun)

lemma mapN_conv_bindN: "mapN\<cdot>f\<cdot>m = bindN\<cdot>m\<cdot>(unitN oo f)"
apply (simp add: mapN_def bindN_def unitN_def)
apply (rule cfun_eqI, simp)
apply (simp add: convex_map_def)
apply (rule cfun_arg_cong)
apply (rule cfun_eqI, simp, rename_tac p)
apply (case_tac p, simp)
apply (case_tac x, simp)
apply (case_tac y, simp)
apply simp
done

lemma bindN_unitN_right: "bindN\<cdot>m\<cdot>unitN = m"
proof -
  have "mapN\<cdot>ID\<cdot>m = m" by (simp add: mapN_ID)
  thus ?thesis by (simp add: mapN_conv_bindN)
qed

lemma bindN_bindN:
  "bindN\<cdot>(bindN\<cdot>m\<cdot>f)\<cdot>g = bindN\<cdot>m\<cdot>(\<Lambda> x. bindN\<cdot>(f\<cdot>x)\<cdot>g)"
apply (rule cfun_eqI, rename_tac s)
apply (simp add: bindN_def)
apply (simp add: convex_bind_bind)
apply (rule cfun_arg_cong)
apply (rule cfun_eqI, rename_tac w)
apply (case_tac w, simp)
apply (case_tac x, simp)
apply (case_tac y, simp)
apply simp
done

lemma mapN_bindN: "mapN\<cdot>f\<cdot>(bindN\<cdot>m\<cdot>g) = bindN\<cdot>m\<cdot>(\<Lambda> x. mapN\<cdot>f\<cdot>(g\<cdot>x))"
by (simp add: mapN_conv_bindN bindN_bindN)

lemma bindN_mapN: "bindN\<cdot>(mapN\<cdot>f\<cdot>m)\<cdot>g = bindN\<cdot>m\<cdot>(\<Lambda> x. g\<cdot>(f\<cdot>x))"
by (simp add: mapN_conv_bindN bindN_bindN bindN_unitN)

lemma mapN_plusN:
  "mapN\<cdot>f\<cdot>(plusN\<cdot>a\<cdot>b) = plusN\<cdot>(mapN\<cdot>f\<cdot>a)\<cdot>(mapN\<cdot>f\<cdot>b)"
unfolding mapN_def plusN_def by (simp add: cfun_map_def)

lemma plusN_commute: "plusN\<cdot>a\<cdot>b = plusN\<cdot>b\<cdot>a"
unfolding plusN_def by (simp add: convex_plus_commute)

lemma plusN_assoc: "plusN\<cdot>(plusN\<cdot>a\<cdot>b)\<cdot>c = plusN\<cdot>a\<cdot>(plusN\<cdot>b\<cdot>c)"
unfolding plusN_def by (simp add: convex_plus_assoc)

lemma plusN_absorb: "plusN\<cdot>a\<cdot>a = a"
unfolding plusN_def by (simp add: eta_cfun)


subsection \<open>Resumption-state-nondeterminism monad\<close>

domain ('s, 'a) R = Done (lazy "'a") | More (lazy "('s, ('s, 'a) R) N")

thm R.take_induct

lemma R_induct [case_names adm bottom Done More, induct type: R]:
  fixes P :: "('s, 'a) R \<Rightarrow> bool"
  assumes adm: "adm P"
  assumes bottom: "P \<bottom>"
  assumes Done: "\<And>x. P (Done\<cdot>x)"
  assumes More: "\<And>p c. (\<And>r::('s, 'a) R. P (p\<cdot>r)) \<Longrightarrow> P (More\<cdot>(mapN\<cdot>p\<cdot>c))"
  shows "P r"
proof (induct r rule: R.take_induct)
  show "adm P" by fact
next
  fix n
  show "P (R_take n\<cdot>r)"
  proof (induct n arbitrary: r)
    case 0 show ?case by (simp add: bottom)
  next
    case (Suc n r)
    show ?case
      apply (cases r)
      apply (simp add: bottom)
      apply (simp add: Done)
      using More [OF Suc]
      apply (simp add: mapN_def)
      done
  qed
qed

declare R.take_rews(2) [simp del]

lemma R_take_Suc_More [simp]:
  "R_take (Suc n)\<cdot>(More\<cdot>k) = More\<cdot>(mapN\<cdot>(R_take n)\<cdot>k)"
by (simp add: mapN_def R.take_rews(2))


subsection \<open>Map function\<close>

fixrec mapR :: "('a \<rightarrow> 'b) \<rightarrow> ('s, 'a) R \<rightarrow> ('s, 'b) R"
  where "mapR\<cdot>f\<cdot>(Done\<cdot>a) = Done\<cdot>(f\<cdot>a)"
  | "mapR\<cdot>f\<cdot>(More\<cdot>k) = More\<cdot>(mapN\<cdot>(mapR\<cdot>f)\<cdot>k)"

lemma mapR_strict [simp]: "mapR\<cdot>f\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

lemma mapR_mapR: "mapR\<cdot>f\<cdot>(mapR\<cdot>g\<cdot>r) = mapR\<cdot>(\<Lambda> x. f\<cdot>(g\<cdot>x))\<cdot>r"
by (induct r) (simp_all add: mapN_mapN)

lemma mapR_ID: "mapR\<cdot>ID\<cdot>r = r"
by (induct r) (simp_all add: mapN_mapN eta_cfun)

lemma "mapR\<cdot>f\<cdot>(mapR\<cdot>g\<cdot>r) = mapR\<cdot>(\<Lambda> x. f\<cdot>(g\<cdot>x))\<cdot>r"
apply (induct r)
apply simp
apply simp
apply simp
apply (simp (no_asm))
apply (simp (no_asm) add: mapN_mapN)
apply simp
done


subsection \<open>Monadic bind function\<close>

fixrec bindR :: "('s, 'a) R \<rightarrow> ('a \<rightarrow> ('s, 'b) R) \<rightarrow> ('s, 'b) R"
  where "bindR\<cdot>(Done\<cdot>x)\<cdot>k = k\<cdot>x"
  | "bindR\<cdot>(More\<cdot>c)\<cdot>k = More\<cdot>(mapN\<cdot>(\<Lambda> r. bindR\<cdot>r\<cdot>k)\<cdot>c)"

lemma bindR_strict [simp]: "bindR\<cdot>\<bottom>\<cdot>k = \<bottom>"
by fixrec_simp

lemma bindR_Done_right: "bindR\<cdot>r\<cdot>Done = r"
by (induct r) (simp_all add: mapN_mapN eta_cfun)

lemma mapR_conv_bindR: "mapR\<cdot>f\<cdot>r = bindR\<cdot>r\<cdot>(\<Lambda> x. Done\<cdot>(f\<cdot>x))"
by (induct r) (simp_all add: mapN_mapN)

lemma bindR_bindR: "bindR\<cdot>(bindR\<cdot>r\<cdot>f)\<cdot>g = bindR\<cdot>r\<cdot>(\<Lambda> x. bindR\<cdot>(f\<cdot>x)\<cdot>g)"
by (induct r) (simp_all add: mapN_mapN)

lemma "bindR\<cdot>(bindR\<cdot>r\<cdot>f)\<cdot>g = bindR\<cdot>r\<cdot>(\<Lambda> x. bindR\<cdot>(f\<cdot>x)\<cdot>g)"
apply (induct r)
apply (simp_all add: mapN_mapN)
done

subsection \<open>Zip function\<close>

fixrec zipR :: "('a \<rightarrow> 'b \<rightarrow> 'c) \<rightarrow> ('s, 'a) R \<rightarrow> ('s, 'b) R \<rightarrow> ('s, 'c) R"
  where zipR_Done_Done:
    "zipR\<cdot>f\<cdot>(Done\<cdot>x)\<cdot>(Done\<cdot>y) = Done\<cdot>(f\<cdot>x\<cdot>y)"
  | zipR_Done_More:
    "zipR\<cdot>f\<cdot>(Done\<cdot>x)\<cdot>(More\<cdot>b) =
      More\<cdot>(mapN\<cdot>(\<Lambda> r. zipR\<cdot>f\<cdot>(Done\<cdot>x)\<cdot>r)\<cdot>b)"
  | zipR_More_Done:
    "zipR\<cdot>f\<cdot>(More\<cdot>a)\<cdot>(Done\<cdot>y) =
      More\<cdot>(mapN\<cdot>(\<Lambda> r. zipR\<cdot>f\<cdot>r\<cdot>(Done\<cdot>y))\<cdot>a)"
  | zipR_More_More:
    "zipR\<cdot>f\<cdot>(More\<cdot>a)\<cdot>(More\<cdot>b) =
      More\<cdot>(plusN\<cdot>(mapN\<cdot>(\<Lambda> r. zipR\<cdot>f\<cdot>(More\<cdot>a)\<cdot>r)\<cdot>b)
                 \<cdot>(mapN\<cdot>(\<Lambda> r. zipR\<cdot>f\<cdot>r\<cdot>(More\<cdot>b))\<cdot>a))"

lemma zipR_strict1 [simp]: "zipR\<cdot>f\<cdot>\<bottom>\<cdot>r = \<bottom>"
by fixrec_simp

lemma zipR_strict2 [simp]: "zipR\<cdot>f\<cdot>r\<cdot>\<bottom> = \<bottom>"
by (fixrec_simp, cases r, simp_all)

abbreviation apR (infixl \<open>\<diamondop>\<close> 70)
  where "a \<diamondop> b \<equiv> zipR\<cdot>ID\<cdot>a\<cdot>b"

text \<open>Proofs that \<open>zipR\<close> satisfies the applicative functor laws:\<close>

lemma R_homomorphism: "Done\<cdot>f \<diamondop> Done\<cdot>x = Done\<cdot>(f\<cdot>x)"
  by simp

lemma R_identity: "Done\<cdot>ID \<diamondop> r = r"
  by (induct r, simp_all add: mapN_mapN eta_cfun)

lemma R_interchange: "r \<diamondop> Done\<cdot>x = Done\<cdot>(\<Lambda> f. f\<cdot>x) \<diamondop> r"
  by (induct r, simp_all add: mapN_mapN)

text \<open>The associativity rule is the hard one!\<close>

lemma R_associativity: "Done\<cdot>cfcomp \<diamondop> r1 \<diamondop> r2 \<diamondop> r3 = r1 \<diamondop> (r2 \<diamondop> r3)"
proof (induct r1 arbitrary: r2 r3)
  case (Done x1) thus ?case
  proof (induct r2 arbitrary: r3)
    case (Done x2) thus ?case
    proof (induct r3)
      case (More p3 c3) thus ?case (* Done/Done/More *)
        by (simp add: mapN_mapN)
    qed simp_all
  next
    case (More p2 c2) thus ?case
    proof (induct r3)
      case (Done x3) thus ?case (* Done/More/Done *)
        by (simp add: mapN_mapN)
    next
      case (More p3 c3) thus ?case (* Done/More/More *)
        by (simp add: mapN_mapN mapN_plusN)
    qed simp_all
  qed simp_all
next
  case (More p1 c1) thus ?case
  proof (induct r2 arbitrary: r3)
    case (Done y) thus ?case
    proof (induct r3)
      case (Done x3) thus ?case
        by (simp add: mapN_mapN)
    next
      case (More p3 c3) thus ?case
        by (simp add: mapN_mapN)
    qed simp_all
  next
    case (More p2 c2) thus ?case
    proof (induct r3)
      case (Done x3) thus ?case
        by (simp add: mapN_mapN mapN_plusN)
    next
      case (More p3 c3) thus ?case
        by (simp add: mapN_mapN mapN_plusN plusN_assoc)
    qed simp_all
  qed simp_all
qed simp_all

text \<open>Other miscellaneous properties about \<open>zipR\<close>:\<close>

lemma zipR_Done_left:
  shows "zipR\<cdot>f\<cdot>(Done\<cdot>x)\<cdot>r = mapR\<cdot>(f\<cdot>x)\<cdot>r"
by (induct r) (simp_all add: mapN_mapN)

lemma zipR_Done_right:
  shows "zipR\<cdot>f\<cdot>r\<cdot>(Done\<cdot>y) = mapR\<cdot>(\<Lambda> x. f\<cdot>x\<cdot>y)\<cdot>r"
by (induct r) (simp_all add: mapN_mapN)

lemma mapR_zipR: "mapR\<cdot>h\<cdot>(zipR\<cdot>f\<cdot>a\<cdot>b) = zipR\<cdot>(\<Lambda> x y. h\<cdot>(f\<cdot>x\<cdot>y))\<cdot>a\<cdot>b"
apply (induct a arbitrary: b)
apply simp
apply simp
apply (simp add: zipR_Done_left zipR_Done_right mapR_mapR)
apply (induct_tac b)
apply simp
apply simp
apply (simp add: mapN_mapN)
apply (simp add: mapN_mapN mapN_plusN)
done

lemma zipR_mapR_left: "zipR\<cdot>f\<cdot>(mapR\<cdot>h\<cdot>a)\<cdot>b = zipR\<cdot>(\<Lambda> x y. f\<cdot>(h\<cdot>x)\<cdot>y)\<cdot>a\<cdot>b"
apply (induct a arbitrary: b)
apply simp
apply simp
apply (simp add: zipR_Done_left zipR_Done_right eta_cfun)
apply (simp add: mapN_mapN)
apply (induct_tac b)
apply simp
apply simp
apply (simp add: mapN_mapN)
apply (simp add: mapN_mapN)
done

lemma zipR_mapR_right: "zipR\<cdot>f\<cdot>a\<cdot>(mapR\<cdot>h\<cdot>b) = zipR\<cdot>(\<Lambda> x y. f\<cdot>x\<cdot>(h\<cdot>y))\<cdot>a\<cdot>b"
apply (induct b arbitrary: a)
apply simp
apply simp
apply (simp add: zipR_Done_left zipR_Done_right)
apply (simp add: mapN_mapN)
apply (induct_tac a)
apply simp
apply simp
apply (simp add: mapN_mapN)
apply (simp add: mapN_mapN)
done

lemma zipR_commute:
  assumes f: "\<And>x y. f\<cdot>x\<cdot>y = g\<cdot>y\<cdot>x"
  shows "zipR\<cdot>f\<cdot>a\<cdot>b = zipR\<cdot>g\<cdot>b\<cdot>a"
apply (induct a arbitrary: b)
apply simp
apply simp
apply (simp add: zipR_Done_left zipR_Done_right f [symmetric] eta_cfun)
apply (induct_tac b)
apply simp
apply simp
apply (simp add: mapN_mapN)
apply (simp add: mapN_mapN mapN_plusN plusN_commute)
done

lemma zipR_assoc:
  fixes a :: "('s, 'a) R" and b :: "('s, 'b) R" and c :: "('s, 'c) R"
  fixes f :: "'a \<rightarrow> 'b \<rightarrow> 'd" and g :: "'d \<rightarrow> 'c \<rightarrow> 'e"
  assumes gf: "\<And>x y z. g\<cdot>(f\<cdot>x\<cdot>y)\<cdot>z = h\<cdot>x\<cdot>(k\<cdot>y\<cdot>z)"
  shows "zipR\<cdot>g\<cdot>(zipR\<cdot>f\<cdot>a\<cdot>b)\<cdot>c = zipR\<cdot>h\<cdot>a\<cdot>(zipR\<cdot>k\<cdot>b\<cdot>c)" (is "?P a b c")
 apply (induct a arbitrary: b c)
    apply simp
   apply simp
  apply (simp add: zipR_Done_left zipR_Done_right)
  apply (simp add: zipR_mapR_left mapR_zipR gf)
 apply (rename_tac pA kA b c)
 apply (rule_tac x=c in spec)
 apply (induct_tac b)
    apply simp
   apply simp
  apply (simp add: mapN_mapN)
  apply (simp add: zipR_Done_left zipR_Done_right eta_cfun)
  apply (simp add: zipR_mapR_right)
  apply (rule allI, rename_tac c)
  apply (induct_tac c)
     apply simp
    apply simp
   apply (rename_tac z)
   apply (simp add: mapN_mapN)
   apply (simp add: zipR_mapR_left gf)
  apply (rename_tac pC kC)
  apply (simp add: mapN_mapN)
  apply (simp add: zipR_mapR_left gf)
 apply (rename_tac pB kB)
 apply (rule allI, rename_tac c)
 apply (induct_tac c)
    apply simp
   apply simp
  apply (simp add: mapN_mapN mapN_plusN)
 apply (rename_tac pC kC)
 apply (simp add: mapN_mapN mapN_plusN plusN_assoc)
done

text \<open>Alternative proof using take lemma.\<close>

lemma
  fixes a :: "('s, 'a) R" and b :: "('s, 'b) R" and c :: "('s, 'c) R"
  fixes f :: "'a \<rightarrow> 'b \<rightarrow> 'd" and g :: "'d \<rightarrow> 'c \<rightarrow> 'e"
  assumes gf: "\<And>x y z. g\<cdot>(f\<cdot>x\<cdot>y)\<cdot>z = h\<cdot>x\<cdot>(k\<cdot>y\<cdot>z)"
  shows "zipR\<cdot>g\<cdot>(zipR\<cdot>f\<cdot>a\<cdot>b)\<cdot>c = zipR\<cdot>h\<cdot>a\<cdot>(zipR\<cdot>k\<cdot>b\<cdot>c)"
    (is "?lhs = ?rhs" is "?P a b c")
proof (rule R.take_lemma)
  fix n show "R_take n\<cdot>?lhs = R_take n\<cdot>?rhs"
  proof (induct n arbitrary: a b c)
    case (0 a b c)
    show ?case by simp
  next
    case (Suc n a b c)
    note IH = this
    let ?P = ?case
    show ?case
    proof (cases a)
      case bottom thus ?P by simp
    next
      case (Done x) thus ?P
        by (simp add: zipR_Done_left zipR_mapR_left mapR_zipR gf)
    next
      case (More nA) thus ?P
      proof (cases b)
        case bottom thus ?P by simp
      next
        case (Done y) thus ?P
          by (simp add: zipR_Done_left zipR_Done_right
            zipR_mapR_left zipR_mapR_right gf)
      next
        case (More nB) thus ?P
        proof (cases c)
          case bottom thus ?P by simp
        next
          case (Done z) thus ?P
            by (simp add: zipR_Done_right mapR_zipR zipR_mapR_right gf)
        next
          case (More nC)
          note H = \<open>a = More\<cdot>nA\<close> \<open>b = More\<cdot>nB\<close> \<open>c = More\<cdot>nC\<close>
          show ?P
            apply (simp only: H zipR_More_More)
            apply (simplesubst zipR_More_More [of f, symmetric])
            apply (simplesubst zipR_More_More [of k, symmetric])
            apply (simp only: H [symmetric])
            apply (simp add: mapN_mapN mapN_plusN plusN_assoc IH)
            done
        qed
      qed
    qed
  qed
qed

end
