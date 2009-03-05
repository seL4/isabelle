(* Title:      HOL/Library/Finite_Cartesian_Product
   Author:     Amine Chaieb, University of Cambridge
*)

header {* Definition of finite Cartesian product types. *}

theory Finite_Cartesian_Product
  (* imports Plain SetInterval ATP_Linkup *)
imports Main
begin

  (* FIXME : ATP_Linkup is only needed for metis at a few places. We could dispense of that by changing the proofs*)
subsection{* Dimention of sets *}

definition "dimindex (S:: 'a set) = (if finite (UNIV::'a set) then card (UNIV:: 'a set) else 1)"

syntax "_type_dimindex" :: "type => nat" ("(1DIM/(1'(_')))")
translations "DIM(t)" => "CONST dimindex (CONST UNIV :: t set)"

lemma dimindex_nonzero: "dimindex S \<noteq>  0"
unfolding dimindex_def 
by (simp add: neq0_conv[symmetric] del: neq0_conv)

lemma dimindex_ge_1: "dimindex S \<ge> 1"
  using dimindex_nonzero[of S] by arith 
lemma dimindex_univ: "dimindex (S :: 'a set) = DIM('a)" by (simp add: dimindex_def)

definition hassize (infixr "hassize" 12) where
  "(S hassize n) = (finite S \<and> card S = n)"

lemma dimindex_unique: " (UNIV :: 'a set) hassize n ==> DIM('a) = n"
by (simp add: dimindex_def hassize_def)


subsection{* An indexing type parametrized by base type. *}

typedef 'a finite_image = "{1 .. DIM('a)}"
  using dimindex_ge_1 by auto

lemma finite_image_image: "(UNIV :: 'a finite_image set) = Abs_finite_image ` {1 .. DIM('a)}"
apply (auto simp add: Abs_finite_image_inverse image_def finite_image_def)
apply (rule_tac x="Rep_finite_image x" in bexI)
apply (simp_all add: Rep_finite_image_inverse Rep_finite_image)
using Rep_finite_image[where ?'a = 'a]
unfolding finite_image_def
apply simp
done

text{* Dimension of such a type, and indexing over it. *}

lemma inj_on_Abs_finite_image: 
  "inj_on (Abs_finite_image:: _ \<Rightarrow> 'a finite_image) {1 .. DIM('a)}"
by (auto simp add: inj_on_def finite_image_def Abs_finite_image_inject[where ?'a='a])

lemma has_size_finite_image: "(UNIV:: 'a finite_image set) hassize dimindex (S :: 'a set)"
  unfolding hassize_def finite_image_image card_image[OF inj_on_Abs_finite_image[where ?'a='a]] by (auto simp add: dimindex_def)

lemma hassize_image_inj: assumes f: "inj_on f S" and S: "S hassize n"
  shows "f ` S hassize n"
  using f S card_image[OF f]
    by (simp add: hassize_def inj_on_def)

lemma card_finite_image: "card (UNIV:: 'a finite_image set) = dimindex(S:: 'a set)"
using has_size_finite_image
unfolding hassize_def by blast

lemma finite_finite_image: "finite (UNIV:: 'a finite_image set)"
using has_size_finite_image
unfolding hassize_def by blast

lemma dimindex_finite_image: "dimindex (S:: 'a finite_image set) = dimindex(T:: 'a set)"
unfolding card_finite_image[of T, symmetric]
by (auto simp add: dimindex_def finite_finite_image)

lemma Abs_finite_image_works: 
  fixes i:: "'a finite_image"
  shows " \<exists>!n \<in> {1 .. DIM('a)}. Abs_finite_image n = i"
  unfolding Bex1_def Ex1_def
  apply (rule_tac x="Rep_finite_image i" in exI)
  using Rep_finite_image_inverse[where ?'a = 'a] 
    Rep_finite_image[where ?'a = 'a] 
  Abs_finite_image_inverse[where ?'a='a, symmetric]
  by (auto simp add: finite_image_def)

lemma Abs_finite_image_inj: 
 "i \<in> {1 .. DIM('a)} \<Longrightarrow> j \<in> {1 .. DIM('a)}
  \<Longrightarrow> (((Abs_finite_image i ::'a finite_image) = Abs_finite_image j) \<longleftrightarrow> (i = j))"
  using Abs_finite_image_works[where ?'a = 'a] 
  by (auto simp add: atLeastAtMost_iff Bex1_def)

lemma forall_Abs_finite_image: 
  "(\<forall>k:: 'a finite_image. P k) \<longleftrightarrow> (\<forall>i \<in> {1 .. DIM('a)}. P(Abs_finite_image i))"
unfolding Ball_def atLeastAtMost_iff Ex1_def
using Abs_finite_image_works[where ?'a = 'a, unfolded atLeastAtMost_iff Bex1_def]
by metis

subsection {* Finite Cartesian products, with indexing and lambdas. *}

typedef (Cart)
  ('a, 'b) "^" (infixl "^" 15)
    = "{f:: 'b finite_image \<Rightarrow> 'a . True}" by simp

abbreviation dimset:: "('a ^ 'n) \<Rightarrow> nat set" where
  "dimset a \<equiv> {1 .. DIM('n)}"

definition Cart_nth :: "'a ^ 'b \<Rightarrow> nat \<Rightarrow> 'a" (infixl "$" 90) where
  "x$i = Rep_Cart x (Abs_finite_image i)"

lemma stupid_ext: "(\<forall>x. f x = g x) \<longleftrightarrow> (f = g)"
  apply auto
  apply (rule ext)
  apply auto
  done
lemma Cart_eq: "((x:: 'a ^ 'b) = y) \<longleftrightarrow> (\<forall>i\<in> dimset x. x$i = y$i)"
  unfolding Cart_nth_def forall_Abs_finite_image[symmetric, where P = "\<lambda>i. Rep_Cart x i = Rep_Cart y i"] stupid_ext
  using Rep_Cart_inject[of x y] ..

consts Cart_lambda :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a ^ 'b" 
notation (xsymbols) Cart_lambda (binder "\<chi>" 10)

defs Cart_lambda_def: "Cart_lambda g == (SOME (f:: 'a ^ 'b). \<forall>i \<in> {1 .. DIM('b)}. f$i = g i)"

lemma  Cart_lambda_beta: " \<forall> i\<in> {1 .. DIM('b)}. (Cart_lambda g:: 'a ^ 'b)$i = g i"
  unfolding Cart_lambda_def
proof (rule someI_ex)
  let ?p = "\<lambda>(i::nat) (k::'b finite_image). i \<in> {1 .. DIM('b)} \<and> (Abs_finite_image i = k)"
  let ?f = "Abs_Cart (\<lambda>k. g (THE i. ?p i k)):: 'a ^ 'b"
  let ?P = "\<lambda>f i. f$i = g i"
  let ?Q = "\<lambda>(f::'a ^ 'b). \<forall> i \<in> {1 .. DIM('b)}. ?P f i"
  {fix i 
    assume i: "i \<in> {1 .. DIM('b)}"
    let ?j = "THE j. ?p j (Abs_finite_image i)"
    from theI'[where P = "\<lambda>j. ?p (j::nat) (Abs_finite_image i :: 'b finite_image)", OF Abs_finite_image_works[of "Abs_finite_image i :: 'b finite_image", unfolded Bex1_def]]
    have j: "?j \<in> {1 .. DIM('b)}" "(Abs_finite_image ?j :: 'b finite_image) = Abs_finite_image i" by blast+
    from i j Abs_finite_image_inject[of i ?j, where ?'a = 'b]
    have th: "?j = i" by (simp add: finite_image_def)  
    have "?P ?f i"
      using th
      by (simp add: Cart_nth_def Abs_Cart_inverse Rep_Cart_inverse Cart_def) }
  hence th0: "?Q ?f" ..
  with th0 show "\<exists>f. ?Q f" unfolding Ex1_def by auto
qed

lemma  Cart_lambda_beta': "i\<in> {1 .. DIM('b)} \<Longrightarrow> (Cart_lambda g:: 'a ^ 'b)$i = g i"
  using Cart_lambda_beta by blast

lemma Cart_lambda_unique:
  fixes f :: "'a ^ 'b"
  shows "(\<forall>i\<in> {1 .. DIM('b)}. f$i = g i) \<longleftrightarrow> Cart_lambda g = f"
  by (auto simp add: Cart_eq Cart_lambda_beta)

lemma Cart_lambda_eta: "(\<chi> i. (g$i)) = g" by (simp add: Cart_eq Cart_lambda_beta)

text{* A non-standard sum to "paste" Cartesian products. *}

typedef ('a,'b) finite_sum = "{1 .. DIM('a) + DIM('b)}"
  apply (rule exI[where x="1"])
  using dimindex_ge_1[of "UNIV :: 'a set"] dimindex_ge_1[of "UNIV :: 'b set"]
  by auto

definition pastecart :: "'a ^ 'm \<Rightarrow> 'a ^ 'n \<Rightarrow> 'a ^ ('m,'n) finite_sum" where
  "pastecart f g = (\<chi> i. (if i <= DIM('m) then f$i else g$(i - DIM('m))))"

definition fstcart:: "'a ^('m, 'n) finite_sum \<Rightarrow> 'a ^ 'm" where
  "fstcart f = (\<chi> i. (f$i))"

definition sndcart:: "'a ^('m, 'n) finite_sum \<Rightarrow> 'a ^ 'n" where
  "sndcart f = (\<chi> i. (f$(i + DIM('m))))"

lemma finite_sum_image: "(UNIV::('a,'b) finite_sum set) = Abs_finite_sum ` {1 .. DIM('a) + DIM('b)}"
apply (auto  simp add: image_def)
apply (rule_tac x="Rep_finite_sum x" in bexI)
apply (simp add: Rep_finite_sum_inverse)
using Rep_finite_sum[unfolded finite_sum_def, where ?'a = 'a and ?'b = 'b]
apply (simp add: Rep_finite_sum)
done

lemma inj_on_Abs_finite_sum: "inj_on (Abs_finite_sum :: _ \<Rightarrow> ('a,'b) finite_sum) {1 .. DIM('a) + DIM('b)}" 
  using Abs_finite_sum_inject[where ?'a = 'a and ?'b = 'b]
  by (auto simp add: inj_on_def finite_sum_def)

lemma dimindex_has_size_finite_sum:
  "(UNIV::('m,'n) finite_sum set) hassize (DIM('m) + DIM('n))"
  by (simp add: finite_sum_image hassize_def card_image[OF inj_on_Abs_finite_sum[where ?'a = 'm and ?'b = 'n]] del: One_nat_def)

lemma dimindex_finite_sum: "DIM(('m,'n) finite_sum) = DIM('m) + DIM('n)"
  using dimindex_has_size_finite_sum[where ?'n = 'n and ?'m = 'm, unfolded hassize_def]
  by (simp add: dimindex_def)

lemma fstcart_pastecart: "fstcart (pastecart (x::'a ^'m ) (y:: 'a ^ 'n)) = x"
  by (simp add: pastecart_def fstcart_def Cart_eq Cart_lambda_beta dimindex_finite_sum)

lemma sndcart_pastecart: "sndcart (pastecart (x::'a ^'m ) (y:: 'a ^ 'n)) = y"
  by (simp add: pastecart_def sndcart_def Cart_eq Cart_lambda_beta dimindex_finite_sum)

lemma pastecart_fst_snd: "pastecart (fstcart z) (sndcart z) = z"
proof -
 {fix i
  assume H: "i \<le> DIM('b) + DIM('c)" 
    "\<not> i \<le> DIM('b)"
    from H have ith: "i - DIM('b) \<in> {1 .. DIM('c)}"
      apply simp by arith
    from H have th0: "i - DIM('b) + DIM('b) = i"
      by simp
  have "(\<chi> i. (z$(i + DIM('b))) :: 'a ^ 'c)$(i - DIM('b)) = z$i"
    unfolding Cart_lambda_beta'[where g = "\<lambda> i. z$(i + DIM('b))", OF ith] th0 ..}
thus ?thesis by (auto simp add: pastecart_def fstcart_def sndcart_def Cart_eq Cart_lambda_beta dimindex_finite_sum)
qed

lemma pastecart_eq: "(x = y) \<longleftrightarrow> (fstcart x = fstcart y) \<and> (sndcart x = sndcart y)"
  using pastecart_fst_snd[of x] pastecart_fst_snd[of y] by metis

lemma forall_pastecart: "(\<forall>p. P p) \<longleftrightarrow> (\<forall>x y. P (pastecart x y))"
  by (metis pastecart_fst_snd fstcart_pastecart sndcart_pastecart)

lemma exists_pastecart: "(\<exists>p. P p)  \<longleftrightarrow> (\<exists>x y. P (pastecart x y))"
  by (metis pastecart_fst_snd fstcart_pastecart sndcart_pastecart)

text{* The finiteness lemma. *}

lemma finite_cart:
 "\<forall>i \<in> {1 .. DIM('n)}. finite {x.  P i x}
  \<Longrightarrow> finite {v::'a ^ 'n . (\<forall>i \<in> {1 .. DIM('n)}. P i (v$i))}"
proof-
  assume f: "\<forall>i \<in> {1 .. DIM('n)}. finite {x.  P i x}"
  {fix n
    assume n: "n \<le> DIM('n)"
    have "finite {v:: 'a ^ 'n . (\<forall>i\<in> {1 .. DIM('n)}. i \<le> n \<longrightarrow> P i (v$i))
                              \<and> (\<forall>i\<in> {1 .. DIM('n)}. n < i \<longrightarrow> v$i = (SOME x. False))}" 
      using n 
      proof(induct n)
	case 0
	have th0: "{v . (\<forall>i \<in> {1 .. DIM('n)}. v$i = (SOME x. False))} =
      {(\<chi> i. (SOME x. False)::'a ^ 'n)}" by (auto simp add: Cart_lambda_beta Cart_eq)
	with "0.prems" show ?case by auto
      next
	case (Suc n)
	let ?h = "\<lambda>(x::'a,v:: 'a ^ 'n). (\<chi> i. if i = Suc n then x else v$i):: 'a ^ 'n"
	let ?T = "{v\<Colon>'a ^ 'n.
            (\<forall>i\<Colon>nat\<in>{1\<Colon>nat..DIM('n)}. i \<le> Suc n \<longrightarrow> P i (v$i)) \<and>
            (\<forall>i\<Colon>nat\<in>{1\<Colon>nat..DIM('n)}.
                Suc n < i \<longrightarrow> v$i = (SOME x\<Colon>'a. False))}"
	let ?S = "{x::'a . P (Suc  n) x} \<times> {v:: 'a^'n. (\<forall>i \<in> {1 .. DIM('n)}. i <= n \<longrightarrow> P i (v$i)) \<and> (\<forall>i \<in> {1 .. DIM('n)}. n < i \<longrightarrow> v$i = (SOME x. False))}"
	have th0: " ?T \<subseteq> (?h ` ?S)" 
	  using Suc.prems
	  apply (auto simp add: image_def)
	  apply (rule_tac x = "x$(Suc n)" in exI)
	  apply (rule conjI)
	  apply (rotate_tac)
	  apply (erule ballE[where x="Suc n"])
	  apply simp
	  apply simp
	  apply (rule_tac x= "\<chi> i. if i = Suc n then (SOME x:: 'a. False) else (x:: 'a ^ 'n)$i:: 'a ^ 'n" in exI)
	  by (simp add: Cart_eq Cart_lambda_beta)
	have th1: "finite ?S" 
	  apply (rule finite_cartesian_product) 
	  using f Suc.hyps Suc.prems by auto 
	from finite_imageI[OF th1] have th2: "finite (?h ` ?S)" . 
	from finite_subset[OF th0 th2] show ?case by blast 
      qed}

  note th = this
  from this[of "DIM('n)"] f
  show ?thesis by auto
qed


end
