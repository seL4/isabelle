(*  Title:      HOL/Library/Countable.thy
    Author:     Alexander Krauss, TU Muenchen
    Author:     Brian Huffman, Portland State University
    Author:     Jasmin Blanchette, TU Muenchen
*)

section \<open>Encoding (almost) everything into natural numbers\<close>

theory Countable
imports Old_Datatype HOL.Rat Nat_Bijection
begin

subsection \<open>The class of countable types\<close>

class countable =
  assumes ex_inj: "\<exists>to_nat :: 'a \<Rightarrow> nat. inj to_nat"

lemma countable_classI:
  fixes f :: "'a \<Rightarrow> nat"
  assumes "\<And>x y. f x = f y \<Longrightarrow> x = y"
  shows "OFCLASS('a, countable_class)"
proof (intro_classes, rule exI)
  show "inj f"
    by (rule injI [OF assms]) assumption
qed


subsection \<open>Conversion functions\<close>

definition to_nat :: "'a::countable \<Rightarrow> nat" where
  "to_nat = (SOME f. inj f)"

definition from_nat :: "nat \<Rightarrow> 'a::countable" where
  "from_nat = inv (to_nat :: 'a \<Rightarrow> nat)"

lemma inj_to_nat [simp]: "inj to_nat"
  by (rule exE_some [OF ex_inj]) (simp add: to_nat_def)

lemma inj_on_to_nat[simp, intro]: "inj_on to_nat S"
  using inj_to_nat by (auto simp: inj_on_def)

lemma surj_from_nat [simp]: "surj from_nat"
  unfolding from_nat_def by (simp add: inj_imp_surj_inv)

lemma to_nat_split [simp]: "to_nat x = to_nat y \<longleftrightarrow> x = y"
  using injD [OF inj_to_nat] by auto

lemma from_nat_to_nat [simp]:
  "from_nat (to_nat x) = x"
  by (simp add: from_nat_def)


subsection \<open>Finite types are countable\<close>

subclass (in finite) countable
proof
  have "finite (UNIV::'a set)" by (rule finite_UNIV)
  with finite_conv_nat_seg_image [of "UNIV::'a set"]
  obtain n and f :: "nat \<Rightarrow> 'a"
    where "UNIV = f ` {i. i < n}" by auto
  then have "surj f" unfolding surj_def by auto
  then have "inj (inv f)" by (rule surj_imp_inj_inv)
  then show "\<exists>to_nat :: 'a \<Rightarrow> nat. inj to_nat" by (rule exI[of inj])
qed


subsection \<open>Automatically proving countability of old-style datatypes\<close>

context
begin

qualified inductive finite_item :: "'a Old_Datatype.item \<Rightarrow> bool" where
  undefined: "finite_item undefined"
| In0: "finite_item x \<Longrightarrow> finite_item (Old_Datatype.In0 x)"
| In1: "finite_item x \<Longrightarrow> finite_item (Old_Datatype.In1 x)"
| Leaf: "finite_item (Old_Datatype.Leaf a)"
| Scons: "\<lbrakk>finite_item x; finite_item y\<rbrakk> \<Longrightarrow> finite_item (Old_Datatype.Scons x y)"

qualified function nth_item :: "nat \<Rightarrow> ('a::countable) Old_Datatype.item"
where
  "nth_item 0 = undefined"
| "nth_item (Suc n) =
  (case sum_decode n of
    Inl i \<Rightarrow>
    (case sum_decode i of
      Inl j \<Rightarrow> Old_Datatype.In0 (nth_item j)
    | Inr j \<Rightarrow> Old_Datatype.In1 (nth_item j))
  | Inr i \<Rightarrow>
    (case sum_decode i of
      Inl j \<Rightarrow> Old_Datatype.Leaf (from_nat j)
    | Inr j \<Rightarrow>
      (case prod_decode j of
        (a, b) \<Rightarrow> Old_Datatype.Scons (nth_item a) (nth_item b))))"
by pat_completeness auto

lemma le_sum_encode_Inl: "x \<le> y \<Longrightarrow> x \<le> sum_encode (Inl y)"
unfolding sum_encode_def by simp

lemma le_sum_encode_Inr: "x \<le> y \<Longrightarrow> x \<le> sum_encode (Inr y)"
unfolding sum_encode_def by simp

qualified termination
by (relation "measure id")
  (auto simp flip: sum_encode_eq prod_encode_eq
    simp: le_imp_less_Suc le_sum_encode_Inl le_sum_encode_Inr
    le_prod_encode_1 le_prod_encode_2)

lemma nth_item_covers: "finite_item x \<Longrightarrow> \<exists>n. nth_item n = x"
proof (induct set: finite_item)
  case undefined
  have "nth_item 0 = undefined" by simp
  thus ?case ..
next
  case (In0 x)
  then obtain n where "nth_item n = x" by fast
  hence "nth_item (Suc (sum_encode (Inl (sum_encode (Inl n))))) = Old_Datatype.In0 x" by simp
  thus ?case ..
next
  case (In1 x)
  then obtain n where "nth_item n = x" by fast
  hence "nth_item (Suc (sum_encode (Inl (sum_encode (Inr n))))) = Old_Datatype.In1 x" by simp
  thus ?case ..
next
  case (Leaf a)
  have "nth_item (Suc (sum_encode (Inr (sum_encode (Inl (to_nat a)))))) = Old_Datatype.Leaf a"
    by simp
  thus ?case ..
next
  case (Scons x y)
  then obtain i j where "nth_item i = x" and "nth_item j = y" by fast
  hence "nth_item
    (Suc (sum_encode (Inr (sum_encode (Inr (prod_encode (i, j))))))) = Old_Datatype.Scons x y"
    by simp
  thus ?case ..
qed

theorem countable_datatype:
  fixes Rep :: "'b \<Rightarrow> ('a::countable) Old_Datatype.item"
  fixes Abs :: "('a::countable) Old_Datatype.item \<Rightarrow> 'b"
  fixes rep_set :: "('a::countable) Old_Datatype.item \<Rightarrow> bool"
  assumes type: "type_definition Rep Abs (Collect rep_set)"
  assumes finite_item: "\<And>x. rep_set x \<Longrightarrow> finite_item x"
  shows "OFCLASS('b, countable_class)"
proof
  define f where "f y = (LEAST n. nth_item n = Rep y)" for y
  {
    fix y :: 'b
    have "rep_set (Rep y)"
      using type_definition.Rep [OF type] by simp
    hence "finite_item (Rep y)"
      by (rule finite_item)
    hence "\<exists>n. nth_item n = Rep y"
      by (rule nth_item_covers)
    hence "nth_item (f y) = Rep y"
      unfolding f_def by (rule LeastI_ex)
    hence "Abs (nth_item (f y)) = y"
      using type_definition.Rep_inverse [OF type] by simp
  }
  hence "inj f"
    by (rule inj_on_inverseI)
  thus "\<exists>f::'b \<Rightarrow> nat. inj f"
    by - (rule exI)
qed

ML \<open>
  fun old_countable_datatype_tac ctxt =
    SUBGOAL (fn (goal, _) =>
      let
        val ty_name =
          (case goal of
            (_ $ Const (\<^const_name>\<open>Pure.type\<close>, Type (\<^type_name>\<open>itself\<close>, [Type (n, _)]))) => n
          | _ => raise Match)
        val typedef_info = hd (Typedef.get_info ctxt ty_name)
        val typedef_thm = #type_definition (snd typedef_info)
        val pred_name =
          (case HOLogic.dest_Trueprop (Thm.concl_of typedef_thm) of
            (_ $ _ $ _ $ (_ $ Const (n, _))) => n
          | _ => raise Match)
        val induct_info = Inductive.the_inductive_global ctxt pred_name
        val pred_names = #names (fst induct_info)
        val induct_thms = #inducts (snd induct_info)
        val alist = pred_names ~~ induct_thms
        val induct_thm = the (AList.lookup (op =) alist pred_name)
        val vars = rev (Term.add_vars (Thm.prop_of induct_thm) [])
        val insts = vars |> map (fn (_, T) => try (Thm.cterm_of ctxt)
          (Const (\<^const_name>\<open>Countable.finite_item\<close>, T)))
        val induct_thm' = Thm.instantiate' [] insts induct_thm
        val rules = @{thms finite_item.intros}
      in
        SOLVED' (fn i => EVERY
          [resolve_tac ctxt @{thms countable_datatype} i,
           resolve_tac ctxt [typedef_thm] i,
           eresolve_tac ctxt [induct_thm'] i,
           REPEAT (resolve_tac ctxt rules i ORELSE assume_tac ctxt i)]) 1
      end)
\<close>

end


subsection \<open>Automatically proving countability of datatypes\<close>

ML_file \<open>../Tools/BNF/bnf_lfp_countable.ML\<close>

ML \<open>
fun countable_datatype_tac ctxt st =
  (case \<^try>\<open>HEADGOAL (old_countable_datatype_tac ctxt) st\<close> of
    SOME res => res
  | NONE => BNF_LFP_Countable.countable_datatype_tac ctxt st);

(* compatibility *)
fun countable_tac ctxt =
  SELECT_GOAL (countable_datatype_tac ctxt);
\<close>

method_setup countable_datatype = \<open>
  Scan.succeed (SIMPLE_METHOD o countable_datatype_tac)
\<close> "prove countable class instances for datatypes"


subsection \<open>More Countable types\<close>

text \<open>Naturals\<close>

instance nat :: countable
  by (rule countable_classI [of "id"]) simp

text \<open>Pairs\<close>

instance prod :: (countable, countable) countable
  by (rule countable_classI [of "\<lambda>(x, y). prod_encode (to_nat x, to_nat y)"])
    (auto simp add: prod_encode_eq)

text \<open>Sums\<close>

instance sum :: (countable, countable) countable
  by (rule countable_classI [of "(\<lambda>x. case x of Inl a \<Rightarrow> to_nat (False, to_nat a)
                                     | Inr b \<Rightarrow> to_nat (True, to_nat b))"])
    (simp split: sum.split_asm)

text \<open>Integers\<close>

instance int :: countable
  by (rule countable_classI [of int_encode]) (simp add: int_encode_eq)

text \<open>Options\<close>

instance option :: (countable) countable
  by countable_datatype

text \<open>Lists\<close>

instance list :: (countable) countable
  by countable_datatype

text \<open>String literals\<close>

instance String.literal :: countable
  by (rule countable_classI [of "to_nat \<circ> String.explode"]) (simp add: String.explode_inject)

text \<open>Functions\<close>

instance "fun" :: (finite, countable) countable
proof
  obtain xs :: "'a list" where xs: "set xs = UNIV"
    using finite_list [OF finite_UNIV] ..
  show "\<exists>to_nat::('a \<Rightarrow> 'b) \<Rightarrow> nat. inj to_nat"
  proof
    show "inj (\<lambda>f. to_nat (map f xs))"
      by (rule injI, simp add: xs fun_eq_iff)
  qed
qed

text \<open>Typereps\<close>

instance typerep :: countable
  by countable_datatype


subsection \<open>The rationals are countably infinite\<close>

definition nat_to_rat_surj :: "nat \<Rightarrow> rat" where
  "nat_to_rat_surj n = (let (a, b) = prod_decode n in Fract (int_decode a) (int_decode b))"

lemma surj_nat_to_rat_surj: "surj nat_to_rat_surj"
unfolding surj_def
proof
  fix r::rat
  show "\<exists>n. r = nat_to_rat_surj n"
  proof (cases r)
    fix i j assume [simp]: "r = Fract i j" and "j > 0"
    have "r = (let m = int_encode i; n = int_encode j in nat_to_rat_surj (prod_encode (m, n)))"
      by (simp add: Let_def nat_to_rat_surj_def)
    thus "\<exists>n. r = nat_to_rat_surj n" by(auto simp: Let_def)
  qed
qed

lemma Rats_eq_range_nat_to_rat_surj: "\<rat> = range nat_to_rat_surj"
  by (simp add: Rats_def surj_nat_to_rat_surj)

context field_char_0
begin

lemma Rats_eq_range_of_rat_o_nat_to_rat_surj:
  "\<rat> = range (of_rat \<circ> nat_to_rat_surj)"
  using surj_nat_to_rat_surj
  by (auto simp: Rats_def image_def surj_def) (blast intro: arg_cong[where f = of_rat])

lemma surj_of_rat_nat_to_rat_surj:
  "r \<in> \<rat> \<Longrightarrow> \<exists>n. r = of_rat (nat_to_rat_surj n)"
  by (simp add: Rats_eq_range_of_rat_o_nat_to_rat_surj image_def)

end

instance rat :: countable
proof
  show "\<exists>to_nat::rat \<Rightarrow> nat. inj to_nat"
  proof
    have "surj nat_to_rat_surj"
      by (rule surj_nat_to_rat_surj)
    then show "inj (inv nat_to_rat_surj)"
      by (rule surj_imp_inj_inv)
  qed
qed

theorem rat_denum: "\<exists>f :: nat \<Rightarrow> rat. surj f"
 using surj_nat_to_rat_surj by metis

end
