(* Author: Gerwin Klein, Jeremy Dawson

   Miscellaneous additional library definitions and lemmas for 
   the word type. Instantiation to boolean algebras, definition
   of recursion and induction patterns for words.
*)

header {* Miscellaneous Library for Words *}

theory WordGenLib
imports WordShift Boolean_Algebra
begin

declare of_nat_2p [simp]

lemma word_int_cases:
  "\<lbrakk>\<And>n. \<lbrakk>(x ::'a::len0 word) = word_of_int n; 0 \<le> n; n < 2^len_of TYPE('a)\<rbrakk> \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by (cases x rule: word_uint.Abs_cases) (simp add: uints_num)

lemma word_nat_cases [cases type: word]:
  "\<lbrakk>\<And>n. \<lbrakk>(x ::'a::len word) = of_nat n; n < 2^len_of TYPE('a)\<rbrakk> \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by (cases x rule: word_unat.Abs_cases) (simp add: unats_def)

lemma max_word_eq:
  "(max_word::'a::len word) = 2^len_of TYPE('a) - 1"
  by (simp add: max_word_def word_of_int_hom_syms word_of_int_2p)

lemma max_word_max [simp,intro!]:
  "n \<le> max_word"
  by (cases n rule: word_int_cases)
     (simp add: max_word_def word_le_def int_word_uint int_mod_eq')
  
lemma word_of_int_2p_len: 
  "word_of_int (2 ^ len_of TYPE('a)) = (0::'a::len0 word)"
  by (subst word_uint.Abs_norm [symmetric]) 
     (simp add: word_of_int_hom_syms)

lemma word_pow_0:
  "(2::'a::len word) ^ len_of TYPE('a) = 0"
proof -
  have "word_of_int (2 ^ len_of TYPE('a)) = (0::'a word)"
    by (rule word_of_int_2p_len)
  thus ?thesis by (simp add: word_of_int_2p)
qed

lemma max_word_wrap: "x + 1 = 0 \<Longrightarrow> x = max_word"
  apply (simp add: max_word_eq)
  apply uint_arith
  apply auto
  apply (simp add: word_pow_0)
  done

lemma max_word_minus: 
  "max_word = (-1::'a::len word)"
proof -
  have "-1 + 1 = (0::'a word)" by simp
  thus ?thesis by (rule max_word_wrap [symmetric])
qed

lemma max_word_bl [simp]:
  "to_bl (max_word::'a::len word) = replicate (len_of TYPE('a)) True"
  by (subst max_word_minus to_bl_n1)+ simp

lemma max_test_bit [simp]:
  "(max_word::'a::len word) !! n = (n < len_of TYPE('a))"
  by (auto simp add: test_bit_bl word_size)

lemma word_and_max [simp]:
  "x AND max_word = x"
  by (rule word_eqI) (simp add: word_ops_nth_size word_size)

lemma word_or_max [simp]:
  "x OR max_word = max_word"
  by (rule word_eqI) (simp add: word_ops_nth_size word_size)

lemma word_ao_dist2:
  "x AND (y OR z) = x AND y OR x AND (z::'a::len0 word)"
  by (rule word_eqI) (auto simp add: word_ops_nth_size word_size)

lemma word_oa_dist2:
  "x OR y AND z = (x OR y) AND (x OR (z::'a::len0 word))"
  by (rule word_eqI) (auto simp add: word_ops_nth_size word_size)

lemma word_and_not [simp]:
  "x AND NOT x = (0::'a::len0 word)"
  by (rule word_eqI) (auto simp add: word_ops_nth_size word_size)

lemma word_or_not [simp]:
  "x OR NOT x = max_word"
  by (rule word_eqI) (auto simp add: word_ops_nth_size word_size)

lemma word_boolean:
  "boolean (op AND) (op OR) bitNOT 0 max_word"
  apply (rule boolean.intro)
           apply (rule word_bw_assocs)
          apply (rule word_bw_assocs)
         apply (rule word_bw_comms)
        apply (rule word_bw_comms)
       apply (rule word_ao_dist2)
      apply (rule word_oa_dist2)
     apply (rule word_and_max)
    apply (rule word_log_esimps)
   apply (rule word_and_not)
  apply (rule word_or_not)
  done

interpretation word_bool_alg!:
  boolean "op AND" "op OR" bitNOT 0 max_word
  by (rule word_boolean)

lemma word_xor_and_or:
  "x XOR y = x AND NOT y OR NOT x AND (y::'a::len0 word)"
  by (rule word_eqI) (auto simp add: word_ops_nth_size word_size)

interpretation word_bool_alg!:
  boolean_xor "op AND" "op OR" bitNOT 0 max_word "op XOR"
  apply (rule boolean_xor.intro)
   apply (rule word_boolean)
  apply (rule boolean_xor_axioms.intro)
  apply (rule word_xor_and_or)
  done

lemma shiftr_0 [iff]:
  "(x::'a::len0 word) >> 0 = x"
  by (simp add: shiftr_bl)

lemma shiftl_0 [simp]: 
  "(x :: 'a :: len word) << 0 = x"
  by (simp add: shiftl_t2n)

lemma shiftl_1 [simp]:
  "(1::'a::len word) << n = 2^n"
  by (simp add: shiftl_t2n)

lemma uint_lt_0 [simp]:
  "uint x < 0 = False"
  by (simp add: linorder_not_less)

lemma shiftr1_1 [simp]: 
  "shiftr1 (1::'a::len word) = 0"
  by (simp add: shiftr1_def word_0_alt)

lemma shiftr_1[simp]: 
  "(1::'a::len word) >> n = (if n = 0 then 1 else 0)"
  by (induct n) (auto simp: shiftr_def)

lemma word_less_1 [simp]: 
  "((x::'a::len word) < 1) = (x = 0)"
  by (simp add: word_less_nat_alt unat_0_iff)

lemma to_bl_mask:
  "to_bl (mask n :: 'a::len word) = 
  replicate (len_of TYPE('a) - n) False @ 
    replicate (min (len_of TYPE('a)) n) True"
  by (simp add: mask_bl word_rep_drop min_def)

lemma map_replicate_True:
  "n = length xs ==>
    map (\<lambda>(x,y). x & y) (zip xs (replicate n True)) = xs"
  by (induct xs arbitrary: n) auto

lemma map_replicate_False:
  "n = length xs ==> map (\<lambda>(x,y). x & y)
    (zip xs (replicate n False)) = replicate n False"
  by (induct xs arbitrary: n) auto

lemma bl_and_mask:
  fixes w :: "'a::len word"
  fixes n
  defines "n' \<equiv> len_of TYPE('a) - n"
  shows "to_bl (w AND mask n) =  replicate n' False @ drop n' (to_bl w)"
proof - 
  note [simp] = map_replicate_True map_replicate_False
  have "to_bl (w AND mask n) = 
        map2 op & (to_bl w) (to_bl (mask n::'a::len word))"
    by (simp add: bl_word_and)
  also
  have "to_bl w = take n' (to_bl w) @ drop n' (to_bl w)" by simp
  also
  have "map2 op & \<dots> (to_bl (mask n::'a::len word)) = 
        replicate n' False @ drop n' (to_bl w)"
    unfolding to_bl_mask n'_def map2_def
    by (subst zip_append) auto
  finally
  show ?thesis .
qed

lemma drop_rev_takefill:
  "length xs \<le> n ==>
    drop (n - length xs) (rev (takefill False n (rev xs))) = xs"
  by (simp add: takefill_alt rev_take)

lemma map_nth_0 [simp]:
  "map (op !! (0::'a::len0 word)) xs = replicate (length xs) False"
  by (induct xs) auto

lemma uint_plus_if_size:
  "uint (x + y) = 
  (if uint x + uint y < 2^size x then 
      uint x + uint y 
   else 
      uint x + uint y - 2^size x)" 
  by (simp add: word_arith_alts int_word_uint mod_add_if_z 
                word_size)

lemma unat_plus_if_size:
  "unat (x + (y::'a::len word)) = 
  (if unat x + unat y < 2^size x then 
      unat x + unat y 
   else 
      unat x + unat y - 2^size x)" 
  apply (subst word_arith_nat_defs)
  apply (subst unat_of_nat)
  apply (simp add:  mod_nat_add word_size)
  done

lemma word_neq_0_conv [simp]:
  fixes w :: "'a :: len word"
  shows "(w \<noteq> 0) = (0 < w)"
proof -
  have "0 \<le> w" by (rule word_zero_le)
  thus ?thesis by (auto simp add: word_less_def)
qed

lemma max_lt:
  "unat (max a b div c) = unat (max a b) div unat (c:: 'a :: len word)"
  apply (subst word_arith_nat_defs)
  apply (subst word_unat.eq_norm)
  apply (subst mod_if)
  apply clarsimp
  apply (erule notE)
  apply (insert div_le_dividend [of "unat (max a b)" "unat c"])
  apply (erule order_le_less_trans)
  apply (insert unat_lt2p [of "max a b"])
  apply simp
  done

lemma uint_sub_if_size:
  "uint (x - y) = 
  (if uint y \<le> uint x then 
      uint x - uint y 
   else 
      uint x - uint y + 2^size x)"
  by (simp add: word_arith_alts int_word_uint mod_sub_if_z 
                word_size)

lemma unat_sub_simple:
  "x \<le> y ==> unat (y - x) = unat y - unat x"
  by (simp add: unat_def uint_sub_if_size word_le_def nat_diff_distrib)

lemmas unat_sub = unat_sub_simple

lemma word_less_sub1:
  fixes x :: "'a :: len word"
  shows "x \<noteq> 0 ==> 1 < x = (0 < x - 1)"
  by (simp add: unat_sub_if_size word_less_nat_alt)

lemma word_le_sub1:
  fixes x :: "'a :: len word"
  shows "x \<noteq> 0 ==> 1 \<le> x = (0 \<le> x - 1)"
  by (simp add: unat_sub_if_size order_le_less word_less_nat_alt)

lemmas word_less_sub1_numberof [simp] =
  word_less_sub1 [of "number_of w", standard]
lemmas word_le_sub1_numberof [simp] =
  word_le_sub1 [of "number_of w", standard]
  
lemma word_of_int_minus: 
  "word_of_int (2^len_of TYPE('a) - i) = (word_of_int (-i)::'a::len word)"
proof -
  have x: "2^len_of TYPE('a) - i = -i + 2^len_of TYPE('a)" by simp
  show ?thesis
    apply (subst x)
    apply (subst word_uint.Abs_norm [symmetric], subst mod_add_self2)
    apply simp
    done
qed
  
lemmas word_of_int_inj = 
  word_uint.Abs_inject [unfolded uints_num, simplified]

lemma word_le_less_eq:
  "(x ::'z::len word) \<le> y = (x = y \<or> x < y)"
  by (auto simp add: word_less_def)

lemma mod_plus_cong:
  assumes 1: "(b::int) = b'"
      and 2: "x mod b' = x' mod b'"
      and 3: "y mod b' = y' mod b'"
      and 4: "x' + y' = z'"
  shows "(x + y) mod b = z' mod b'"
proof -
  from 1 2[symmetric] 3[symmetric] have "(x + y) mod b = (x' mod b' + y' mod b') mod b'"
    by (simp add: mod_add_eq[symmetric])
  also have "\<dots> = (x' + y') mod b'"
    by (simp add: mod_add_eq[symmetric])
  finally show ?thesis by (simp add: 4)
qed

lemma mod_minus_cong:
  assumes 1: "(b::int) = b'"
      and 2: "x mod b' = x' mod b'"
      and 3: "y mod b' = y' mod b'"
      and 4: "x' - y' = z'"
  shows "(x - y) mod b = z' mod b'"
  using assms
  apply (subst zmod_zsub_left_eq)
  apply (subst zmod_zsub_right_eq)
  apply (simp add: zmod_zsub_left_eq [symmetric] zmod_zsub_right_eq [symmetric])
  done

lemma word_induct_less: 
  "\<lbrakk>P (0::'a::len word); \<And>n. \<lbrakk>n < m; P n\<rbrakk> \<Longrightarrow> P (1 + n)\<rbrakk> \<Longrightarrow> P m"
  apply (cases m)
  apply atomize
  apply (erule rev_mp)+
  apply (rule_tac x=m in spec)
  apply (induct_tac n)
   apply simp
  apply clarsimp
  apply (erule impE)
   apply clarsimp
   apply (erule_tac x=n in allE)
   apply (erule impE)
    apply (simp add: unat_arith_simps)
    apply (clarsimp simp: unat_of_nat)
   apply simp
  apply (erule_tac x="of_nat na" in allE)
  apply (erule impE)
   apply (simp add: unat_arith_simps)
   apply (clarsimp simp: unat_of_nat)
  apply simp
  done
  
lemma word_induct: 
  "\<lbrakk>P (0::'a::len word); \<And>n. P n \<Longrightarrow> P (1 + n)\<rbrakk> \<Longrightarrow> P m"
  by (erule word_induct_less, simp)

lemma word_induct2 [induct type]: 
  "\<lbrakk>P 0; \<And>n. \<lbrakk>1 + n \<noteq> 0; P n\<rbrakk> \<Longrightarrow> P (1 + n)\<rbrakk> \<Longrightarrow> P (n::'b::len word)"
  apply (rule word_induct, simp)
  apply (case_tac "1+n = 0", auto)
  done

constdefs
  word_rec :: "'a \<Rightarrow> ('b::len word \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'b word \<Rightarrow> 'a"
  "word_rec forZero forSuc n \<equiv> nat_rec forZero (forSuc \<circ> of_nat) (unat n)"

lemma word_rec_0: "word_rec z s 0 = z"
  by (simp add: word_rec_def)

lemma word_rec_Suc: 
  "1 + n \<noteq> (0::'a::len word) \<Longrightarrow> word_rec z s (1 + n) = s n (word_rec z s n)"
  apply (simp add: word_rec_def unat_word_ariths)
  apply (subst nat_mod_eq')
   apply (cut_tac x=n in unat_lt2p)
   apply (drule Suc_mono)
   apply (simp add: less_Suc_eq_le)
   apply (simp only: order_less_le, simp)
   apply (erule contrapos_pn, simp)
   apply (drule arg_cong[where f=of_nat])
   apply simp
   apply (subst (asm) word_unat.Rep_inverse[of n])
   apply simp
  apply simp
  done

lemma word_rec_Pred: 
  "n \<noteq> 0 \<Longrightarrow> word_rec z s n = s (n - 1) (word_rec z s (n - 1))"
  apply (rule subst[where t="n" and s="1 + (n - 1)"])
   apply simp
  apply (subst word_rec_Suc)
   apply simp
  apply simp
  done

lemma word_rec_in: 
  "f (word_rec z (\<lambda>_. f) n) = word_rec (f z) (\<lambda>_. f) n"
  by (induct n) (simp_all add: word_rec_0 word_rec_Suc)

lemma word_rec_in2: 
  "f n (word_rec z f n) = word_rec (f 0 z) (f \<circ> op + 1) n"
  by (induct n) (simp_all add: word_rec_0 word_rec_Suc)

lemma word_rec_twice: 
  "m \<le> n \<Longrightarrow> word_rec z f n = word_rec (word_rec z f (n - m)) (f \<circ> op + (n - m)) m"
apply (erule rev_mp)
apply (rule_tac x=z in spec)
apply (rule_tac x=f in spec)
apply (induct n)
 apply (simp add: word_rec_0)
apply clarsimp
apply (rule_tac t="1 + n - m" and s="1 + (n - m)" in subst)
 apply simp
apply (case_tac "1 + (n - m) = 0")
 apply (simp add: word_rec_0)
 apply (rule_tac f = "word_rec ?a ?b" in arg_cong)
 apply (rule_tac t="m" and s="m + (1 + (n - m))" in subst)
  apply simp
 apply (simp (no_asm_use))
apply (simp add: word_rec_Suc word_rec_in2)
apply (erule impE)
 apply uint_arith
apply (drule_tac x="x \<circ> op + 1" in spec)
apply (drule_tac x="x 0 xa" in spec)
apply simp
apply (rule_tac t="\<lambda>a. x (1 + (n - m + a))" and s="\<lambda>a. x (1 + (n - m) + a)"
       in subst)
 apply (clarsimp simp add: expand_fun_eq)
 apply (rule_tac t="(1 + (n - m + xb))" and s="1 + (n - m) + xb" in subst)
  apply simp
 apply (rule refl)
apply (rule refl)
done

lemma word_rec_id: "word_rec z (\<lambda>_. id) n = z"
  by (induct n) (auto simp add: word_rec_0 word_rec_Suc)

lemma word_rec_id_eq: "\<forall>m < n. f m = id \<Longrightarrow> word_rec z f n = z"
apply (erule rev_mp)
apply (induct n)
 apply (auto simp add: word_rec_0 word_rec_Suc)
 apply (drule spec, erule mp)
 apply uint_arith
apply (drule_tac x=n in spec, erule impE)
 apply uint_arith
apply simp
done

lemma word_rec_max: 
  "\<forall>m\<ge>n. m \<noteq> -1 \<longrightarrow> f m = id \<Longrightarrow> word_rec z f -1 = word_rec z f n"
apply (subst word_rec_twice[where n="-1" and m="-1 - n"])
 apply simp
apply simp
apply (rule word_rec_id_eq)
apply clarsimp
apply (drule spec, rule mp, erule mp)
 apply (rule word_plus_mono_right2[OF _ order_less_imp_le])
  prefer 2 
  apply assumption
 apply simp
apply (erule contrapos_pn)
apply simp
apply (drule arg_cong[where f="\<lambda>x. x - n"])
apply simp
done

lemma unatSuc: 
  "1 + n \<noteq> (0::'a::len word) \<Longrightarrow> unat (1 + n) = Suc (unat n)"
  by unat_arith


lemmas word_no_1 [simp] = word_1_no [symmetric, unfolded BIT_simps]
lemmas word_no_0 [simp] = word_0_no [symmetric]

declare word_0_bl [simp]
declare bin_to_bl_def [simp]
declare to_bl_0 [simp]
declare of_bl_True [simp]

end
