(*  Title:      HOL/HOLCF/Library/Char_Discrete.thy
    Author:     Brian Huffman
*)

section {* Discrete cpo instance for 8-bit char type *}

theory Char_Discrete
imports HOLCF
begin

subsection {* Discrete cpo instance for @{typ nibble}. *}

instantiation nibble :: discrete_cpo
begin

definition below_nibble_def:
  "(x::nibble) \<sqsubseteq> y \<longleftrightarrow> x = y"

instance proof
qed (rule below_nibble_def)

end

text {*
  TODO: implement a command to automate discrete predomain instances.
*}

instantiation nibble :: predomain
begin

definition
  "(liftemb :: nibble u \<rightarrow> udom u) \<equiv> liftemb oo u_map\<cdot>(\<Lambda> x. Discr x)"

definition
  "(liftprj :: udom u \<rightarrow> nibble u) \<equiv> u_map\<cdot>(\<Lambda> y. undiscr y) oo liftprj"

definition
  "liftdefl \<equiv> (\<lambda>(t::nibble itself). LIFTDEFL(nibble discr))"

instance proof
  show "ep_pair liftemb (liftprj :: udom u \<rightarrow> nibble u)"
    unfolding liftemb_nibble_def liftprj_nibble_def
    apply (rule ep_pair_comp)
    apply (rule ep_pair_u_map)
    apply (simp add: ep_pair.intro)
    apply (rule predomain_ep)
    done
  show "cast\<cdot>LIFTDEFL(nibble) = liftemb oo (liftprj :: udom u \<rightarrow> nibble u)"
    unfolding liftemb_nibble_def liftprj_nibble_def liftdefl_nibble_def
    apply (simp add: cast_liftdefl cfcomp1 u_map_map)
    apply (simp add: ID_def [symmetric] u_map_ID)
    done
qed

end

subsection {* Discrete cpo instance for @{typ char}. *}

instantiation char :: discrete_cpo
begin

definition below_char_def:
  "(x::char) \<sqsubseteq> y \<longleftrightarrow> x = y"

instance proof
qed (rule below_char_def)

end

text {*
  TODO: implement a command to automate discrete predomain instances.
*}

instantiation char :: predomain
begin

definition
  "(liftemb :: char u \<rightarrow> udom u) \<equiv> liftemb oo u_map\<cdot>(\<Lambda> x. Discr x)"

definition
  "(liftprj :: udom u \<rightarrow> char u) \<equiv> u_map\<cdot>(\<Lambda> y. undiscr y) oo liftprj"

definition
  "liftdefl \<equiv> (\<lambda>(t::char itself). LIFTDEFL(char discr))"

instance proof
  show "ep_pair liftemb (liftprj :: udom u \<rightarrow> char u)"
    unfolding liftemb_char_def liftprj_char_def
    apply (rule ep_pair_comp)
    apply (rule ep_pair_u_map)
    apply (simp add: ep_pair.intro)
    apply (rule predomain_ep)
    done
  show "cast\<cdot>LIFTDEFL(char) = liftemb oo (liftprj :: udom u \<rightarrow> char u)"
    unfolding liftemb_char_def liftprj_char_def liftdefl_char_def
    apply (simp add: cast_liftdefl cfcomp1 u_map_map)
    apply (simp add: ID_def [symmetric] u_map_ID)
    done
qed

end

subsection {* Using chars with Fixrec *}

definition match_Char :: "char \<rightarrow> (nibble \<rightarrow> nibble \<rightarrow> 'a match) \<rightarrow> 'a match"
  where "match_Char = (\<Lambda> c k. case c of Char a b \<Rightarrow> k\<cdot>a\<cdot>b)"

lemma match_Char_simps [simp]:
  "match_Char\<cdot>(Char a b)\<cdot>k = k\<cdot>a\<cdot>b"
by (simp add: match_Char_def)

definition match_Nibble0 :: "nibble \<rightarrow> 'a match \<rightarrow> 'a match"
  where "match_Nibble0 = (\<Lambda> c k. if c = Nibble0 then k else Fixrec.fail)"

definition match_Nibble1 :: "nibble \<rightarrow> 'a match \<rightarrow> 'a match"
  where "match_Nibble1 = (\<Lambda> c k. if c = Nibble1 then k else Fixrec.fail)"

definition match_Nibble2 :: "nibble \<rightarrow> 'a match \<rightarrow> 'a match"
  where "match_Nibble2 = (\<Lambda> c k. if c = Nibble2 then k else Fixrec.fail)"

definition match_Nibble3 :: "nibble \<rightarrow> 'a match \<rightarrow> 'a match"
  where "match_Nibble3 = (\<Lambda> c k. if c = Nibble3 then k else Fixrec.fail)"

definition match_Nibble4 :: "nibble \<rightarrow> 'a match \<rightarrow> 'a match"
  where "match_Nibble4 = (\<Lambda> c k. if c = Nibble4 then k else Fixrec.fail)"

definition match_Nibble5 :: "nibble \<rightarrow> 'a match \<rightarrow> 'a match"
  where "match_Nibble5 = (\<Lambda> c k. if c = Nibble5 then k else Fixrec.fail)"

definition match_Nibble6 :: "nibble \<rightarrow> 'a match \<rightarrow> 'a match"
  where "match_Nibble6 = (\<Lambda> c k. if c = Nibble6 then k else Fixrec.fail)"

definition match_Nibble7 :: "nibble \<rightarrow> 'a match \<rightarrow> 'a match"
  where "match_Nibble7 = (\<Lambda> c k. if c = Nibble7 then k else Fixrec.fail)"

definition match_Nibble8 :: "nibble \<rightarrow> 'a match \<rightarrow> 'a match"
  where "match_Nibble8 = (\<Lambda> c k. if c = Nibble8 then k else Fixrec.fail)"

definition match_Nibble9 :: "nibble \<rightarrow> 'a match \<rightarrow> 'a match"
  where "match_Nibble9 = (\<Lambda> c k. if c = Nibble9 then k else Fixrec.fail)"

definition match_NibbleA :: "nibble \<rightarrow> 'a match \<rightarrow> 'a match"
  where "match_NibbleA = (\<Lambda> c k. if c = NibbleA then k else Fixrec.fail)"

definition match_NibbleB :: "nibble \<rightarrow> 'a match \<rightarrow> 'a match"
  where "match_NibbleB = (\<Lambda> c k. if c = NibbleB then k else Fixrec.fail)"

definition match_NibbleC :: "nibble \<rightarrow> 'a match \<rightarrow> 'a match"
  where "match_NibbleC = (\<Lambda> c k. if c = NibbleC then k else Fixrec.fail)"

definition match_NibbleD :: "nibble \<rightarrow> 'a match \<rightarrow> 'a match"
  where "match_NibbleD = (\<Lambda> c k. if c = NibbleD then k else Fixrec.fail)"

definition match_NibbleE :: "nibble \<rightarrow> 'a match \<rightarrow> 'a match"
  where "match_NibbleE = (\<Lambda> c k. if c = NibbleE then k else Fixrec.fail)"

definition match_NibbleF :: "nibble \<rightarrow> 'a match \<rightarrow> 'a match"
  where "match_NibbleF = (\<Lambda> c k. if c = NibbleF then k else Fixrec.fail)"

lemma match_Nibble0_simps [simp]:
  "match_Nibble0\<cdot>c\<cdot>k = (if c = Nibble0 then k else Fixrec.fail)"
by (simp add: match_Nibble0_def)

lemma match_Nibble1_simps [simp]:
  "match_Nibble1\<cdot>c\<cdot>k = (if c = Nibble1 then k else Fixrec.fail)"
by (simp add: match_Nibble1_def)

lemma match_Nibble2_simps [simp]:
  "match_Nibble2\<cdot>c\<cdot>k = (if c = Nibble2 then k else Fixrec.fail)"
by (simp add: match_Nibble2_def)

lemma match_Nibble3_simps [simp]:
  "match_Nibble3\<cdot>c\<cdot>k = (if c = Nibble3 then k else Fixrec.fail)"
by (simp add: match_Nibble3_def)

lemma match_Nibble4_simps [simp]:
  "match_Nibble4\<cdot>c\<cdot>k = (if c = Nibble4 then k else Fixrec.fail)"
by (simp add: match_Nibble4_def)

lemma match_Nibble5_simps [simp]:
  "match_Nibble5\<cdot>c\<cdot>k = (if c = Nibble5 then k else Fixrec.fail)"
by (simp add: match_Nibble5_def)

lemma match_Nibble6_simps [simp]:
  "match_Nibble6\<cdot>c\<cdot>k = (if c = Nibble6 then k else Fixrec.fail)"
by (simp add: match_Nibble6_def)

lemma match_Nibble7_simps [simp]:
  "match_Nibble7\<cdot>c\<cdot>k = (if c = Nibble7 then k else Fixrec.fail)"
by (simp add: match_Nibble7_def)

lemma match_Nibble8_simps [simp]:
  "match_Nibble8\<cdot>c\<cdot>k = (if c = Nibble8 then k else Fixrec.fail)"
by (simp add: match_Nibble8_def)

lemma match_Nibble9_simps [simp]:
  "match_Nibble9\<cdot>c\<cdot>k = (if c = Nibble9 then k else Fixrec.fail)"
by (simp add: match_Nibble9_def)

lemma match_NibbleA_simps [simp]:
  "match_NibbleA\<cdot>c\<cdot>k = (if c = NibbleA then k else Fixrec.fail)"
by (simp add: match_NibbleA_def)

lemma match_NibbleB_simps [simp]:
  "match_NibbleB\<cdot>c\<cdot>k = (if c = NibbleB then k else Fixrec.fail)"
by (simp add: match_NibbleB_def)

lemma match_NibbleC_simps [simp]:
  "match_NibbleC\<cdot>c\<cdot>k = (if c = NibbleC then k else Fixrec.fail)"
by (simp add: match_NibbleC_def)

lemma match_NibbleD_simps [simp]:
  "match_NibbleD\<cdot>c\<cdot>k = (if c = NibbleD then k else Fixrec.fail)"
by (simp add: match_NibbleD_def)

lemma match_NibbleE_simps [simp]:
  "match_NibbleE\<cdot>c\<cdot>k = (if c = NibbleE then k else Fixrec.fail)"
by (simp add: match_NibbleE_def)

lemma match_NibbleF_simps [simp]:
  "match_NibbleF\<cdot>c\<cdot>k = (if c = NibbleF then k else Fixrec.fail)"
by (simp add: match_NibbleF_def)

setup {*
  Fixrec.add_matchers
    [ (@{const_name Char}, @{const_name match_Char}),
      (@{const_name Nibble0}, @{const_name match_Nibble0}),
      (@{const_name Nibble1}, @{const_name match_Nibble1}),
      (@{const_name Nibble2}, @{const_name match_Nibble2}),
      (@{const_name Nibble3}, @{const_name match_Nibble3}),
      (@{const_name Nibble4}, @{const_name match_Nibble4}),
      (@{const_name Nibble5}, @{const_name match_Nibble5}),
      (@{const_name Nibble6}, @{const_name match_Nibble6}),
      (@{const_name Nibble7}, @{const_name match_Nibble7}),
      (@{const_name Nibble8}, @{const_name match_Nibble8}),
      (@{const_name Nibble9}, @{const_name match_Nibble9}),
      (@{const_name NibbleA}, @{const_name match_NibbleA}),
      (@{const_name NibbleB}, @{const_name match_NibbleB}),
      (@{const_name NibbleC}, @{const_name match_NibbleC}),
      (@{const_name NibbleD}, @{const_name match_NibbleD}),
      (@{const_name NibbleE}, @{const_name match_NibbleE}),
      (@{const_name NibbleF}, @{const_name match_NibbleF}) ]
*}

end
