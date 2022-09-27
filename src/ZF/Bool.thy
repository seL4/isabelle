(*  Title:      ZF/Bool.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge
*)

section\<open>Booleans in Zermelo-Fraenkel Set Theory\<close>

theory Bool imports pair begin

abbreviation
  one  (\<open>1\<close>) where
  "1 \<equiv> succ(0)"

abbreviation
  two  (\<open>2\<close>) where
  "2 \<equiv> succ(1)"

text\<open>2 is equal to bool, but is used as a number rather than a type.\<close>

definition "bool \<equiv> {0,1}"

definition "cond(b,c,d) \<equiv> if(b=1,c,d)"

definition "not(b) \<equiv> cond(b,0,1)"

definition
  "and"       :: "[i,i]=>i"      (infixl \<open>and\<close> 70)  where
    "a and b \<equiv> cond(a,b,0)"

definition
  or          :: "[i,i]=>i"      (infixl \<open>or\<close> 65)  where
    "a or b \<equiv> cond(a,1,b)"

definition
  xor         :: "[i,i]=>i"      (infixl \<open>xor\<close> 65) where
    "a xor b \<equiv> cond(a,not(b),b)"


lemmas bool_defs = bool_def cond_def

lemma singleton_0: "{0} = 1"
by (simp add: succ_def)

(* Introduction rules *)

lemma bool_1I [simp,TC]: "1 \<in> bool"
by (simp add: bool_defs )

lemma bool_0I [simp,TC]: "0 \<in> bool"
by (simp add: bool_defs)

lemma one_not_0: "1\<noteq>0"
by (simp add: bool_defs )

(** 1=0 \<Longrightarrow> R **)
lemmas one_neq_0 = one_not_0 [THEN notE]

lemma boolE:
    "\<lbrakk>c: bool;  c=1 \<Longrightarrow> P;  c=0 \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
by (simp add: bool_defs, blast)

(** cond **)

(*1 means true*)
lemma cond_1 [simp]: "cond(1,c,d) = c"
by (simp add: bool_defs )

(*0 means false*)
lemma cond_0 [simp]: "cond(0,c,d) = d"
by (simp add: bool_defs )

lemma cond_type [TC]: "\<lbrakk>b: bool;  c: A(1);  d: A(0)\<rbrakk> \<Longrightarrow> cond(b,c,d): A(b)"
by (simp add: bool_defs, blast)

(*For Simp_tac and Blast_tac*)
lemma cond_simple_type: "\<lbrakk>b: bool;  c: A;  d: A\<rbrakk> \<Longrightarrow> cond(b,c,d): A"
by (simp add: bool_defs )

lemma def_cond_1: "\<lbrakk>\<And>b. j(b)\<equiv>cond(b,c,d)\<rbrakk> \<Longrightarrow> j(1) = c"
by simp

lemma def_cond_0: "\<lbrakk>\<And>b. j(b)\<equiv>cond(b,c,d)\<rbrakk> \<Longrightarrow> j(0) = d"
by simp

lemmas not_1 = not_def [THEN def_cond_1, simp]
lemmas not_0 = not_def [THEN def_cond_0, simp]

lemmas and_1 = and_def [THEN def_cond_1, simp]
lemmas and_0 = and_def [THEN def_cond_0, simp]

lemmas or_1 = or_def [THEN def_cond_1, simp]
lemmas or_0 = or_def [THEN def_cond_0, simp]

lemmas xor_1 = xor_def [THEN def_cond_1, simp]
lemmas xor_0 = xor_def [THEN def_cond_0, simp]

lemma not_type [TC]: "a:bool \<Longrightarrow> not(a) \<in> bool"
by (simp add: not_def)

lemma and_type [TC]: "\<lbrakk>a:bool;  b:bool\<rbrakk> \<Longrightarrow> a and b \<in> bool"
by (simp add: and_def)

lemma or_type [TC]: "\<lbrakk>a:bool;  b:bool\<rbrakk> \<Longrightarrow> a or b \<in> bool"
by (simp add: or_def)

lemma xor_type [TC]: "\<lbrakk>a:bool;  b:bool\<rbrakk> \<Longrightarrow> a xor b \<in> bool"
by (simp add: xor_def)

lemmas bool_typechecks = bool_1I bool_0I cond_type not_type and_type
                         or_type xor_type

subsection\<open>Laws About 'not'\<close>

lemma not_not [simp]: "a:bool \<Longrightarrow> not(not(a)) = a"
by (elim boolE, auto)

lemma not_and [simp]: "a:bool \<Longrightarrow> not(a and b) = not(a) or not(b)"
by (elim boolE, auto)

lemma not_or [simp]: "a:bool \<Longrightarrow> not(a or b) = not(a) and not(b)"
by (elim boolE, auto)

subsection\<open>Laws About 'and'\<close>

lemma and_absorb [simp]: "a: bool \<Longrightarrow> a and a = a"
by (elim boolE, auto)

lemma and_commute: "\<lbrakk>a: bool; b:bool\<rbrakk> \<Longrightarrow> a and b = b and a"
by (elim boolE, auto)

lemma and_assoc: "a: bool \<Longrightarrow> (a and b) and c  =  a and (b and c)"
by (elim boolE, auto)

lemma and_or_distrib: "\<lbrakk>a: bool; b:bool; c:bool\<rbrakk> \<Longrightarrow>
       (a or b) and c  =  (a and c) or (b and c)"
by (elim boolE, auto)

subsection\<open>Laws About 'or'\<close>

lemma or_absorb [simp]: "a: bool \<Longrightarrow> a or a = a"
by (elim boolE, auto)

lemma or_commute: "\<lbrakk>a: bool; b:bool\<rbrakk> \<Longrightarrow> a or b = b or a"
by (elim boolE, auto)

lemma or_assoc: "a: bool \<Longrightarrow> (a or b) or c  =  a or (b or c)"
by (elim boolE, auto)

lemma or_and_distrib: "\<lbrakk>a: bool; b: bool; c: bool\<rbrakk> \<Longrightarrow>
           (a and b) or c  =  (a or c) and (b or c)"
by (elim boolE, auto)


definition
  bool_of_o :: "o=>i" where
   "bool_of_o(P) \<equiv> (if P then 1 else 0)"

lemma [simp]: "bool_of_o(True) = 1"
by (simp add: bool_of_o_def)

lemma [simp]: "bool_of_o(False) = 0"
by (simp add: bool_of_o_def)

lemma [simp,TC]: "bool_of_o(P) \<in> bool"
by (simp add: bool_of_o_def)

lemma [simp]: "(bool_of_o(P) = 1) \<longleftrightarrow> P"
by (simp add: bool_of_o_def)

lemma [simp]: "(bool_of_o(P) = 0) \<longleftrightarrow> \<not>P"
by (simp add: bool_of_o_def)

end
