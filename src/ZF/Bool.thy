(*  Title:      ZF/Bool.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge
*)

header{*Booleans in Zermelo-Fraenkel Set Theory*}

theory Bool imports pair begin

abbreviation
  one  ("1") where
  "1 == succ(0)"

abbreviation
  two  ("2") where
  "2 == succ(1)"

text{*2 is equal to bool, but is used as a number rather than a type.*}

definition "bool == {0,1}"

definition "cond(b,c,d) == if(b=1,c,d)"

definition "not(b) == cond(b,0,1)"

definition
  "and"       :: "[i,i]=>i"      (infixl "and" 70)  where
    "a and b == cond(a,b,0)"

definition
  or          :: "[i,i]=>i"      (infixl "or" 65)  where
    "a or b == cond(a,1,b)"

definition
  xor         :: "[i,i]=>i"      (infixl "xor" 65) where
    "a xor b == cond(a,not(b),b)"


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

(** 1=0 ==> R **)
lemmas one_neq_0 = one_not_0 [THEN notE]

lemma boolE:
    "[| c: bool;  c=1 ==> P;  c=0 ==> P |] ==> P"
by (simp add: bool_defs, blast)

(** cond **)

(*1 means true*)
lemma cond_1 [simp]: "cond(1,c,d) = c"
by (simp add: bool_defs )

(*0 means false*)
lemma cond_0 [simp]: "cond(0,c,d) = d"
by (simp add: bool_defs )

lemma cond_type [TC]: "[| b: bool;  c: A(1);  d: A(0) |] ==> cond(b,c,d): A(b)"
by (simp add: bool_defs, blast)

(*For Simp_tac and Blast_tac*)
lemma cond_simple_type: "[| b: bool;  c: A;  d: A |] ==> cond(b,c,d): A"
by (simp add: bool_defs )

lemma def_cond_1: "[| !!b. j(b)==cond(b,c,d) |] ==> j(1) = c"
by simp

lemma def_cond_0: "[| !!b. j(b)==cond(b,c,d) |] ==> j(0) = d"
by simp

lemmas not_1 = not_def [THEN def_cond_1, simp]
lemmas not_0 = not_def [THEN def_cond_0, simp]

lemmas and_1 = and_def [THEN def_cond_1, simp]
lemmas and_0 = and_def [THEN def_cond_0, simp]

lemmas or_1 = or_def [THEN def_cond_1, simp]
lemmas or_0 = or_def [THEN def_cond_0, simp]

lemmas xor_1 = xor_def [THEN def_cond_1, simp]
lemmas xor_0 = xor_def [THEN def_cond_0, simp]

lemma not_type [TC]: "a:bool ==> not(a) \<in> bool"
by (simp add: not_def)

lemma and_type [TC]: "[| a:bool;  b:bool |] ==> a and b \<in> bool"
by (simp add: and_def)

lemma or_type [TC]: "[| a:bool;  b:bool |] ==> a or b \<in> bool"
by (simp add: or_def)

lemma xor_type [TC]: "[| a:bool;  b:bool |] ==> a xor b \<in> bool"
by (simp add: xor_def)

lemmas bool_typechecks = bool_1I bool_0I cond_type not_type and_type
                         or_type xor_type

subsection{*Laws About 'not' *}

lemma not_not [simp]: "a:bool ==> not(not(a)) = a"
by (elim boolE, auto)

lemma not_and [simp]: "a:bool ==> not(a and b) = not(a) or not(b)"
by (elim boolE, auto)

lemma not_or [simp]: "a:bool ==> not(a or b) = not(a) and not(b)"
by (elim boolE, auto)

subsection{*Laws About 'and' *}

lemma and_absorb [simp]: "a: bool ==> a and a = a"
by (elim boolE, auto)

lemma and_commute: "[| a: bool; b:bool |] ==> a and b = b and a"
by (elim boolE, auto)

lemma and_assoc: "a: bool ==> (a and b) and c  =  a and (b and c)"
by (elim boolE, auto)

lemma and_or_distrib: "[| a: bool; b:bool; c:bool |] ==>
       (a or b) and c  =  (a and c) or (b and c)"
by (elim boolE, auto)

subsection{*Laws About 'or' *}

lemma or_absorb [simp]: "a: bool ==> a or a = a"
by (elim boolE, auto)

lemma or_commute: "[| a: bool; b:bool |] ==> a or b = b or a"
by (elim boolE, auto)

lemma or_assoc: "a: bool ==> (a or b) or c  =  a or (b or c)"
by (elim boolE, auto)

lemma or_and_distrib: "[| a: bool; b: bool; c: bool |] ==>
           (a and b) or c  =  (a or c) and (b or c)"
by (elim boolE, auto)


definition
  bool_of_o :: "o=>i" where
   "bool_of_o(P) == (if P then 1 else 0)"

lemma [simp]: "bool_of_o(True) = 1"
by (simp add: bool_of_o_def)

lemma [simp]: "bool_of_o(False) = 0"
by (simp add: bool_of_o_def)

lemma [simp,TC]: "bool_of_o(P) \<in> bool"
by (simp add: bool_of_o_def)

lemma [simp]: "(bool_of_o(P) = 1) \<longleftrightarrow> P"
by (simp add: bool_of_o_def)

lemma [simp]: "(bool_of_o(P) = 0) \<longleftrightarrow> ~P"
by (simp add: bool_of_o_def)

end
