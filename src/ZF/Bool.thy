(*  Title:      ZF/bool.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

*)

header{*Booleans in Zermelo-Fraenkel Set Theory*}

theory Bool = pair:

syntax
    "1"         :: i             ("1")
    "2"         :: i             ("2")

translations
   "1"  == "succ(0)"
   "2"  == "succ(1)"

text{*2 is equal to bool, but is used as a number rather than a type.*}

constdefs
  bool        :: i
    "bool == {0,1}"

  cond        :: "[i,i,i]=>i"
    "cond(b,c,d) == if(b=1,c,d)"

  not         :: "i=>i"
    "not(b) == cond(b,0,1)"

  "and"       :: "[i,i]=>i"      (infixl "and" 70)
    "a and b == cond(a,b,0)"

  or          :: "[i,i]=>i"      (infixl "or" 65)
    "a or b == cond(a,1,b)"

  xor         :: "[i,i]=>i"      (infixl "xor" 65)
    "a xor b == cond(a,not(b),b)"


lemmas bool_defs = bool_def cond_def

lemma singleton_0: "{0} = 1"
by (simp add: succ_def)

(* Introduction rules *)

lemma bool_1I [simp,TC]: "1 : bool"
by (simp add: bool_defs )

lemma bool_0I [simp,TC]: "0 : bool"
by (simp add: bool_defs)

lemma one_not_0: "1~=0"
by (simp add: bool_defs )

(** 1=0 ==> R **)
lemmas one_neq_0 = one_not_0 [THEN notE, standard]

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

lemmas not_1 = not_def [THEN def_cond_1, standard, simp]
lemmas not_0 = not_def [THEN def_cond_0, standard, simp]

lemmas and_1 = and_def [THEN def_cond_1, standard, simp]
lemmas and_0 = and_def [THEN def_cond_0, standard, simp]

lemmas or_1 = or_def [THEN def_cond_1, standard, simp]
lemmas or_0 = or_def [THEN def_cond_0, standard, simp]

lemmas xor_1 = xor_def [THEN def_cond_1, standard, simp]
lemmas xor_0 = xor_def [THEN def_cond_0, standard, simp]

lemma not_type [TC]: "a:bool ==> not(a) : bool"
by (simp add: not_def)

lemma and_type [TC]: "[| a:bool;  b:bool |] ==> a and b : bool"
by (simp add: and_def)

lemma or_type [TC]: "[| a:bool;  b:bool |] ==> a or b : bool"
by (simp add: or_def)

lemma xor_type [TC]: "[| a:bool;  b:bool |] ==> a xor b : bool"
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


constdefs bool_of_o :: "o=>i"
   "bool_of_o(P) == (if P then 1 else 0)"

lemma [simp]: "bool_of_o(True) = 1"
by (simp add: bool_of_o_def) 

lemma [simp]: "bool_of_o(False) = 0"
by (simp add: bool_of_o_def) 

lemma [simp,TC]: "bool_of_o(P) \<in> bool"
by (simp add: bool_of_o_def) 

lemma [simp]: "(bool_of_o(P) = 1) <-> P"
by (simp add: bool_of_o_def) 

lemma [simp]: "(bool_of_o(P) = 0) <-> ~P"
by (simp add: bool_of_o_def) 

ML
{*
val bool_def = thm "bool_def";

val bool_defs = thms "bool_defs";
val singleton_0 = thm "singleton_0";
val bool_1I = thm "bool_1I";
val bool_0I = thm "bool_0I";
val one_not_0 = thm "one_not_0";
val one_neq_0 = thm "one_neq_0";
val boolE = thm "boolE";
val cond_1 = thm "cond_1";
val cond_0 = thm "cond_0";
val cond_type = thm "cond_type";
val cond_simple_type = thm "cond_simple_type";
val def_cond_1 = thm "def_cond_1";
val def_cond_0 = thm "def_cond_0";
val not_1 = thm "not_1";
val not_0 = thm "not_0";
val and_1 = thm "and_1";
val and_0 = thm "and_0";
val or_1 = thm "or_1";
val or_0 = thm "or_0";
val xor_1 = thm "xor_1";
val xor_0 = thm "xor_0";
val not_type = thm "not_type";
val and_type = thm "and_type";
val or_type = thm "or_type";
val xor_type = thm "xor_type";
val bool_typechecks = thms "bool_typechecks";
val not_not = thm "not_not";
val not_and = thm "not_and";
val not_or = thm "not_or";
val and_absorb = thm "and_absorb";
val and_commute = thm "and_commute";
val and_assoc = thm "and_assoc";
val and_or_distrib = thm "and_or_distrib";
val or_absorb = thm "or_absorb";
val or_commute = thm "or_commute";
val or_assoc = thm "or_assoc";
val or_and_distrib = thm "or_and_distrib";
*}

end
