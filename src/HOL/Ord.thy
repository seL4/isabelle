(*  Title:      HOL/Ord.thy
    ID:         $Id$
    Author:     Tobias Nipkow, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Type classes for order signatures and orders.
*)

theory Ord = HOL:


axclass
  ord < "term"

syntax
  "op <"        :: "['a::ord, 'a] => bool"             ("op <")
  "op <="       :: "['a::ord, 'a] => bool"             ("op <=")

global

consts
  "op <"        :: "['a::ord, 'a] => bool"             ("(_/ < _)"  [50, 51] 50)
  "op <="       :: "['a::ord, 'a] => bool"             ("(_/ <= _)" [50, 51] 50)

local

syntax (symbols)
  "op <="       :: "['a::ord, 'a] => bool"             ("op \\<le>")
  "op <="       :: "['a::ord, 'a] => bool"             ("(_/ \\<le> _)"  [50, 51] 50)

(*Tell Blast_tac about overloading of < and <= to reduce the risk of
  its applying a rule for the wrong type*)
ML {*
Blast.overloaded ("op <" , domain_type);
Blast.overloaded ("op <=", domain_type);
*}


constdefs
  mono          :: "['a::ord => 'b::ord] => bool"      (*monotonicity*)
                "mono(f)   == (!A B. A <= B --> f(A) <= f(B))"

lemma monoI [intro?]: "[| !!A B. A <= B ==> f(A) <= f(B) |] ==> mono(f)"
apply (unfold mono_def)
apply fast
done

lemma monoD [dest?]: "[| mono(f);  A <= B |] ==> f(A) <= f(B)"
apply (unfold mono_def)
apply fast
done


constdefs
  min     :: "['a::ord, 'a] => 'a"
             "min a b   == (if a <= b then a else b)"
  max     :: "['a::ord, 'a] => 'a"
             "max a b   == (if a <= b then b else a)"

lemma min_leastL: "(!!x. least <= x) ==> min least x = least"
apply (simp add: min_def)
done

lemma min_of_mono: 
  "!x y. (f x <= f y) = (x <= y) ==> min (f m) (f n) = f (min m n)"
apply (simp add: min_def)
done

lemma max_leastL: "(!!x. least <= x) ==> max least x = x"
apply (simp add: max_def)
done

lemma max_of_mono: 
  "!x y. (f x <= f y) = (x <= y) ==> max (f m) (f n) = f (max m n)"
apply (simp add: max_def)
done

constdefs
  LeastM   :: "['a => 'b::ord, 'a => bool] => 'a"
              "LeastM m P == @x. P x & (!y. P y --> m x <= m y)"
  Least    :: "('a::ord => bool) => 'a"               (binder "LEAST " 10)
              "Least     == LeastM (%x. x)"

syntax
 "@LeastM" :: "[pttrn, 'a=>'b::ord, bool] => 'a" ("LEAST _ WRT _. _" [0,4,10]10)
translations
                "LEAST x WRT m. P" == "LeastM m (%x. P)"

lemma LeastMI2: "[| P x; !!y. P y ==> m x <= m y;
 !!x. [| P x; \\<forall>y. P y \\<longrightarrow> m x \\<le> m y |] ==> Q x
		 |] ==> Q (LeastM m P)";
apply (unfold LeastM_def)
apply (rule someI2_ex)
apply  blast
apply blast
done


section "Orders"

axclass order < ord
  order_refl [iff]:                          "x <= x"
  order_trans:      "[| x <= y; y <= z |] ==> x <= z"
  order_antisym:    "[| x <= y; y <= x |] ==> x = y"
  order_less_le:    "x < y = (x <= y & x ~= y)"

(** Reflexivity **)

(*This form is useful with the classical reasoner*)
lemma order_eq_refl: "!!x::'a::order. x = y ==> x <= y"
apply (erule ssubst)
apply (rule order_refl)
done

lemma order_less_irrefl [simp]: "~ x < (x::'a::order)"
apply (simp (no_asm) add: order_less_le)
done

lemma order_le_less: "(x::'a::order) <= y = (x < y | x = y)"
apply (simp (no_asm) add: order_less_le)
   (*NOT suitable for AddIffs, since it can cause PROOF FAILED*)
apply (blast intro!: order_refl)
done

lemmas order_le_imp_less_or_eq = order_le_less [THEN iffD1, standard]

lemma order_less_imp_le: "!!x::'a::order. x < y ==> x <= y"
apply (simp add: order_less_le)
done

(** Asymmetry **)

lemma order_less_not_sym: "(x::'a::order) < y ==> ~ (y<x)"
apply (simp add: order_less_le order_antisym)
done

(* [| n<m;  ~P ==> m<n |] ==> P *)
lemmas order_less_asym = order_less_not_sym [THEN contrapos_np, standard]

(* Transitivity *)

lemma order_less_trans: "!!x::'a::order. [| x < y; y < z |] ==> x < z"
apply (simp add: order_less_le)
apply (blast intro: order_trans order_antisym)
done

lemma order_le_less_trans: "!!x::'a::order. [| x <= y; y < z |] ==> x < z"
apply (simp add: order_less_le)
apply (blast intro: order_trans order_antisym)
done

lemma order_less_le_trans: "!!x::'a::order. [| x < y; y <= z |] ==> x < z"
apply (simp add: order_less_le)
apply (blast intro: order_trans order_antisym)
done


(** Useful for simplification, but too risky to include by default. **)

lemma order_less_imp_not_less: "(x::'a::order) < y ==>  (~ y < x) = True"
apply (blast elim: order_less_asym)
done

lemma order_less_imp_triv: "(x::'a::order) < y ==>  (y < x --> P) = True"
apply (blast elim: order_less_asym)
done

lemma order_less_imp_not_eq: "(x::'a::order) < y ==>  (x = y) = False"
apply auto
done

lemma order_less_imp_not_eq2: "(x::'a::order) < y ==>  (y = x) = False"
apply auto
done

(* Other operators *)

lemma min_leastR: "(!!x::'a::order. least <= x) ==> min x least = least"
apply (simp (no_asm_simp) add: min_def)
apply (blast intro: order_antisym)
done

lemma max_leastR: "(!!x::'a::order. least <= x) ==> max x least = x"
apply (simp add: max_def)
apply (blast intro: order_antisym)
done

lemma LeastM_equality:
 "[| P k; !!x. P x ==> m k <= m x |] ==> m (LEAST x WRT m. P x) = 
     (m k::'a::order)";
apply (rule LeastMI2)
apply   assumption
apply  blast
apply (blast intro!: order_antisym) 
done

lemma Least_equality:
  "[| P (k::'a::order); !!x. P x ==> k <= x |] ==> (LEAST x. P x) = k";
apply (unfold Least_def)
apply (erule LeastM_equality)
apply blast
done


section "Linear/Total Orders"

axclass linorder < order
  linorder_linear: "x <= y | y <= x"

lemma linorder_less_linear: "!!x::'a::linorder. x<y | x=y | y<x"
apply (simp (no_asm) add: order_less_le)
apply (cut_tac linorder_linear)
apply blast
done

lemma linorder_less_split: 
  "[| (x::'a::linorder)<y ==> P; x=y ==> P; y<x ==> P |] ==> P"
apply (cut_tac linorder_less_linear)
apply blast
done

lemma linorder_not_less: "!!x::'a::linorder. (~ x < y) = (y <= x)"
apply (simp (no_asm) add: order_less_le)
apply (cut_tac linorder_linear)
apply (blast intro: order_antisym)
done

lemma linorder_not_le: "!!x::'a::linorder. (~ x <= y) = (y < x)"
apply (simp (no_asm) add: order_less_le)
apply (cut_tac linorder_linear)
apply (blast intro: order_antisym)
done

lemma linorder_neq_iff: "!!x::'a::linorder. (x ~= y) = (x<y | y<x)"
apply (cut_tac x = "x" and y = "y" in linorder_less_linear)
apply auto
done

(* eliminates ~= in premises *)
lemmas linorder_neqE = linorder_neq_iff [THEN iffD1, THEN disjE, standard]

section "min & max on (linear) orders"

lemma min_same [simp]: "min (x::'a::order) x = x"
apply (simp add: min_def)
done

lemma max_same [simp]: "max (x::'a::order) x = x"
apply (simp add: max_def)
done

lemma le_max_iff_disj: "!!z::'a::linorder. (z <= max x y) = (z <= x | z <= y)"
apply (unfold max_def)
apply (simp (no_asm))
apply (cut_tac linorder_linear)
apply (blast intro: order_trans)
done

lemma le_maxI1: "(x::'a::linorder) <= max x y"
apply (simp (no_asm) add: le_max_iff_disj)
done

lemma le_maxI2: "(y::'a::linorder) <= max x y"
apply (simp (no_asm) add: le_max_iff_disj)
done
(*CANNOT use with AddSIs because blast_tac will give PROOF FAILED.*)

lemma less_max_iff_disj: "!!z::'a::linorder. (z < max x y) = (z < x | z < y)"
apply (simp (no_asm) add: max_def order_le_less)
apply (cut_tac linorder_less_linear)
apply (blast intro: order_less_trans)
done

lemma max_le_iff_conj [simp]: 
  "!!z::'a::linorder. (max x y <= z) = (x <= z & y <= z)"
apply (simp (no_asm) add: max_def)
apply (cut_tac linorder_linear)
apply (blast intro: order_trans)
done

lemma max_less_iff_conj [simp]: 
  "!!z::'a::linorder. (max x y < z) = (x < z & y < z)"
apply (simp (no_asm) add: order_le_less max_def)
apply (cut_tac linorder_less_linear)
apply (blast intro: order_less_trans)
done

lemma le_min_iff_conj [simp]: 
  "!!z::'a::linorder. (z <= min x y) = (z <= x & z <= y)"
apply (simp (no_asm) add: min_def)
apply (cut_tac linorder_linear)
apply (blast intro: order_trans)
done
(* AddIffs screws up a blast_tac in MiniML *)

lemma min_less_iff_conj [simp]:
  "!!z::'a::linorder. (z < min x y) = (z < x & z < y)"
apply (simp (no_asm) add: order_le_less min_def)
apply (cut_tac linorder_less_linear)
apply (blast intro: order_less_trans)
done

lemma min_le_iff_disj: "!!z::'a::linorder. (min x y <= z) = (x <= z | y <= z)"
apply (unfold min_def)
apply (simp (no_asm))
apply (cut_tac linorder_linear)
apply (blast intro: order_trans)
done

lemma min_less_iff_disj: "!!z::'a::linorder. (min x y < z) = (x < z | y < z)"
apply (unfold min_def)
apply (simp (no_asm) add: order_le_less)
apply (cut_tac linorder_less_linear)
apply (blast intro: order_less_trans)
done

lemma split_min: 
 "P(min (i::'a::linorder) j) = ((i <= j --> P(i)) & (~ i <= j --> P(j)))"
apply (simp (no_asm) add: min_def)
done

lemma split_max: 
 "P(max (i::'a::linorder) j) = ((i <= j --> P(j)) & (~ i <= j --> P(i)))"
apply (simp (no_asm) add: max_def)
done


section "bounded quantifiers"

syntax
  "_lessAll" :: "[idt, 'a, bool] => bool"  ("(3ALL _<_./ _)"  [0, 0, 10] 10)
  "_lessEx"  :: "[idt, 'a, bool] => bool"  ("(3EX _<_./ _)"  [0, 0, 10] 10)
  "_leAll"   :: "[idt, 'a, bool] => bool"  ("(3ALL _<=_./ _)" [0, 0, 10] 10)
  "_leEx"    :: "[idt, 'a, bool] => bool"  ("(3EX _<=_./ _)" [0, 0, 10] 10)

syntax (symbols)
  "_lessAll" :: "[idt, 'a, bool] => bool"  ("(3\\<forall>_<_./ _)"  [0, 0, 10] 10)
  "_lessEx"  :: "[idt, 'a, bool] => bool"  ("(3\\<exists>_<_./ _)"  [0, 0, 10] 10)
  "_leAll"   :: "[idt, 'a, bool] => bool"  ("(3\\<forall>_\\<le>_./ _)" [0, 0, 10] 10)
  "_leEx"    :: "[idt, 'a, bool] => bool"  ("(3\\<exists>_\\<le>_./ _)" [0, 0, 10] 10)

syntax (HOL)
  "_lessAll" :: "[idt, 'a, bool] => bool"  ("(3! _<_./ _)"  [0, 0, 10] 10)
  "_lessEx"  :: "[idt, 'a, bool] => bool"  ("(3? _<_./ _)"  [0, 0, 10] 10)
  "_leAll"   :: "[idt, 'a, bool] => bool"  ("(3! _<=_./ _)" [0, 0, 10] 10)
  "_leEx"    :: "[idt, 'a, bool] => bool"  ("(3? _<=_./ _)" [0, 0, 10] 10)

translations
 "ALL x<y. P"   =>  "ALL x. x < y --> P"
 "EX x<y. P"    =>  "EX x. x < y  & P"
 "ALL x<=y. P"  =>  "ALL x. x <= y --> P"
 "EX x<=y. P"   =>  "EX x. x <= y & P"


ML
{*
val mono_def = thm "mono_def";
val monoI = thm "monoI";
val monoD = thm "monoD";
val min_def = thm "min_def";
val min_of_mono = thm "min_of_mono";
val max_def = thm "max_def";
val max_of_mono = thm "max_of_mono";
val min_leastL = thm "min_leastL";
val max_leastL = thm "max_leastL";
val LeastMI2 = thm "LeastMI2";
val LeastM_equality = thm "LeastM_equality";
val Least_def = thm "Least_def";
val Least_equality = thm "Least_equality";
val min_leastR = thm "min_leastR";
val max_leastR = thm "max_leastR";
val order_eq_refl = thm "order_eq_refl";
val order_less_irrefl = thm "order_less_irrefl";
val order_le_less = thm "order_le_less";
val order_le_imp_less_or_eq = thm "order_le_imp_less_or_eq";
val order_less_imp_le = thm "order_less_imp_le";
val order_less_not_sym = thm "order_less_not_sym";
val order_less_asym = thm "order_less_asym";
val order_less_trans = thm "order_less_trans";
val order_le_less_trans = thm "order_le_less_trans";
val order_less_le_trans = thm "order_less_le_trans";
val order_less_imp_not_less = thm "order_less_imp_not_less";
val order_less_imp_triv = thm "order_less_imp_triv";
val order_less_imp_not_eq = thm "order_less_imp_not_eq";
val order_less_imp_not_eq2 = thm "order_less_imp_not_eq2";
val linorder_less_linear = thm "linorder_less_linear";
val linorder_less_split = thm "linorder_less_split";
val linorder_not_less = thm "linorder_not_less";
val linorder_not_le = thm "linorder_not_le";
val linorder_neq_iff = thm "linorder_neq_iff";
val linorder_neqE = thm "linorder_neqE";
val min_same = thm "min_same";
val max_same = thm "max_same";
val le_max_iff_disj = thm "le_max_iff_disj";
val le_maxI1 = thm "le_maxI1";
val le_maxI2 = thm "le_maxI2";
val less_max_iff_disj = thm "less_max_iff_disj";
val max_le_iff_conj = thm "max_le_iff_conj";
val max_less_iff_conj = thm "max_less_iff_conj";
val le_min_iff_conj = thm "le_min_iff_conj";
val min_less_iff_conj = thm "min_less_iff_conj";
val min_le_iff_disj = thm "min_le_iff_disj";
val min_less_iff_disj = thm "min_less_iff_disj";
val split_min = thm "split_min";
val split_max = thm "split_max";
val order_refl = thm "order_refl";
val order_trans = thm "order_trans";
val order_antisym = thm "order_antisym";
val order_less_le = thm "order_less_le";
val linorder_linear = thm "linorder_linear";
*}

end
