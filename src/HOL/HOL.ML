(*  Title:      HOL/HOL.ML
    ID:         $Id$
*)

structure HOL =
struct
  val thy = the_context ();
  val plusI = plusI;
  val minusI = minusI;
  val timesI = timesI;
  val eq_reflection = eq_reflection;
  val refl = refl;
  val subst = subst;
  val ext = ext;
  val impI = impI;
  val mp = mp;
  val True_def = True_def;
  val All_def = All_def;
  val Ex_def = Ex_def;
  val False_def = False_def;
  val not_def = not_def;
  val and_def = and_def;
  val or_def = or_def;
  val Ex1_def = Ex1_def;
  val iff = iff;
  val True_or_False = True_or_False;
  val Let_def = Let_def;
  val if_def = if_def;
  val arbitrary_def = arbitrary_def;
end;

open HOL;

val Least_def = thm "Least_def";
val Least_equality = thm "Least_equality";
val mono_def = thm "mono_def";
val monoI = thm "monoI";
val monoD = thm "monoD";
val min_def = thm "min_def";
val min_of_mono = thm "min_of_mono";
val max_def = thm "max_def";
val max_of_mono = thm "max_of_mono";
val min_leastL = thm "min_leastL";
val max_leastL = thm "max_leastL";
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
val linorder_cases = thm "linorder_cases";
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
