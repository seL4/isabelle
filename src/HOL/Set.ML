
(* legacy ML bindings *)

structure Set =
struct
  val thy = the_context ();
  val Ball_def = Ball_def;
  val Bex_def = Bex_def;
  val Collect_mem_eq = Collect_mem_eq;
  val Compl_def = Compl_def;
  val INTER_def = INTER_def;
  val Int_def = Int_def;
  val Inter_def = Inter_def;
  val Pow_def = Pow_def;
  val UNION_def = UNION_def;
  val UNIV_def = UNIV_def;
  val Un_def = Un_def;
  val Union_def = Union_def;
  val empty_def = empty_def;
  val image_def = image_def;
  val insert_def = insert_def;
  val mem_Collect_eq = mem_Collect_eq;
  val psubset_def = psubset_def;
  val set_diff_def = set_diff_def;
  val subset_def = subset_def;
end;
