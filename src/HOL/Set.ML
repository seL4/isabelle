
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

val vimageD = thm "vimageD";
val vimageE = thm "vimageE";
val vimageI = thm "vimageI";
val vimageI2 = thm "vimageI2";
val vimage_Collect = thm "vimage_Collect";
val vimage_Collect_eq = thm "vimage_Collect_eq";
val vimage_Compl = thm "vimage_Compl";
val vimage_Diff = thm "vimage_Diff";
val vimage_INT = thm "vimage_INT";
val vimage_Int = thm "vimage_Int";
val vimage_UN = thm "vimage_UN";
val vimage_UNIV = thm "vimage_UNIV";
val vimage_Un = thm "vimage_Un";
val vimage_Union = thm "vimage_Union";
val vimage_def = thm "vimage_def";
val vimage_empty = thm "vimage_empty";
val vimage_eq = thm "vimage_eq";
val vimage_eq_UN = thm "vimage_eq_UN";
val vimage_insert = thm "vimage_insert";
val vimage_mono = thm "vimage_mono";
val vimage_singleton_eq = thm "vimage_singleton_eq";
