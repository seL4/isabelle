
(* legacy ML bindings *)

val Istrictify_def = thm "Istrictify_def";
val strictify_def = thm "strictify_def";
val ID_def = thm "ID_def";
val oo_def = thm "oo_def";
val inst_cfun_pcpo = thm "inst_cfun_pcpo";
val contlub_Rep_CFun1 = thm "contlub_Rep_CFun1";
val cont_Rep_CFun1 = thm "cont_Rep_CFun1";
val contlub_cfun_fun = thm "contlub_cfun_fun";
val cont_cfun_fun = thm "cont_cfun_fun";
val contlub_cfun = thm "contlub_cfun";
val cont_cfun = thm "cont_cfun";
val cont2cont_Rep_CFun = thm "cont2cont_Rep_CFun";
val cont2mono_LAM = thm "cont2mono_LAM";
val cont2cont_LAM = thm "cont2cont_LAM";
val cont_lemmas1 = [cont_const, cont_id, cont_Rep_CFun2,
                    cont2cont_Rep_CFun, cont2cont_LAM];
val strict_Rep_CFun1 = thm "strict_Rep_CFun1";
val Istrictify1 = thm "Istrictify1";
val Istrictify2 = thm "Istrictify2";
val monofun_Istrictify1 = thm "monofun_Istrictify1";
val monofun_Istrictify2 = thm "monofun_Istrictify2";
val contlub_Istrictify1 = thm "contlub_Istrictify1";
val contlub_Istrictify2 = thm "contlub_Istrictify2";
val cont_Istrictify1 = thm "cont_Istrictify1";
val cont_Istrictify2 = thm "cont_Istrictify2";
val strictify1 = thm "strictify1";
val strictify2 = thm "strictify2";
val chfin_Rep_CFunR = thm "chfin_Rep_CFunR";
val iso_strict = thm "iso_strict";
val isorep_defined = thm "isorep_defined";
val isoabs_defined = thm "isoabs_defined";
val chfin2chfin = thm "chfin2chfin";
val flat2flat = thm "flat2flat";
val flat_codom = thm "flat_codom";
val ID1 = thm "ID1";
val cfcomp1 = thm "cfcomp1";
val cfcomp2 = thm "cfcomp2";
val ID2 = thm "ID2";
val ID3 = thm "ID3";
val assoc_oo = thm "assoc_oo";

structure Cfun3 =
struct
  val thy = the_context ();
  val Istrictify_def = Istrictify_def;
  val strictify_def = strictify_def;
  val ID_def = ID_def;
  val oo_def = oo_def;
end;
