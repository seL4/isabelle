
(* legacy ML bindings *)

val Iwhen_def = thm "Iwhen_def";
val Iwhen1 = thm "Iwhen1";
val Iwhen2 = thm "Iwhen2";
val Iwhen3 = thm "Iwhen3";
val less_ssum_def = thm "less_ssum_def";
val sinl_def = thm "sinl_def";
val sinr_def = thm "sinr_def";
val sscase_def = thm "sscase_def";
val cont_Iwhen1 = thm "cont_Iwhen1";
val cont_Iwhen2 = thm "cont_Iwhen2";
val cont_Iwhen3 = thm "cont_Iwhen3";
val sinl_strict = thm "sinl_strict";
val sinr_strict = thm "sinr_strict";
val noteq_sinlsinr = thm "noteq_sinlsinr";
val sinl_inject = thm "sinl_inject";
val sinr_inject = thm "sinr_inject";
val sinl_eq = thm "sinl_eq";
val sinr_eq = thm "sinr_eq";
val sinl_defined = thm "sinl_defined";
val sinr_defined = thm "sinr_defined";
val Exh_Ssum1 = thm "Exh_Ssum1";
val ssumE = thm "ssumE";
val ssumE2 = thm "ssumE2";
val sinl_less = thm "sinl_less";
val sinr_less = thm "sinr_less";
val sinl_less_sinr = thm "sinl_less_sinr";
val sinr_less_sinl = thm "sinr_less_sinl";
val sscase1 = thm "sscase1";
val sscase2 = thm "sscase2";
val sscase3 = thm "sscase3";
val sscase4 = thm "sscase4";
val Ssum_rews = [sinl_strict, sinr_strict, sinl_defined, sinr_defined,
                sscase1, sscase2, sscase3];
