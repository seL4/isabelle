
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
val sinl_defined = thm "sinl_defined";
val sinr_defined = thm "sinr_defined";
val Exh_Ssum1 = thm "Exh_Ssum1";
val ssumE = thm "ssumE";
val ssumE2 = thm "ssumE2";
val sscase1 = thm "sscase1";
val sscase2 = thm "sscase2";
val sscase3 = thm "sscase3";
val less_ssum4a = thm "less_ssum4a";
val less_ssum4b = thm "less_ssum4b";
val less_ssum4c = thm "less_ssum4c";
val less_ssum4d = thm "less_ssum4d";
val sscase4 = thm "sscase4";
val Ssum_rews = [sinl_strict, sinr_strict, sinl_defined, sinr_defined,
                sscase1, sscase2, sscase3];
