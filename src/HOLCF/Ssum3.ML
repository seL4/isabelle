
(* legacy ML bindings *)

val sinl_def = thm "sinl_def";
val sinr_def = thm "sinr_def";
val sscase_def = thm "sscase_def";
val inst_ssum_pcpo = thm "inst_ssum_pcpo";
val contlub_Isinl = thm "contlub_Isinl";
val contlub_Isinr = thm "contlub_Isinr";
val cont_Isinl = thm "cont_Isinl";
val cont_Isinr = thm "cont_Isinr";
val contlub_Iwhen1 = thm "contlub_Iwhen1";
val contlub_Iwhen2 = thm "contlub_Iwhen2";
val ssum_lemma9 = thm "ssum_lemma9";
val ssum_lemma10 = thm "ssum_lemma10";
val ssum_lemma11 = thm "ssum_lemma11";
val ssum_lemma12 = thm "ssum_lemma12";
val ssum_lemma13 = thm "ssum_lemma13";
val contlub_Iwhen3 = thm "contlub_Iwhen3";
val cont_Iwhen1 = thm "cont_Iwhen1";
val cont_Iwhen2 = thm "cont_Iwhen2";
val cont_Iwhen3 = thm "cont_Iwhen3";
val strict_sinl = thm "strict_sinl";
val strict_sinr = thm "strict_sinr";
val noteq_sinlsinr = thm "noteq_sinlsinr";
val inject_sinl = thm "inject_sinl";
val inject_sinr = thm "inject_sinr";
val defined_sinl = thm "defined_sinl";
val defined_sinr = thm "defined_sinr";
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
val ssum_chainE = thm "ssum_chainE";
val thelub_ssum2a = thm "thelub_ssum2a";
val thelub_ssum2b = thm "thelub_ssum2b";
val thelub_ssum2a_rev = thm "thelub_ssum2a_rev";
val thelub_ssum2b_rev = thm "thelub_ssum2b_rev";
val thelub_ssum3 = thm "thelub_ssum3";
val sscase4 = thm "sscase4";
val Ssum_rews = [strict_sinl, strict_sinr, defined_sinl, defined_sinr,
                sscase1, sscase2, sscase3]
