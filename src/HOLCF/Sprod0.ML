
(* legacy ML bindings *)

val Ispair_def = thm "Ispair_def";
val Isfst_def = thm "Isfst_def";
val Issnd_def = thm "Issnd_def";
val SprodI = thm "SprodI";
val inj_on_Abs_Sprod = thm "inj_on_Abs_Sprod";
val strict_Spair_Rep = thm "strict_Spair_Rep";
val defined_Spair_Rep_rev = thm "defined_Spair_Rep_rev";
val inject_Spair_Rep = thm "inject_Spair_Rep";
val inject_Ispair = thm "inject_Ispair";
val strict_Ispair = thm "strict_Ispair";
val strict_Ispair1 = thm "strict_Ispair1";
val strict_Ispair2 = thm "strict_Ispair2";
val strict_Ispair_rev = thm "strict_Ispair_rev";
val defined_Ispair_rev = thm "defined_Ispair_rev";
val defined_Ispair = thm "defined_Ispair";
val Exh_Sprod = thm "Exh_Sprod";
val IsprodE = thm "IsprodE";
val strict_Isfst = thm "strict_Isfst";
val strict_Isfst1 = thm "strict_Isfst1";
val strict_Isfst2 = thm "strict_Isfst2";
val strict_Issnd = thm "strict_Issnd";
val strict_Issnd1 = thm "strict_Issnd1";
val strict_Issnd2 = thm "strict_Issnd2";
val Isfst = thm "Isfst";
val Issnd = thm "Issnd";
val Isfst2 = thm "Isfst2";
val Issnd2 = thm "Issnd2";
val Sprod0_ss = [strict_Isfst1, strict_Isfst2, strict_Issnd1, strict_Issnd2,
                 Isfst2, Issnd2]
val defined_IsfstIssnd = thm "defined_IsfstIssnd";
val surjective_pairing_Sprod = thm "surjective_pairing_Sprod";
val Sel_injective_Sprod = thm "Sel_injective_Sprod";
