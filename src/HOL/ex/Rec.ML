open Rec;

goalw thy [mono_def,Domf_def] "mono(Domf(F))";
by (DEPTH_SOLVE (slow_step_tac set_cs 1));
qed "mono_Domf";
