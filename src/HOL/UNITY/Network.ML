(*  Title:      HOL/UNITY/Network
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

The Communication Network

From Misra, "A Logic for Concurrent Programming" (1994), section 5.7
*)

val [rsA, rsB, sent_nondec, rcvd_nondec, rcvd_idle, sent_idle] = 
Goalw [stable_def]
   "[| !! m. F : stable {s. s(Bproc,Rcvd) <= s(Aproc,Sent)};  \
\      !! m. F : stable {s. s(Aproc,Rcvd) <= s(Bproc,Sent)};  \
\      !! m proc. F : stable {s. m <= s(proc,Sent)};  \
\      !! n proc. F : stable {s. n <= s(proc,Rcvd)};  \
\      !! m proc. F : {s. s(proc,Idle) = 1 & s(proc,Rcvd) = m} co \
\                                 {s. s(proc,Rcvd) = m --> s(proc,Idle) = 1}; \
\      !! n proc. F : {s. s(proc,Idle) = 1 & s(proc,Sent) = n} co \
\                                 {s. s(proc,Sent) = n} \
\   |] ==> F : stable {s. s(Aproc,Idle) = 1 & s(Bproc,Idle) = 1 & \
\                         s(Aproc,Sent) = s(Bproc,Rcvd) & \
\                         s(Bproc,Sent) = s(Aproc,Rcvd) & \
\                         s(Aproc,Rcvd) = m & s(Bproc,Rcvd) = n}";

val sent_nondec_A = read_instantiate [("proc","Aproc")] sent_nondec;
val sent_nondec_B = read_instantiate [("proc","Bproc")] sent_nondec;
val rcvd_nondec_A = read_instantiate [("proc","Aproc")] rcvd_nondec;
val rcvd_nondec_B = read_instantiate [("proc","Bproc")] rcvd_nondec;
val rcvd_idle_A = read_instantiate [("proc","Aproc")] rcvd_idle;
val rcvd_idle_B = read_instantiate [("proc","Bproc")] rcvd_idle;
val sent_idle_A = read_instantiate [("proc","Aproc")] sent_idle;
val sent_idle_B = read_instantiate [("proc","Bproc")] sent_idle;

val rs_AB = [rsA, rsB] MRS constrains_Int;
val sent_nondec_AB = [sent_nondec_A, sent_nondec_B] MRS constrains_Int;
val rcvd_nondec_AB = [rcvd_nondec_A, rcvd_nondec_B] MRS constrains_Int;
val rcvd_idle_AB = [rcvd_idle_A, rcvd_idle_B] MRS constrains_Int;
val sent_idle_AB = [sent_idle_A, sent_idle_B] MRS constrains_Int;
val nondec_AB = [sent_nondec_AB, rcvd_nondec_AB] MRS constrains_Int;
val idle_AB = [rcvd_idle_AB, sent_idle_AB] MRS constrains_Int;
val nondec_idle = [nondec_AB, idle_AB] MRS constrains_Int;

by (rtac constrainsI 1);
by (dtac ([rs_AB, nondec_idle] MRS constrains_Int RS constrainsD) 1);
by (assume_tac 1);
by (ALLGOALS Asm_full_simp_tac);
by (blast_tac (HOL_cs addIs [order_refl]) 1);
by (Clarify_tac 1);
by (subgoals_tac ["s' (Aproc, Rcvd) = s (Aproc, Rcvd)",
		  "s' (Bproc, Rcvd) = s (Bproc, Rcvd)"] 1);
by (REPEAT 
    (blast_tac (claset() addIs [order_antisym, le_trans, eq_imp_le]) 2));
by (Asm_simp_tac 1);
result();




