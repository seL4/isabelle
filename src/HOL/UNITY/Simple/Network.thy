(*  Title:      HOL/UNITY/Simple/Network.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

The Communication Network.

From Misra, "A Logic for Concurrent Programming" (1994), section 5.7.
*)

theory Network imports "../UNITY" begin

(*The state assigns a number to each process variable*)

datatype pvar = Sent | Rcvd | Idle

datatype pname = Aproc | Bproc

type_synonym state = "pname * pvar => nat"

locale F_props =
  fixes F 
  assumes rsA: "F \<in> stable {s. s(Bproc,Rcvd) \<le> s(Aproc,Sent)}"
      and rsB: "F \<in> stable {s. s(Aproc,Rcvd) \<le> s(Bproc,Sent)}"
    and sent_nondec: "F \<in> stable {s. m \<le> s(proc,Sent)}"
    and rcvd_nondec: "F \<in> stable {s. n \<le> s(proc,Rcvd)}"
    and rcvd_idle: "F \<in> {s. s(proc,Idle) = Suc 0 & s(proc,Rcvd) = m}
                        co {s. s(proc,Rcvd) = m --> s(proc,Idle) = Suc 0}"
    and sent_idle: "F \<in> {s. s(proc,Idle) = Suc 0 & s(proc,Sent) = n}
                        co {s. s(proc,Sent) = n}"
begin

lemmas sent_nondec_A = sent_nondec [of _ Aproc]
    and sent_nondec_B = sent_nondec [of _ Bproc]
    and rcvd_nondec_A = rcvd_nondec [of _ Aproc]
    and rcvd_nondec_B = rcvd_nondec [of _ Bproc]
    and rcvd_idle_A = rcvd_idle [of Aproc]
    and rcvd_idle_B = rcvd_idle [of Bproc]
    and sent_idle_A = sent_idle [of Aproc]
    and sent_idle_B = sent_idle [of Bproc]

    and rs_AB = stable_Int [OF rsA rsB]

lemmas sent_nondec_AB = stable_Int [OF sent_nondec_A sent_nondec_B]
    and rcvd_nondec_AB = stable_Int [OF rcvd_nondec_A rcvd_nondec_B]
    and rcvd_idle_AB = constrains_Int [OF rcvd_idle_A rcvd_idle_B]
    and sent_idle_AB = constrains_Int [OF sent_idle_A sent_idle_B]

lemmas nondec_AB = stable_Int [OF sent_nondec_AB rcvd_nondec_AB]
    and idle_AB = constrains_Int [OF rcvd_idle_AB sent_idle_AB]

lemmas nondec_idle = constrains_Int [OF nondec_AB [unfolded stable_def] idle_AB]

lemma
  shows "F \<in> stable {s. s(Aproc,Idle) = Suc 0 & s(Bproc,Idle) = Suc 0 &  
                        s(Aproc,Sent) = s(Bproc,Rcvd) &  
                        s(Bproc,Sent) = s(Aproc,Rcvd) &  
                        s(Aproc,Rcvd) = m & s(Bproc,Rcvd) = n}"
apply (unfold stable_def) 
apply (rule constrainsI)
apply (drule constrains_Int [OF rs_AB [unfolded stable_def] nondec_idle, 
                             THEN constrainsD], assumption)
apply simp_all
apply (blast del: le0, clarify) 
apply (subgoal_tac "s' (Aproc, Rcvd) = s (Aproc, Rcvd)")
apply (subgoal_tac "s' (Bproc, Rcvd) = s (Bproc, Rcvd)") 
apply simp 
apply (blast intro: order_antisym le_trans eq_imp_le)+
done

end

end
