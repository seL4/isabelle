(*  Title:      HOL/UNITY/Network
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

The Communication Network

From Misra, "A Logic for Concurrent Programming" (1994), section 5.7
*)

theory Network = UNITY:

(*The state assigns a number to each process variable*)

datatype pvar = Sent | Rcvd | Idle

datatype pname = Aproc | Bproc

types state = "pname * pvar => nat"

locale F_props =
  fixes F 
  assumes rsA: "F : stable {s. s(Bproc,Rcvd) <= s(Aproc,Sent)}"
      and rsB: "F : stable {s. s(Aproc,Rcvd) <= s(Bproc,Sent)}"
    and sent_nondec: "F : stable {s. m <= s(proc,Sent)}"
    and rcvd_nondec: "F : stable {s. n <= s(proc,Rcvd)}"
    and rcvd_idle: "F : {s. s(proc,Idle) = Suc 0 & s(proc,Rcvd) = m}
                        co {s. s(proc,Rcvd) = m --> s(proc,Idle) = Suc 0}"
    and sent_idle: "F : {s. s(proc,Idle) = Suc 0 & s(proc,Sent) = n}
                        co {s. s(proc,Sent) = n}"
  

lemmas (in F_props) 
        sent_nondec_A = sent_nondec [of _ Aproc]
    and sent_nondec_B = sent_nondec [of _ Bproc]
    and rcvd_nondec_A = rcvd_nondec [of _ Aproc]
    and rcvd_nondec_B = rcvd_nondec [of _ Bproc]
    and rcvd_idle_A = rcvd_idle [of Aproc]
    and rcvd_idle_B = rcvd_idle [of Bproc]
    and sent_idle_A = sent_idle [of Aproc]
    and sent_idle_B = sent_idle [of Bproc]

    and rs_AB = stable_Int [OF rsA rsB]
    and sent_nondec_AB = stable_Int [OF sent_nondec_A sent_nondec_B]
    and rcvd_nondec_AB = stable_Int [OF rcvd_nondec_A rcvd_nondec_B]
    and rcvd_idle_AB = constrains_Int [OF rcvd_idle_A rcvd_idle_B]
    and sent_idle_AB = constrains_Int [OF sent_idle_A sent_idle_B]
    and nondec_AB = stable_Int [OF sent_nondec_AB rcvd_nondec_AB]
    and idle_AB = constrains_Int [OF rcvd_idle_AB sent_idle_AB]
    and nondec_idle = constrains_Int [OF nondec_AB [unfolded stable_def] 
                                         idle_AB]

lemma (in F_props)
  shows "F : stable {s. s(Aproc,Idle) = Suc 0 & s(Bproc,Idle) = Suc 0 &  
			s(Aproc,Sent) = s(Bproc,Rcvd) &  
			s(Bproc,Sent) = s(Aproc,Rcvd) &  
			s(Aproc,Rcvd) = m & s(Bproc,Rcvd) = n}"
apply (unfold stable_def) 
apply (rule constrainsI)
apply (drule constrains_Int [OF rs_AB [unfolded stable_def] nondec_idle, 
                             THEN constrainsD], assumption)
apply simp_all
apply (blast intro!: order_refl del: le0, clarify) 
apply (subgoal_tac "s' (Aproc, Rcvd) = s (Aproc, Rcvd)")
apply (subgoal_tac "s' (Bproc, Rcvd) = s (Bproc, Rcvd)") 
apply simp 
apply (blast intro: order_antisym le_trans eq_imp_le)+
done

end
