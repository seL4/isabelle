
val aut_simps = [Greater_def,one_leader_def,
  one_leader_asig_def,one_leader_trans_def,one_leader_initial_def,
  ring_def,aut0_asig_def,aut0_trans_def,aut0_initial_def,aut0_def,
  aut1_asig_def,aut1_trans_def,aut1_initial_def,aut1_def,
  aut2_asig_def,aut2_trans_def,aut2_initial_def,aut2_def];

(* property to prove: at most one (of 3) members of the ring will
	declare itself to leader *)
Goal "ring =<| one_leader";
by (is_sim_tac aut_simps 1); 
by Auto_tac;
qed"at_most_one_leader";
