local
  fun prover s = prove_goal Init.thy s 
                    (K [force_tac (claset(), simpset() addsimps [Init_def]) 1])
in
  val const_simps = map (int_rewrite o prover)
      [ "|- (Init #True) = #True",
        "|- (Init #False) = #False"]
  val Init_simps = map (int_rewrite o prover)
      [ "|- (Init ~F) = (~ Init F)",
        "|- (Init (P --> Q)) = (Init P --> Init Q)",
        "|- (Init (P & Q)) = (Init P & Init Q)",
        "|- (Init (P | Q)) = (Init P | Init Q)",
        "|- (Init (P = Q)) = ((Init P) = (Init Q))",
        "|- (Init (!x. F x)) = (!x. (Init F x))",
        "|- (Init (? x. F x)) = (? x. (Init F x))",
        "|- (Init (?! x. F x)) = (?! x. (Init F x))"
      ]
end;

Addsimps const_simps;

Goal "|- (Init $P) = (Init P)";
by (force_tac (claset(), simpset() addsimps [Init_def,fw_act_def,fw_stp_def]) 1);
qed "Init_stp_act";
val Init_simps = (int_rewrite Init_stp_act)::Init_simps;
bind_thm("Init_stp_act_rev", symmetric(int_rewrite Init_stp_act));

Goal "|- (Init F) = F";
by (force_tac (claset(), simpset() addsimps [Init_def,fw_temp_def]) 1);
qed "Init_temp";
val Init_simps = (int_rewrite Init_temp)::Init_simps;

(* Trivial instances of the definitions that avoid introducing lambda expressions. *)
Goalw [Init_def,fw_stp_def] "(sigma |= Init P) = P (st1 sigma)";
by (rtac refl 1);
qed "Init_stp";

Goalw [Init_def,fw_act_def] "(sigma |= Init A) = A (st1 sigma, st2 sigma)";
by (rtac refl 1);
qed "Init_act";

val Init_defs = [Init_stp, Init_act, int_use Init_temp];

