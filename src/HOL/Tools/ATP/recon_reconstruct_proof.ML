

(****************************************)
(* Reconstruct an axiom resolution step *)
(****************************************)

 fun reconstruct_axiom clauses (clausenum:int) thml (numlist, symlist, nsymlist ) =  
                                     let val this_axiom =(assoc  clausenum clauses)
                                         val symmed = (apply_rule sym  symlist this_axiom)
                                         val nsymmed = (apply_rule not_sym nsymlist  symmed )
                                     in
                                         rearrange_prems numlist nsymmed
                                     end

(****************************************)
(* Reconstruct a binary resolution step *)
(****************************************)

fun reconstruct_binary ((clause1, lit1), (clause2 , lit2)) thml (numlist, symlist, nsymlist )
        = let
              val thm1 =  select_literal (lit1 + 1) (assoc  clause1 thml)
              val thm2 =  assoc  clause2 thml
              val res =   thm1 RSN ((lit2 +1), thm2)
              val symmed = (apply_rule sym  symlist res)
              val nsymmed = (apply_rule not_sym nsymlist  symmed )
          in
              rearrange_prems numlist nsymmed
          end


(****************************************)
(* Reconstruct a binary resolution step *)
(****************************************)

fun reconstruct_mrr ((clause1, lit1), (clause2 , lit2)) thml (numlist, symlist, nsymlist )
        = let
              val thm1 =  select_literal (lit1 + 1) (assoc  clause1 thml)
              val thm2 =  assoc  clause2 thml
              val res =   thm1 RSN ((lit2 +1), thm2)
              val symmed = (apply_rule sym  symlist res)
              val nsymmed = (apply_rule not_sym nsymlist  symmed )
          in
              rearrange_prems numlist nsymmed
          end

(*******************************************)
(* Reconstruct a factoring resolution step *)
(*******************************************)

fun reconstruct_factor (clause,  lit1, lit2) thml (numlist, symlist, nsymlist )= 
                          let 
                            val th =  assoc clause thml
                            val prems = prems_of th
                            val fac1 = get_nth (lit1+1) prems
                            val fac2 = get_nth (lit2+1) prems
                            val unif_env = unifiers (Mainsign,myenv, [(fac1, fac2)])
                            val newenv = getnewenv unif_env
                            val envlist = alist_of newenv
                            
                            val newsubsts = mksubstlist envlist []
                          in 
                            if (is_Var (fst(hd(newsubsts))))
                            then
                                let 
                                   val str1 = lit_string_with_nums (fst (hd newsubsts));
                                   val str2 = lit_string_with_nums (snd (hd newsubsts));
                                   val facthm = read_instantiate [(str1,str2)] th;
                                   val res = hd (Seq.list_of(delete_assump_tac  facthm (lit1 + 1)))
                                   val symmed = (apply_rule sym  symlist res)
                                   val nsymmed = (apply_rule not_sym nsymlist  symmed )
         
                                in 
                                   rearrange_prems numlist nsymmed
                                end
                            else
                                let
                                   val str2 = lit_string_with_nums (fst (hd newsubsts));
                                   val str1 = lit_string_with_nums (snd (hd newsubsts));
                                   val facthm = read_instantiate [(str1,str2)] th;
                                   val res = hd (Seq.list_of(delete_assump_tac  facthm (lit1 + 1)))
                                   val symmed = (apply_rule sym  symlist res)
                                   val nsymmed = (apply_rule not_sym nsymlist  symmed )
                                in 
                                    rearrange_prems numlist nsymmed    
                                end
                         end;


(****************************************)
(* Reconstruct a paramodulation step    *)
(****************************************)

                          (* clause1, lit1 is thing to rewrite with *)
fun reconstruct_standard_para_left ((clause1, lit1), (clause2 , lit2)) thml (numlist, symlist, nsymlist )= 

                          let 
                             
                              val newthm = para_left ((clause1, lit1), (clause2 , lit2))  thml 
                              val symmed = (apply_rule sym  symlist newthm)
                              val nsymmed = (apply_rule not_sym nsymlist  symmed )
                                
                         in
                              rearrange_prems numlist nsymmed  
                         end



                        (* clause1, lit1 is thing to rewrite with *)
fun reconstruct_standard_para_right ((clause1, lit1), (clause2 , lit2)) thml (numlist, symlist, nsymlist )= 

                          let 
                             
                              val newthm = para_right ((clause1, lit1), (clause2 , lit2))  thml 
                              val symmed = (apply_rule sym  symlist newthm)
                              val nsymmed = (apply_rule not_sym nsymlist  symmed )
                                
                         in
                              rearrange_prems numlist nsymmed  
                         end








                        (*  let 
                            val th1 =  assoc clause1 thml
                            val th2 =  assoc clause2 thml 
                            val prems1 = prems_of th1
                            val prems2 = prems_of th2
                            (* want to get first element of equality *)

                            val fac1 = get_nth (lit1+1) prems1
                            val {lhs, rhs} = dest_eq(dest_Trueprop fac1)
                                             handle ERR _ => dest_eq(dest_neg (dest_Trueprop fac1))
                            (* get other literal involved in the paramodulation *)
                            val fac2 = get_nth (lit2+1) prems2

                           (* get bit of th2 to unify with lhs of th1 *)
                            val unif_lit = get_unif_lit (dest_Trueprop fac2) lhs
                            val unif_env = unifiers (Mainsign,myenv, [(unif_lit, lhs)])
                            val newenv = getnewenv unif_env
                            val envlist = alist_of newenv
                            val newsubsts = mksubstlist envlist []
                           (* instantiate th2 with unifiers *)
                          
                            val newth1 =  
                              if (is_Var (fst(hd(newsubsts))))
                              then
                                  let 
                                     val str1 = lit_string_with_nums (fst (hd newsubsts));
                                     val str2 = lit_string_with_nums (snd (hd newsubsts));
                                     val facthm = read_instantiate [(str1,str2)] th1
                                  in 
                                     hd (Seq.list_of(distinct_subgoals_tac facthm))
                                  end
                              else
                                  let
                                     val str2 = lit_string_with_nums (fst (hd newsubsts));
                                     val str1 = lit_string_with_nums  (snd (hd newsubsts));
                                     val facthm = read_instantiate [(str1,str2)] th1
                                  in 
                                     hd (Seq.list_of(distinct_subgoals_tac facthm))
                                  end
                           (*rewrite th2 with the equality bit of th2 i.e. lit2 *)
                              val facthm' = select_literal  (lit1 + 1) newth1
                              val equal_lit = concl_of facthm'
                              val cterm_eq = cterm_of Mainsign equal_lit  
                              val eq_thm = assume cterm_eq
                              val meta_eq_thm = mk_meta_eq eq_thm
                              val newth2= rewrite_rule [meta_eq_thm] th2
                           (*thin lit2 from th2 *)
                           (* get th1 with lit one as concl, then resolve with thin_rl *)
                              val thm' = facthm' RS thin_rl
                           (* now resolve th2 with last premise of thm' *)
                              val newthm = newth2  RSN ((length prems1), thm')
                              val symmed = (apply_rule sym  symlist newthm)
                              val nsymmed = (apply_rule not_sym nsymlist  symmed )
                                
                         in
                              rearrange_prems numlist nsymmed  
                         end

*)


(********************************************)
(* Reconstruct a rewrite step               *)
(********************************************)






(* does rewriting involve every literal in rewritten clause? *)
                    (* clause1, lit1 is thing to rewrite with *)

fun reconstruct_rewrite (clause1, lit1, clause2) thml  (numlist, symlist, nsymlist )=

                          let val th1 =  assoc clause1 thml
                              val th2 =  assoc clause2 thml 
                              val eq_lit_th = select_literal (lit1+1) th1
                              val equal_lit = concl_of eq_lit_th
                              val cterm_eq = cterm_of Mainsign  equal_lit 
                              val eq_thm = assume cterm_eq
                              val meta_eq_thm = mk_meta_eq eq_thm
                              val newth2= rewrite_rule [meta_eq_thm] th2
                             val symmed = (apply_rule sym  symlist newth2)
                              val nsymmed = (apply_rule not_sym nsymlist  symmed )
                                
                           in
                              rearrange_prems numlist nsymmed  
                           end



(*****************************************)
(* Reconstruct an obvious reduction step *)
(*****************************************)


fun reconstruct_obvious  (clause1, lit1)  allvars thml clause_strs= 
                           let val th1 =  assoc clause1 thml
                               val prems1 = prems_of th1
                               val newthm = refl RSN ((lit1+ 1), th1)
                                               handle THM _ =>  hd (Seq.list_of(delete_assump_tac  th1 (lit1 + 1)))
                               val symmed = (apply_rule sym  symlist newthm)
                               val nsymmed = (apply_rule not_sym nsymlist  symmed )
                           in 
                               rearrange_prems numlist nsymmed  
                           end



(********************************************************************************************)
(* reconstruct a single step of the res. proof - depending on what sort of proof step it was*)
(********************************************************************************************)


 fun reconstruct_proof clauses clausenum thml  Axiom (numlist, symlist, nsymlist)
        = reconstruct_axiom clauses clausenum thml  (numlist, symlist, nsymlist)
      | reconstruct_proof clauses clausenum  thml (Binary (a, b)) (numlist, symlist, nsymlist)
        = reconstruct_binary (a, b) thml (numlist, symlist, nsymlist)
       | reconstruct_proof clauses clausenum  thml (MRR (a, b)) (numlist, symlist, nsymlist)
        = reconstruct_mrr (a, b) thml (numlist, symlist, nsymlist)
      | reconstruct_proof clauses clausenum  thml (Factor (a, b, c)) (numlist, symlist, nsymlist)
         = reconstruct_factor (a ,b ,c) thml (numlist, symlist, nsymlist)
      | reconstruct_proof clauses clausenum  thml (Para (a, b)) (numlist, symlist, nsymlist)
        = reconstruct_standard_para (a, b) thml (numlist, symlist, nsymlist)
      | reconstruct_proof clauses clausenum thml (Rewrite (a,b,c)) (numlist, symlist, nsymlist)
        = reconstruct_rewrite (a,b,c) thml (numlist, symlist, nsymlist)
      | reconstruct_proof clauses clausenum thml (Obvious (a,b)) (numlist, symlist, nsymlist)
        = reconstruct_obvious (a,b) thml (numlist, symlist, nsymlist)
      (*| reconstruct_proof clauses  clausenum thml (Hyper l)
        = reconstruct_hyper l thml*)
      | reconstruct_proof clauses clausenum  thml _ _ =
          raise ASSERTION  "proof step not implemented"


(********************************************************************************************)
(* reconstruct a single line of the res. proof - at the moment do only inference steps      *)
(********************************************************************************************)

    fun reconstruct_line clauses thml (clause_num, (proof_step, numlist, symlist,nsymlist))
        = let
            val thm = reconstruct_proof clauses clause_num thml proof_step (numlist, symlist,nsymlist)
            
          in
            (clause_num, thm)::thml
          end

(********************************************************************)
(* reconstruct through the res. proof, creating an Isabelle theorem *)
(********************************************************************)


fun reconstruct clauses [] thml  = ((snd( hd thml)))
      | reconstruct clauses (h::t) thml  
        = let
            val (thml') = reconstruct_line clauses thml h 
            val  (thm) = reconstruct clauses t thml' 
          in
             (thm)
          end


(* Assume we have the cnf clauses as a list of (clauseno, clause) *)
 (* and the proof as a list of the proper datatype *)
(* take the cnf clauses of the goal and the proof from the res. prover *)
(* as a list of type Proofstep and return the thm goal ==> False *)

fun first_pair (a,b,c) = (a,b);

fun second_pair (a,b,c) = (b,c);

fun one_of_three (a,b,c) = a;
fun two_of_three (a,b,c) = b;
fun three_of_three (a,b,c) = c;

(*************************)
(* reconstruct res proof *)
(*************************)

fun reconstruct_proof clauses proof
        = let val thm = reconstruct clauses proof [] 
          in
             thm
          end
  
