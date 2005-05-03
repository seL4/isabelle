(*  ID:         $Id$
    Author:     Claire Quigley
    Copyright   2004  University of Cambridge
*)

fun add_in_order (x:string) [] = [x]
|   add_in_order (x:string) ((y:string)::ys) = if (x < y) 
                             then 
                                  (x::(y::ys))
                             else
                                  (y::(add_in_order x ys))
fun add_once x [] = [x]
|   add_once x (y::ys) = if (inlist x (y::ys)) then 
                            (y::ys)
                        else
                            add_in_order x (y::ys)
     
fun thm_vars thm = map (fn ((name,ix),_) => name) (Drule.vars_of thm);

Goal "False ==> False";
by Auto_tac;
qed "False_imp";

exception Reflex_equal;

(********************************)
(* Proofstep datatype           *)
(********************************)
(* Assume rewrite steps have only two clauses in them just now, but lcl109-5 has Rew[5,3,5,3]  *)

datatype Side = Left |Right

 datatype Proofstep = ExtraAxiom
                     |OrigAxiom
                     | Axiom
                     | Binary of (int * int) * (int * int)   (* (clause1,lit1), (clause2, lit2) *)
                     | MRR of (int * int) * (int * int) 
                     | Factor of (int * int * int)           (* (clause,lit1, lit2) *)
                     | Para of (int * int) * (int * int) 
                     | Rewrite of (int * int) * (int * int)  
                     | Obvious of (int * int)
                     (*| Hyper of int list*)
                     | Unusedstep of unit


datatype Clausesimp = Binary_s of int * int
                      | Factor_s of unit
                      | Demod_s of (int * int) list
                      | Hyper_s of int list
                      | Unusedstep_s of unit



datatype Step_label = T_info
                     |P_info


fun is_alpha_space_digit_or_neg ch = (ch = "~") orelse (is_alpha ch) orelse (is_digit ch) orelse ( ch = " ")



fun lit_string_with_nums t = let val termstr = Term.string_of_term t
                                 val exp_term = explode termstr
                             in
                                 implode(List.filter is_alpha_space_digit_or_neg exp_term)
                             end

fun reconstruction_failed fname = error (fname ^ ": reconstruction failed")

(************************************************)
(* Reconstruct an axiom resolution step         *)
(* clauses is a list of (clausenum,clause) pairs*)
(************************************************)

fun follow_axiom clauses  allvars (clausenum:int) thml clause_strs =  
                                     let val this_axiom = valOf (assoc (clauses,clausenum))
                                         val (res, numlist, symlist, nsymlist) = (rearrange_clause this_axiom clause_strs allvars)         
                                         val thmvars = thm_vars res
                                     in
                                         (res, (Axiom,clause_strs,thmvars )  )
                                     end
                                     handle Option => reconstruction_failed "follow_axiom"

(****************************************)
(* Reconstruct a binary resolution step *)
(****************************************)

                 (* numbers of clauses and literals*) (*vars*) (*list of current thms*) (* literal strings as parsed from spass *)
fun follow_binary ((clause1, lit1), (clause2 , lit2)) allvars thml clause_strs 
        = let
              val thm1 =  select_literal (lit1 + 1) (valOf (assoc (thml,clause1)))
              val thm2 =  valOf (assoc (thml,clause2))
              val res =   thm1 RSN ((lit2 +1), thm2)
              val (res', numlist, symlist, nsymlist) = (rearrange_clause res clause_strs allvars)
              val thmvars = thm_vars res
          in
             (res',  ((Binary ((clause1, lit1), (clause2 , lit2))),clause_strs,thmvars) )
          end
	  handle Option => reconstruction_failed "follow_binary"



(******************************************************)
(* Reconstruct a matching replacement resolution step *)
(******************************************************)


fun follow_mrr ((clause1, lit1), (clause2 , lit2))  allvars thml clause_strs 
        = let
              val thm1 =  select_literal (lit1 + 1) (valOf (assoc (thml,clause1)))
              val thm2 =  valOf (assoc (thml,clause2))
              val res =   thm1 RSN ((lit2 +1), thm2)
              val (res', numlist, symlist, nsymlist) = (rearrange_clause res clause_strs allvars)
              val thmvars = thm_vars res
          in
             (res',  ((MRR ((clause1, lit1), (clause2 , lit2))) ,clause_strs,thmvars))
          end
	  handle Option => reconstruction_failed "follow_mrr"


(*******************************************)
(* Reconstruct a factoring resolution step *)
(*******************************************)

fun mksubstlist [] sublist = sublist
   |mksubstlist ((a, (_, b)) :: rest) sublist = let val vartype = type_of b 
                                          val avar = Var(a,vartype)
                                          val newlist = ((avar,b)::sublist) in
                                          mksubstlist rest newlist
                                      end;

(* based on Tactic.distinct_subgoals_tac *)

fun delete_assump_tac state lit =
    let val (frozth,thawfn) = freeze_thaw state
        val froz_prems = cprems_of frozth
        val assumed = implies_elim_list frozth (map assume froz_prems)
        val new_prems = remove_nth lit froz_prems
        val implied = implies_intr_list new_prems assumed
    in  
        Seq.single (thawfn implied)  
    end





(*************************************)
(* Reconstruct a factoring step      *)
(*************************************)

(*FIXME: share code with that in Tools/reconstruction.ML*)
fun follow_factor clause lit1 lit2 allvars thml clause_strs= 
                          let 
                            val th =  valOf (assoc (thml,clause))
                            val prems = prems_of th
                            val sign = sign_of_thm th
                            val fac1 = get_nth (lit1+1) prems
                            val fac2 = get_nth (lit2+1) prems
                            val unif_env = Unify.unifiers (sign,Envir.empty 0, [(fac1, fac2)])
                            val newenv = getnewenv unif_env
                            val envlist = Envir.alist_of newenv
                            
                            val (t1,t2)::_ = mksubstlist envlist []
                          in 
                            if (is_Var t1)
                            then
                                let 
                                   val str1 = lit_string_with_nums t1;
                                   val str2 = lit_string_with_nums t2;
                                   val facthm = read_instantiate [(str1,str2)] th;
                                   val res = hd (Seq.list_of(delete_assump_tac  facthm (lit1 + 1)))
                                   val (res', numlist, symlist, nsymlist) = (rearrange_clause res clause_strs allvars)
                                   val thmvars = thm_vars res'
                                in 
                                       (res',((Factor (clause,  lit1, lit2)),clause_strs,thmvars))
                                end
                            else
                                let
                                   val str2 = lit_string_with_nums t1;
                                   val str1 = lit_string_with_nums t2;
                                   val facthm = read_instantiate [(str1,str2)] th;
                                   val res = hd (Seq.list_of(delete_assump_tac  facthm (lit1 + 1)))
                                   val (res', numlist, symlist, nsymlist) = (rearrange_clause res clause_strs allvars)
                                  val thmvars = thm_vars res'
                                in 
                                       (res', ((Factor (clause,  lit1, lit2)),clause_strs, thmvars))         
                                end
                         end
                         handle Option => reconstruction_failed "follow_factor"



fun get_unif_comb t eqterm =
    if ((type_of t) = (type_of eqterm))
    then t
    else
        let val _ $ rand = t
        in get_unif_comb rand eqterm end;

fun get_unif_lit t eqterm =
    if (can HOLogic.dest_eq t)
    then
	let val (lhs,rhs) = HOLogic.dest_eq(HOLogic.dest_Trueprop eqterm)
	in lhs end
    else
	get_unif_comb t eqterm;



(*************************************)
(* Reconstruct a paramodulation step *)
(*************************************)

val rev_subst = rotate_prems 1 subst;
val rev_ssubst = rotate_prems 1 ssubst;


fun follow_standard_para ((clause1, lit1), (clause2 , lit2)) allvars thml clause_strs= 
                          let 
                            val th1 =  valOf (assoc (thml,clause1))
                            val th2 =  valOf (assoc (thml,clause2)) 
                            val eq_lit_th = select_literal (lit1+1) th1
                            val mod_lit_th = select_literal (lit2+1) th2
                            val eqsubst = eq_lit_th RSN (2,rev_subst)
                            val newth = Seq.hd (biresolution false [(false, mod_lit_th)] 1 eqsubst)
			    val newth' =negate_head newth 
                            val (res, numlist, symlist, nsymlist)  = (rearrange_clause newth' clause_strs allvars 
                                handle Not_in_list => let 
                                                  val mod_lit_th' = mod_lit_th RS not_sym
                                                   val newth = Seq.hd (biresolution false [(false, mod_lit_th')] 1 eqsubst)
			                           val newth' =negate_head newth 
                                               in 
                                                  (rearrange_clause newth' clause_strs allvars)
                                               end)
                            val thmvars = thm_vars res
                         in 
                           (res, ((Para((clause1, lit1), (clause2 , lit2))),clause_strs,thmvars))
                         end
			 handle Option => reconstruction_failed "follow_standard_para"

(*              
fun follow_standard_para ((clause1, lit1), (clause2 , lit2)) allvars thml clause_strs= 
                          let 
                            val th1 =  valOf (assoc (thml,clause1))
                            val th2 =  valOf (assoc (thml,clause2)) 
                            val eq_lit_th = select_literal (lit1+1) th1
                            val mod_lit_th = select_literal (lit2+1) th2
                            val eqsubst = eq_lit_th RSN (2,rev_subst)
                            val newth = Seq.hd (biresolution false [(false, mod_lit_th)] 1 eqsubst)
			    val newth' =negate_nead newth 
                            val (res, numlist, symlist, nsymlist)  = (rearrange_clause newth' clause_strs allvars)
                            val thmvars = thm_vars res
                         in 
                           (res, ((Para((clause1, lit1), (clause2 , lit2))),clause_strs,thmvars))
                         end
			 handle Option => reconstruction_failed "follow_standard_para"

*)


(********************************)
(* Reconstruct a rewriting step *)
(********************************)
 
(*

val rev_subst = rotate_prems 1 subst;

fun paramod_rule ((cl1, lit1), (cl2 , lit2)) =
     let  val eq_lit_th = select_literal (lit1+1) cl1
          val mod_lit_th = select_literal (lit2+1) cl2
          val eqsubst = eq_lit_th RSN (2,rev_subst)
          val newth = Seq.hd (biresolution false [(false, mod_lit_th)] 1 
eqsubst)
     in Meson.negated_asm_of_head newth end;

val newth = Seq.hd (biresolution false [(false, mod_lit_th)] 1 
eqsubst)

val mod_lit_th' = mod_lit_th RS not_sym

*)


fun delete_assumps 0 th = th 
|   delete_assumps n th = let val th_prems = length (prems_of th)
                              val th' = hd (Seq.list_of(delete_assump_tac  th (th_prems -1)))
                          in
                              delete_assumps (n-1) th'
                          end

(* extra conditions from the equality turn up as 2nd to last literals of result.  Need to delete them *)
(* changed negate_nead to negate_head here too*)
                    (* clause1, lit1 is thing to rewrite with *)
fun follow_rewrite ((clause1, lit1), (clause2, lit2)) allvars thml clause_strs= 

                          let val th1 =  valOf (assoc (thml,clause1))
                              val th2 = valOf (assoc (thml,clause2))
                              val eq_lit_th = select_literal (lit1+1) th1
                              val mod_lit_th = select_literal (lit2+1) th2
                              val eqsubst = eq_lit_th RSN (2,rev_subst)
                              val eq_lit_prem_num = length (prems_of eq_lit_th)
                              val sign = Sign.merge (sign_of_thm th1, sign_of_thm th2)
                              val newth = Seq.hd (biresolution false [(false, mod_lit_th)] 1 
eqsubst)
                         
                              val newthm = negate_head newth
                              val newthm' = delete_assumps eq_lit_prem_num newthm
                              val (res, numlist, symlist, nsymlist) =(rearrange_clause newthm clause_strs allvars)
                              val thmvars = thm_vars res
                           in
                               (res, ((Rewrite ((clause1, lit1),  (clause2, lit2))),clause_strs,thmvars))
                           end
			   handle Option => reconstruction_failed "follow_rewrite"



(*****************************************)
(* Reconstruct an obvious reduction step *)
(*****************************************)


fun follow_obvious  (clause1, lit1)  allvars thml clause_strs= 
                           let val th1 =  valOf (assoc (thml,clause1))
                               val prems1 = prems_of th1
                               val newthm = refl RSN ((lit1+ 1), th1)
                                               handle THM _ =>  hd (Seq.list_of(delete_assump_tac  th1 (lit1 + 1)))
                               val (res, numlist, symlist, nsymlist) =(rearrange_clause newthm clause_strs allvars)
                               val thmvars = thm_vars res
                           in 
                               (res, ((Obvious (clause1, lit1)),clause_strs,thmvars))
                           end
  	 		   handle Option => reconstruction_failed "follow_obvious"

(**************************************************************************************)
(* reconstruct a single line of the res. proof - depending on what sort of proof step it was*)
(**************************************************************************************)

 fun follow_proof clauses allvars  clausenum thml  (Axiom ) clause_strs
        = follow_axiom clauses allvars  clausenum thml clause_strs

      | follow_proof clauses  allvars clausenum  thml (Binary (a, b)) clause_strs
        = follow_binary  (a, b)  allvars thml clause_strs

      | follow_proof clauses  allvars clausenum  thml (MRR (a, b)) clause_strs
        = follow_mrr (a, b)  allvars thml clause_strs

      | follow_proof clauses  allvars clausenum  thml (Factor (a, b, c)) clause_strs
         = follow_factor a b c  allvars thml clause_strs

      | follow_proof clauses  allvars clausenum  thml (Para (a, b)) clause_strs
        = follow_standard_para (a, b) allvars  thml clause_strs

      | follow_proof clauses  allvars clausenum thml (Rewrite (a,b)) clause_strs
        = follow_rewrite (a,b)  allvars thml clause_strs

      | follow_proof clauses  allvars clausenum thml (Obvious (a,b)) clause_strs
        = follow_obvious (a,b)  allvars thml clause_strs

      (*| follow_proof clauses  clausenum thml (Hyper l)
        = follow_hyper l thml*)
      | follow_proof clauses  allvars clausenum  thml _ _ =
          raise ASSERTION  "proof step not implemented"



 
(**************************************************************************************)
(* reconstruct a single line of the res. proof - at the moment do only inference steps*)
(**************************************************************************************)

    fun follow_line clauses  allvars thml (clause_num, proof_step, clause_strs) recons
        = let
            val (thm, recon_fun) = follow_proof clauses  allvars clause_num thml proof_step clause_strs 
            val recon_step = (recon_fun)
          in
            (((clause_num, thm)::thml), ((clause_num,recon_step)::recons))
          end

(***************************************************************)
(* follow through the res. proof, creating an Isabelle theorem *)
(***************************************************************)



(*fun is_proof_char ch = (case ch of 
                       
                        "(" => true
                       |  ")" => true
                         | ":" => true
                        |  "'" => true
                        |  "&" => true
                        | "|" => true
                        | "~" => true
                        |  "." => true
                        |(is_alpha ) => true
                       |(is_digit) => true
                         | _ => false)*)

fun is_proof_char ch = ((33 <= (ord ch)) andalso ((ord ch ) <= 126)) orelse (ch = " ")

fun proofstring x = let val exp = explode x 
                    in
                        List.filter (is_proof_char ) exp
                    end


fun not_newline ch = not (ch = "\n");

(*

fun follow clauses [] allvars thml recons = 
                             let (* val _ = reset show_sorts*)
                              val thmstring = Meson.concat_with_and (map string_of_thm (map snd thml))
                              val thmproofstring = proofstring ( thmstring)
                            val no_returns =List.filter  not_newline ( thmproofstring)
                            val thmstr = implode no_returns
                               val outfile = TextIO.openOut(File.sysify_path(File.tmp_path (Path.basic "thml_file")))
                               val _ = TextIO.output(outfile, "thmstr is "^thmstr)
                               val _ = TextIO.flushOut outfile;
                               val _ =  TextIO.closeOut outfile
                                 (*val _ = set show_sorts*)
                             in
                                  ((snd( hd thml)), recons)
                             end
      | follow clauses (h::t) allvars thml recons 
        = let
            val (thml', recons') = follow_line clauses allvars  thml h recons
            val  (thm, recons_list) = follow clauses t  allvars thml' recons'
            

          in
             (thm,recons_list)
          end

*)

fun replace_clause_strs [] recons newrecons= (newrecons)
|   replace_clause_strs ((thmnum, thm)::thml)  ((clausenum,(step,clause_strs,thmvars))::recons) newrecons = 
                           let val new_clause_strs = get_meta_lits_bracket thm
                           in
                               replace_clause_strs thml recons ((clausenum,(step,new_clause_strs,thmvars))::newrecons)
                           end


fun follow clauses [] allvars thml recons = 
                             let 
                                 val new_recons = replace_clause_strs thml recons []
                             in
                                  ((snd( hd thml)), new_recons)
                             end

 |  follow clauses (h::t) allvars thml recons 
        = let
            val (thml', recons') = follow_line clauses allvars  thml h recons
            val  (thm, recons_list) = follow clauses t  allvars thml' recons'     
          in
             (thm,recons_list)
          end



(* Assume we have the cnf clauses as a list of (clauseno, clause) *)
 (* and the proof as a list of the proper datatype *)
(* take the cnf clauses of the goal and the proof from the res. prover *)
(* as a list of type Proofstep and return the thm goal ==> False *)

fun first_pair (a,b,c) = (a,b);

fun second_pair (a,b,c) = (b,c);

(* takes original axioms, proof_steps parsed from spass, variables *)

fun translate_proof clauses proof allvars
        = let val (thm, recons) = follow clauses proof allvars [] []
          in
             (thm, (recons))
          end
  


fun remove_tinfo [] = []
|   remove_tinfo ( (clausenum, step, T_info, newstrs)::xs) = (clausenum, step , newstrs)::(remove_tinfo xs)
