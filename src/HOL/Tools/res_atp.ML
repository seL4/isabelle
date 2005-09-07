(*  Author: Jia Meng, Cambridge University Computer Laboratory
    ID: $Id$
    Copyright 2004 University of Cambridge

ATPs with TPTP format input.
*)

signature RES_ATP =
sig
  val axiom_file : Path.T
  val prover: string ref
  val custom_spass: string list ref
  val hook_count: int ref
end;

structure ResAtp: RES_ATP =
struct


val call_atp = ref false;
val hook_count = ref 0;

fun debug_tac tac = (debug "testing"; tac);

val prover = ref "spass";   (* use spass as default prover *)
val custom_spass =   (*specialized options for SPASS*)
      ref ["Auto=0","-IORe","-IOFc","-RTaut","-RFSub","-RBSub",
           "-DocProof","-TimeLimit=60"];

val axiom_file = File.tmp_path (Path.basic "axioms");
val hyps_file = File.tmp_path (Path.basic "hyps");
val prob_file = File.tmp_path (Path.basic "prob");


(**** for Isabelle/ML interface  ****)

(*Remove unwanted characters such as ? and newline from the textural 
  representation of a theorem (surely they don't need to be produced in 
  the first place?) *)

fun is_proof_char ch = (#" " <= ch andalso ch <= #"~" andalso ch <> #"?");

val proofstring =
    String.translate (fn c => if is_proof_char c then str c else "");


(**** For running in Isar ****)

(* same function as that in res_axioms.ML *)
fun repeat_RS thm1 thm2 =
    let val thm1' =  thm1 RS thm2 handle THM _ => thm1
    in
        if eq_thm(thm1,thm1') then thm1' else (repeat_RS thm1' thm2)
    end;

(* a special version of repeat_RS *)
fun repeat_someI_ex thm = repeat_RS thm someI_ex;


(*********************************************************************)
(* convert clauses from "assume" to conjecture. write to file "hyps" *)
(* hypotheses of the goal currently being proved                     *)
(*********************************************************************)
(*perhaps have 2 different versions of this, depending on whether or not spass is set *)
fun isar_atp_h thms =
    let val prems = map (skolemize o make_nnf o ObjectLogic.atomize_thm) thms
        val prems' = map repeat_someI_ex prems
        val prems'' = make_clauses prems'
        val prems''' = ResAxioms.rm_Eps [] prems''
        val clss = map ResClause.make_conjecture_clause prems'''
	val (tptp_clss,tfree_litss) = ListPair.unzip (map ResClause.clause2tptp clss) 
	val tfree_lits = ResLib.flat_noDup tfree_litss
        (* tfree clause is different in tptp and dfg versions *)
	val tfree_clss = map ResClause.tfree_clause tfree_lits 
        val hypsfile = File.platform_path hyps_file
        val out = TextIO.openOut(hypsfile)
    in
        ResLib.writeln_strs out (tfree_clss @ tptp_clss);
        TextIO.closeOut out; debug hypsfile;
        tfree_lits
    end;


(*********************************************************************)
(* write out a subgoal as tptp clauses to the file "probN"           *)
(* where N is the number of this subgoal                             *)
(*********************************************************************)

fun tptp_inputs_tfrees thms n tfrees axclauses =
    let
      val _ = debug ("in tptp_inputs_tfrees 0")
      val clss = map (ResClause.make_conjecture_clause_thm) thms
      val _ = debug ("in tptp_inputs_tfrees 1")
      val (tptp_clss,tfree_litss) = ListPair.unzip (map ResClause.clause2tptp clss)
      val _ = debug ("in tptp_inputs_tfrees 2")
      val tfree_clss = map ResClause.tfree_clause ((ResLib.flat_noDup tfree_litss) \\ tfrees)
      val _ = debug ("in tptp_inputs_tfrees 3")
      val probfile = File.platform_path prob_file ^ "_" ^ string_of_int n
      val out = TextIO.openOut(probfile)
    in
      ResLib.writeln_strs out (List.concat (map ResClause.tptp_clause axclauses));
      ResLib.writeln_strs out (tfree_clss @ tptp_clss);
      TextIO.closeOut out;
      debug probfile
    end;


(*********************************************************************)
(* write out a subgoal as DFG clauses to the file "probN"           *)
(* where N is the number of this subgoal                             *)
(*********************************************************************)

fun dfg_inputs_tfrees thms n tfrees axclauses = 
    let val clss = map (ResClause.make_conjecture_clause_thm) thms
        val probfile = (File.platform_path prob_file) ^ "_" ^ (string_of_int n)
        val _ = debug ("about to write out dfg prob file " ^ probfile)
       	(*val (dfg_clss,tfree_litss) = ListPair.unzip (map ResClause.clause2dfg clss)
        val tfree_clss = map ResClause.tfree_dfg_clause ((ResLib.flat_noDup tfree_litss) \\ tfrees) *)   
        val probN = ResClause.clauses2dfg clss ("prob" ^ (string_of_int n)) 
                        axclauses [] [] [] tfrees   
	val out = TextIO.openOut(probfile)
    in
	(ResLib.writeln_strs out [probN]; TextIO.closeOut out; debug probfile )
(* (ResLib.writeln_strs out (tfree_clss @ dfg_clss); *)
    end;


(*********************************************************************)
(* call prover with settings and problem file for the current subgoal *)
(*********************************************************************)
(* now passing in list of skolemized thms and list of sgterms to go with them *)
fun call_resolve_tac  (thms: thm list list)  sign (sg_terms:  term list) (childin, childout,pid) n  =
  let
    val axfile = (File.platform_path axiom_file)

    val hypsfile = (File.platform_path hyps_file)

    fun make_atp_list [] sign n = []
      | make_atp_list ((sko_thm, sg_term)::xs) sign n =
          let
            val thmstr = proofstring (Meson.concat_with_and (map string_of_thm sko_thm))
            val _ = debug ("thmstring in make_atp_lists is " ^ thmstr)

            val goalstring = proofstring (Sign.string_of_term sign sg_term)
            val _ = debug ("goalstring in make_atp_lists is " ^ goalstring)

            val probfile = File.platform_path prob_file ^ "_" ^ (string_of_int n)
            val _ = debug ("prob file in call_resolve_tac is " ^ probfile)
          in
            if !prover = "spass"
            then
              let val optionline = 
		      if !SpassComm.reconstruct 
		          (*Proof reconstruction works for only a limited set of 
		            inference rules*)
                      then "-" ^ space_implode "%-" (!custom_spass)
                      else "-DocProof%-TimeLimit=60%-SOS" (*Auto mode*)
                  val _ = debug ("SPASS option string is " ^ optionline)
                  val _ = ResLib.helper_path "SPASS_HOME" "SPASS"
                    (*We've checked that SPASS is there for ATP/spassshell to run.*)
              in 
                  ([("spass", thmstr, goalstring,
                     getenv "ISABELLE_HOME" ^ "/src/HOL/Tools/ATP/spassshell",
                     optionline, axfile, hypsfile, probfile)] @ 
                  (make_atp_list xs sign (n+1)))
              end
            else if !prover = "vampire"
	    then 
              let val vampire = ResLib.helper_path "VAMPIRE_HOME" "vkernel"
              in
                ([("vampire", thmstr, goalstring, vampire, "-t 60%-m 100000",
                   axfile, hypsfile, probfile)] @
                 (make_atp_list xs sign (n+1)))
              end
      	     else if !prover = "E"
      	     then
	       let val Eprover = ResLib.helper_path "E_HOME" "eproof"
	       in
		  ([("E", thmstr, goalstring, Eprover, 
		     "--tptp-in%-l5%-xAuto%-tAuto%--soft-cpu-limit=60",
		     axfile, hypsfile, probfile)] @
		   (make_atp_list xs sign (n+1)))
	       end
	     else error ("Invalid prover name: " ^ !prover)
          end

    val atp_list = make_atp_list (ListPair.zip (thms, sg_terms)) sign 1
  in
    Watcher.callResProvers(childout,atp_list);
    debug "Sent commands to watcher!";
    all_tac
  end

(**********************************************************)
(* write out the current subgoal as a tptp file, probN,   *)
(* then call all_tac - should be call_res_tac           *)
(**********************************************************)


fun get_sko_thms tfrees sign sg_terms (childin, childout,pid) thm n sko_thms axclauses =
    if n=0 then 
       (call_resolve_tac  (rev sko_thms)
        sign  sg_terms (childin, childout, pid) (List.length sg_terms);
        all_tac thm)
     else
	
      (SELECT_GOAL
        (EVERY1 [rtac ccontr, ResLib.atomize_tac, skolemize_tac, 
          METAHYPS(fn negs => 
            (if !prover = "spass" 
             then dfg_inputs_tfrees (make_clauses negs) n tfrees axclauses
             else tptp_inputs_tfrees (make_clauses negs) n tfrees axclauses;
             get_sko_thms tfrees sign sg_terms (childin, childout, pid) 
                          thm (n-1) (negs::sko_thms) axclauses; 
             all_tac))]) n thm)



(**********************************************)
(* recursively call atp_tac_g on all subgoals *)
(* sg_term is the nth subgoal as a term - used*)
(* in proof reconstruction                    *)
(**********************************************)

fun isar_atp_aux thms thm n_subgoals  (childin, childout, pid) axclauses =
  let val tfree_lits = isar_atp_h thms
      val prems = Thm.prems_of thm
      val sign = sign_of_thm thm
      val thmstring = string_of_thm thm
  in
    debug ("in isar_atp_aux");
    debug("thmstring in isar_atp_goal': " ^ thmstring);
    (* go and call callResProvers with this subgoal *)
    (* isar_atp_g tfree_lits  sg_term (childin, childout, pid) k thm; *)
    (* recursive call to pick up the remaining subgoals *)
    (* isar_atp_goal' thm (k+1) n tfree_lits  (childin, childout, pid) *)
    get_sko_thms tfree_lits sign prems (childin, childout, pid) 
                 thm n_subgoals []  axclauses
  end;

(******************************************************************)
(* called in Isar automatically                                   *)
(* writes out the current clasimpset to a tptp file               *)
(* passes all subgoals on to isar_atp_aux for further processing  *)
(* turns off xsymbol at start of function, restoring it at end    *)
(******************************************************************)
(*FIX changed to clasimp_file *)
val isar_atp' = setmp print_mode [] (fn (ctxt, thms, thm) =>
  if Thm.no_prems thm then ()
  else
    let
      val _= debug ("in isar_atp'")
      val thy = ProofContext.theory_of ctxt
      val prems = Thm.prems_of thm
      val thms_string = Meson.concat_with_and (map string_of_thm thms)
      val prems_string = Meson.concat_with_and (map (Sign.string_of_term thy) prems)

      (*set up variables for writing out the clasimps to a tptp file*)
      val (clause_arr, num_of_clauses, axclauses) =
        ResClasimp.get_clasimp_lemmas thy (hd prems) (*FIXME: hack!! need to do all prems*)
      val _ = debug ("claset and simprules total " ^ (string_of_int num_of_clauses)^ " clauses")
      val (childin, childout, pid) = Watcher.createWatcher (thm, clause_arr, num_of_clauses)
      val pid_string =
        string_of_int (Word.toInt (Word.fromLargeWord (Posix.Process.pidToWord pid)))
    in
      debug ("initial thms: " ^ thms_string);
      debug ("subgoals: " ^ prems_string);
      debug ("pid: "^ pid_string);
      isar_atp_aux thms thm (length prems) (childin, childout, pid) axclauses;
      ()
    end);


fun get_thms_cs claset =
  let val {safeEs, safeIs, hazEs, hazIs, ...} = rep_cs claset
  in safeEs @ safeIs @ hazEs @ hazIs end;

fun append_name name [] _ = []
  | append_name name (thm :: thms) k =
      Thm.name_thm ((name ^ "_" ^ string_of_int k), thm) :: append_name name thms (k + 1);

fun append_names (name :: names) (thms :: thmss) =
  append_name name thms 0 :: append_names names thmss;

fun get_thms_ss [] = []
  | get_thms_ss thms =
      let
        val names = map Thm.name_of_thm thms
        val thms' = map (mksimps mksimps_pairs) thms
        val thms'' = append_names names thms'
      in
        ResLib.flat_noDup thms''
      end;


(* convert locally declared rules to axiom clauses *)

fun subtract_simpset thy ctxt =
  let
    val rules1 = #rules (#1 (rep_ss (simpset_of thy)));
    val rules2 = #rules (#1 (rep_ss (local_simpset_of ctxt)));
  in map #thm (Net.subtract MetaSimplifier.eq_rrule rules1 rules2) end;

fun subtract_claset thy ctxt =
  let
    val (netI1, netE1) = #xtra_netpair (rep_cs (claset_of thy));
    val (netI2, netE2) = #xtra_netpair (rep_cs (local_claset_of ctxt));
    val subtract = map (#2 o #2) oo Net.subtract Tactic.eq_kbrl;
  in subtract netI1 netI2 @ subtract netE1 netE2 end;



(** the Isar toplevel hook **)

val invoke_atp = Toplevel.unknown_proof o Toplevel.keep (fn state =>
  let
    val proof = Toplevel.proof_of state
    val (ctxt, (_, goal)) = Proof.get_goal proof
        handle Proof.STATE _ => error "No goal present";

    val thy = ProofContext.theory_of ctxt;

    (* FIXME presently unused *)
    val ss_thms = subtract_simpset thy ctxt;
    val cs_thms = subtract_claset thy ctxt;
  in
    debug ("initial thm in isar_atp: " ^ 
           Pretty.string_of (ProofContext.pretty_thm ctxt goal));
    debug ("subgoals in isar_atp: " ^ 
           Pretty.string_of (ProofContext.pretty_term ctxt
             (Logic.mk_conjunction_list (Thm.prems_of goal))));
    debug ("number of subgoals in isar_atp: " ^ string_of_int (Thm.nprems_of goal));
    hook_count := !hook_count +1;
    debug ("in hook for time: " ^(string_of_int (!hook_count)) );
    ResClause.init thy;
    isar_atp' (ctxt, ProofContext.prems_of ctxt, goal)
  end);

val call_atpP =
  OuterSyntax.improper_command 
    "ProofGeneral.call_atp" 
    "call automatic theorem provers" 
    OuterKeyword.diag
    (Scan.succeed (Toplevel.no_timing o invoke_atp));

val _ = OuterSyntax.add_parsers [call_atpP];

end;
