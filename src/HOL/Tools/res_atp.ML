(*  Author: Jia Meng, Cambridge University Computer Laboratory
    ID: $Id$
    Copyright 2004 University of Cambridge

ATPs with TPTP format input.
*)

(*Jia: changed: isar_atp now processes entire proof context.  fetch thms from delta simpset/claset*)
(*Claire: changed: added actual watcher calls *)


signature RES_ATP = 
sig
val trace_res : bool ref
val subgoals: Thm.thm list
val traceflag : bool ref
val axiom_file : Path.T
val hyps_file : Path.T
val isar_atp : ProofContext.context * Thm.thm -> unit
val prob_file : Path.T;
(*val atp_ax_tac : Thm.thm list -> int -> Tactical.tactic*)
(*val atp_tac : int -> Tactical.tactic*)
val debug: bool ref
val full_spass: bool ref
end;

structure ResAtp : RES_ATP =

struct

val subgoals = [];

val traceflag = ref true;
(* used for debug *)
val debug = ref false;

fun debug_tac tac = (warning "testing";tac);
(* default value is false *)
val full_spass = ref false;
val trace_res = ref false;

val skolem_tac = skolemize_tac;

val num_of_clauses = ref 0;
val clause_arr = Array.array(3500, ("empty", 0));


val atomize_tac =
    SUBGOAL
     (fn (prop,_) =>
	 let val ts = Logic.strip_assums_hyp prop
	 in EVERY1 
		[METAHYPS
		     (fn hyps => (cut_facts_tac (map (ObjectLogic.atomize_thm o forall_intr_vars) hyps) 1)),
	  REPEAT_DETERM_N (length ts) o (etac thin_rl)]
     end);

(* temporarily use these files, which will be loaded by Vampire *)
val file_id_num =ref 0;

fun new_prob_file () =  (file_id_num := (!file_id_num) + 1;"prob"^(string_of_int (!file_id_num)));


val axiom_file = File.tmp_path (Path.basic "axioms");
val clasimp_file = File.tmp_path (Path.basic "clasimp");
val hyps_file = File.tmp_path (Path.basic "hyps");
val prob_file = File.tmp_path (Path.basic "prob");
val dummy_tac = PRIMITIVE(fn thm => thm );

 
(**** for Isabelle/ML interface  ****)

fun is_proof_char ch = ((33 <= (ord ch)) andalso ((ord ch ) <= 126) andalso (not ((ord ch ) = 63))) orelse (ch = " ")

fun proofstring x = let val exp = explode x 
                    in
                        List.filter (is_proof_char ) exp
                    end



(*
fun call_atp_tac thms n = (tptp_inputs thms ; dummy_tac);

*)

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

fun isar_atp_h thms =
        
    let val prems = map (skolemize o make_nnf o ObjectLogic.atomize_thm) thms
        val prems' = map repeat_someI_ex prems
        val prems'' = make_clauses prems'
        val prems''' = ResAxioms.rm_Eps [] prems''
        val clss = map ResClause.make_conjecture_clause prems'''
	val (tptp_clss,tfree_litss) = ListPair.unzip (map ResClause.clause2tptp clss) 
	val tfree_lits = ResLib.flat_noDup tfree_litss
	val tfree_clss = map ResClause.tfree_clause tfree_lits 
        val hypsfile = File.platform_path hyps_file
	val out = TextIO.openOut(hypsfile)
    in
	((ResLib.writeln_strs out (tfree_clss @ tptp_clss); TextIO.closeOut out; if !trace_res then (warning hypsfile) else ());tfree_lits) 
    end;


(*********************************************************************)
(* write out a subgoal as tptp clauses to the file "probN"           *)
(* where N is the number of this subgoal                             *)
(*********************************************************************)

fun tptp_inputs_tfrees thms n tfrees = 
    let val _ = (warning ("in tptp_inputs_tfrees 0"))
        val clss = map (ResClause.make_conjecture_clause_thm) thms
         val _ = (warning ("in tptp_inputs_tfrees 1"))
	val (tptp_clss,tfree_litss) = ListPair.unzip (map ResClause.clause2tptp clss)
        val _ = (warning ("in tptp_inputs_tfrees 2"))
	val tfree_clss = map ResClause.tfree_clause ((ResLib.flat_noDup tfree_litss) \\ tfrees) 
         val _ = (warning ("in tptp_inputs_tfrees 3"))
        val probfile = (File.platform_path prob_file) ^ "_" ^ (string_of_int n)
	val out = TextIO.openOut(probfile)
    in
	(ResLib.writeln_strs out (tfree_clss @ tptp_clss); TextIO.closeOut out; (if !trace_res then (warning probfile) else ()))
    end;



(*********************************************************************)
(* call SPASS with settings and problem file for the current subgoal *)
(* should be modified to allow other provers to be called            *)
(*********************************************************************)
(* now passing in list of skolemized thms and list of sgterms to go with them *)
fun call_resolve_tac  (thms: Thm.thm list list)  sign (sg_terms:  Term.term list) (childin, childout,pid) n  = let
   val axfile = (File.platform_path axiom_file)
    val hypsfile = (File.platform_path hyps_file)
     val clasimpfile = (File.platform_path clasimp_file)
    val spass_home = getenv "SPASS_HOME"
     
fun make_atp_list [] sign n = []
|   make_atp_list ((sko_thm, sg_term)::xs) sign  n = 
let 
	val skothmstr = Meson.concat_with_and (map string_of_thm sko_thm) 
	val thmproofstr = proofstring ( skothmstr)
	val no_returns =List.filter   not_newline ( thmproofstr)
	val thmstr = implode no_returns
	val _ = warning ("thmstring in make_atp_lists is: "^thmstr)

	val sgstr = Sign.string_of_term sign sg_term 
	val goalproofstring = proofstring sgstr
	val no_returns =List.filter not_newline ( goalproofstring)
	val goalstring = implode no_returns
	val _ = warning ("goalstring in make_atp_lists is: "^goalstring)

	val probfile = (File.platform_path prob_file) ^ "_" ^ (string_of_int n)
	val _ = (warning ("prob file in cal_res_tac is: "^probfile))                                                                           
in
 	if !full_spass 
  	then
   		([("spass", thmstr, goalstring (*,spass_home*), 
	    	 getenv "ISABELLE_HOME" ^ "/src/HOL/Tools/ATP/spassshell"(*( getenv "SPASS_HOME")^"/SPASS"*),  
	     	"-DocProof%-TimeLimit=60", 
	     	clasimpfile, axfile, hypsfile, probfile)]@(make_atp_list xs sign (n+1)))
  	else	
   		([("spass", thmstr, goalstring (*,spass_home*), 
	     	getenv "ISABELLE_HOME" ^"/src/HOL/Tools/ATP/spassshell"(* (getenv "SPASS_HOME")^"/SPASS"*),  
	     	"-Auto=0%-ISRe%-ISFc%-RTaut%-RFSub%-RBSub%-DocProof%-TimeLimit=60", 
	     	clasimpfile, axfile, hypsfile, probfile)]@(make_atp_list xs sign (n+1)))
end

val thms_goals = ListPair.zip( thms, sg_terms) 
val atp_list = make_atp_list  thms_goals sign 1
in
	Watcher.callResProvers(childout,atp_list);
        warning("Sent commands to watcher!");
  	dummy_tac
 end
(*
  val axfile = (File.platform_path axiom_file)
    val hypsfile = (File.platform_path hyps_file)
     val clasimpfile = (File.platform_path  clasimp_file)
    val spass_home = getenv "SPASS_HOME"
 val probfile = (File.platform_path prob_file) ^ "_" ^ (string_of_int 1)
    
 val (clause_arr, num_of_clauses) = ResClasimp.write_out_clasimp_small (File.platform_path clasimp_file) ;
 val (childin,childout,pid) = Watcher.createWatcher(mp, clause_arr, num_of_clauses);
Watcher.callResProvers(childout, [("spass", "thmstring", "goalstr", spass_home,  "-DocProof", clasimpfile, axfile, hypsfile,probfile)]);

Watcher.callResProvers(childout, [("spass", "thmstring", "goalstr", "/homes/clq20/spassshell",  "", clasimpfile, axfile, hypsfile,probfile)]);


*)
(**********************************************************)
(* write out the current subgoal as a tptp file, probN,   *)
(* then call dummy_tac - should be call_res_tac           *)
(**********************************************************)


fun get_sko_thms tfrees sign sg_terms (childin, childout,pid)  thm n sko_thms  =
                       if (equal n 0) then 
				(call_resolve_tac  (rev sko_thms) sign  sg_terms (childin, childout, pid) (List.length sg_terms);dummy_tac thm)
			else
                           
               		( SELECT_GOAL
  				(EVERY1 [rtac ccontr,atomize_tac, skolemize_tac, 
  				 METAHYPS(fn negs => (tptp_inputs_tfrees (make_clauses negs) n tfrees;
                                                    get_sko_thms  tfrees sign sg_terms (childin, childout, pid) thm  (n -1) (negs::sko_thms);dummy_tac))]) n thm )



(**********************************************)
(* recursively call atp_tac_g on all subgoals *)
(* sg_term is the nth subgoal as a term - used*)
(* in proof reconstruction                    *)
(**********************************************)

fun isar_atp_goal' thm n tfree_lits  (childin, childout, pid) = 
                  
                           (let val  prems = prems_of thm 
                              (*val sg_term = get_nth k prems*)
                                val sign = sign_of_thm thm
                                val thmstring = string_of_thm thm
                            in   
                                 
                		(warning("in isar_atp_goal'"));
                                (warning("thmstring in isar_atp_goal': "^thmstring));
 				(* go and call callResProvers with this subgoal *)
 				(* isar_atp_g tfree_lits  sg_term (childin, childout, pid) k thm; *)
 				(* recursive call to pick up the remaining subgoals *)
                                (* isar_atp_goal' thm (k+1) n tfree_lits  (childin, childout, pid) *)
                                get_sko_thms tfree_lits sign  prems (childin, childout, pid) thm n []
                            end);

(*fun isar_atp_goal thm n_subgoals tfree_lits   (childin, childout, pid) = 
              (if (!debug) then warning (string_of_thm thm) 
               else (isar_atp_goal' thm n_subgoals tfree_lits  (childin, childout, pid) ));*)

(**************************************************)
(* convert clauses from "assume" to conjecture.   *)
(* i.e. apply make_clauses and then get tptp for  *)
(* any hypotheses in the goal produced by assume  *)
(* statements;                                    *)
(* write to file "hyps"                           *)
(**************************************************)


fun isar_atp_aux thms thm n_subgoals  (childin, childout, pid) = 
    let val tfree_lits = isar_atp_h thms 
    in
	(warning("in isar_atp_aux"));
         isar_atp_goal' thm n_subgoals tfree_lits   (childin, childout, pid)
    end;

(******************************************************************)
(* called in Isar automatically                                   *)
(* writes out the current clasimpset to a tptp file               *)
(* passes all subgoals on to isar_atp_aux for further processing  *)
(* turns off xsymbol at start of function, restoring it at end    *)
(******************************************************************)
(*FIX changed to clasimp_file *)
fun isar_atp' (ctxt,thms, thm) =
    let 
	val _=  (print_mode := (Library.gen_rems (op =) (! print_mode, ["xsymbols", "symbols"])))
        val _= (warning ("in isar_atp'"))
        val prems  = prems_of thm
        val sign = sign_of_thm thm
        val thms_string = Meson.concat_with_and (map string_of_thm thms) 
        val thmstring = string_of_thm thm
        val prems_string = Meson.concat_with_and (map (Sign.string_of_term sign) prems) 
        
	(* set up variables for writing out the clasimps to a tptp file *)
	val (clause_arr, num_of_clauses) =
	    ResClasimp.write_out_clasimp(*_small*) (File.platform_path clasimp_file) 
	                                 (ProofContext.theory_of ctxt)
        val _ = (warning ("clasimp_file is this: "^(File.platform_path clasimp_file)) )  

        (* cq: add write out clasimps to file *)
        (* cq:create watcher and pass to isar_atp_aux *)
        (* tracing *) 
        (*val tenth_ax = fst( Array.sub(clause_arr, 1))  
         val tenth_ax_thms = Recon_Transfer.memo_find_clause (tenth_ax, clause_tab)
         val clause_str = Meson.concat_with_and (map string_of_thm tenth_ax_thms)
         val _ = (warning ("tenth axiom in array is: "^tenth_ax))         
         val _ = (warning ("tenth axiom in table is: "^clause_str))         
                 
         val _ = (warning ("num_of_clauses is: "^(string_of_int (num_of_clauses))) )     
         *)             
        
        val (childin,childout,pid) = Watcher.createWatcher(thm,clause_arr, num_of_clauses)
        val pidstring = string_of_int(Word.toInt (Word.fromLargeWord ( Posix.Process.pidToWord pid )))
    in
	case prems of [] => () 
		    | _ => ((warning ("initial thms: "^thms_string)); 
                           (warning ("initial thm: "^thmstring));
                           (warning ("subgoals: "^prems_string));
                           (warning ("pid: "^ pidstring))); 
                            isar_atp_aux thms thm (length prems) (childin, childout, pid) ;
                           (warning("turning xsymbol back on!"));
                           print_mode := (["xsymbols", "symbols"] @ ! print_mode)
    end;




local

fun get_thms_cs claset =
    let val clsset = rep_cs claset
	val safeEs = #safeEs clsset
	val safeIs = #safeIs clsset
	val hazEs = #hazEs clsset
	val hazIs = #hazIs clsset
    in
	safeEs @ safeIs @ hazEs @ hazIs
    end;



fun append_name name [] _ = []
  | append_name name (thm::thms) k = (Thm.name_thm ((name ^ "_" ^ (string_of_int k)),thm)) :: (append_name name thms (k+1));

fun append_names (name::names) (thms::thmss) =
    let val thms' = append_name name thms 0
    in
	thms'::(append_names names thmss)
    end;


fun get_thms_ss [] = []
  | get_thms_ss thms =
    let val names = map Thm.name_of_thm thms 
        val thms' = map (mksimps mksimps_pairs) thms
        val thms'' = append_names names thms'
    in
	ResLib.flat_noDup thms''
    end;




in


(* convert locally declared rules to axiom clauses *)
(* write axiom clauses to ax_file *)
(* what about clasimpset - it should already be in the ax file - perhaps append to ax file rather than just *)
(* write out ? Or keep as a separate file and then cat them all together in the watcher, like we do with the *)
(*claset file and prob file*)
(* FIX*)
(*fun isar_local_thms (delta_cs, delta_ss_thms) =
    let val thms_cs = get_thms_cs delta_cs
	val thms_ss = get_thms_ss delta_ss_thms
	val thms_clauses = ResLib.flat_noDup (map ResAxioms.clausify_axiom (thms_cs @ thms_ss))
	val clauses_strs = ResLib.flat_noDup (map ResClause.tptp_clause thms_clauses) (*string list*)
	val ax_file = File.platform_path axiom_file
	val out = TextIO.openOut ax_file
    in
	(ResLib.writeln_strs out clauses_strs; (warning ("axiom file is: "^ax_file));TextIO.closeOut out)
    end;
*)




(* called in Isar automatically *)

fun isar_atp (ctxt,thm) =
    let val prems = ProofContext.prems_of ctxt
        val d_cs = Classical.get_delta_claset ctxt 
        val d_ss_thms = Simplifier.get_delta_simpset ctxt
        val thmstring = string_of_thm thm
        val sg_prems = prems_of thm
        val sign = sign_of_thm thm
        val prem_no = length sg_prems
        val prems_string = Meson.concat_with_and (map (Sign.string_of_term sign) sg_prems) 
    in
          (warning ("initial thm in isar_atp: "^thmstring));
          (warning ("subgoals in isar_atp: "^prems_string));
    	  (warning ("number of subgoals in isar_atp: "^(string_of_int prem_no)));
          (*isar_local_thms (d_cs,d_ss_thms);*)
           isar_atp' (ctxt,prems, thm)
    end;

end




end;

Proof.atp_hook := ResAtp.isar_atp;
