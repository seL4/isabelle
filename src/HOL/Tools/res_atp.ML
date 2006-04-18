(*  Author: Jia Meng, Cambridge University Computer Laboratory, NICTA
    ID: $Id$
    Copyright 2004 University of Cambridge

ATPs with TPTP format input.
*)

signature RES_ATP =
sig
  val prover: string ref
  val custom_spass: string list ref
  val destdir: string ref
  val helper_path: string -> string -> string
  val problem_name: string ref
  val time_limit: int ref
   
  datatype mode = Auto | Fol | Hol
  val write_subgoal_file: mode -> Proof.context -> thm list -> thm list -> int -> string
  val vampire_time: int ref
  val eprover_time: int ref
  val run_vampire: int -> unit
  val run_eprover: int -> unit
  val vampireLimit: unit -> int
  val eproverLimit: unit -> int
  val atp_method: (ProofContext.context -> thm list -> int -> Tactical.tactic) ->
		  Method.src -> ProofContext.context -> Method.method
  val cond_rm_tmp: string -> unit
  val keep_atp_input: bool ref
  val fol_keep_types: bool ref
  val hol_full_types: unit -> unit
  val hol_partial_types: unit -> unit
  val hol_const_types_only: unit -> unit
  val hol_no_types: unit -> unit
  val hol_typ_level: unit -> ResHolClause.type_level
  val run_relevance_filter: bool ref
  val invoke_atp_ml : ProofContext.context * thm -> unit
  val add_claset : unit -> unit
  val add_simpset : unit -> unit
  val add_clasimp : unit -> unit
  val add_atpset : unit -> unit
  val rm_claset : unit -> unit
  val rm_simpset : unit -> unit
  val rm_atpset : unit -> unit
  val rm_clasimp : unit -> unit
end;

structure ResAtp : RES_ATP =
struct

(********************************************************************)
(* some settings for both background automatic ATP calling procedure*)
(* and also explicit ATP invocation methods                         *)
(********************************************************************)

(*** background linkup ***)
val call_atp = ref false; 
val hook_count = ref 0;
val time_limit = ref 30;
val prover = ref "E";   (* use E as the default prover *)
val custom_spass =   (*specialized options for SPASS*)
      ref ["-Auto=0","-FullRed=0","-IORe","-IOFc","-RTaut","-RFSub","-RBSub"];
val destdir = ref "";   (*Empty means write files to /tmp*)
val problem_name = ref "prob";

(*Return the path to a "helper" like SPASS or tptp2X, first checking that
  it exists.  FIXME: modify to use Path primitives and move to some central place.*)  
fun helper_path evar base =
  case getenv evar of
      "" => error  ("Isabelle environment variable " ^ evar ^ " not defined")
    | home => 
        let val path = home ^ "/" ^ base
        in  if File.exists (File.unpack_platform_path path) then path 
	    else error ("Could not find the file " ^ path)
	end;  

fun probfile_nosuffix _ = 
  if !destdir = "" then File.platform_path (File.tmp_path (Path.basic (!problem_name)))
  else if File.exists (File.unpack_platform_path (!destdir))
  then !destdir ^ "/" ^ !problem_name
  else error ("No such directory: " ^ !destdir);

fun prob_pathname n = probfile_nosuffix n ^ "_" ^ Int.toString n;


(*** ATP methods ***)
val vampire_time = ref 60;
val eprover_time = ref 60;
fun run_vampire time =  
    if (time >0) then vampire_time:= time
    else vampire_time:=60;

fun run_eprover time = 
    if (time > 0) then eprover_time:= time
    else eprover_time:=60;

fun vampireLimit () = !vampire_time;
fun eproverLimit () = !eprover_time;

val keep_atp_input = ref false;
val fol_keep_types = ResClause.keep_types;
val hol_full_types = ResHolClause.full_types;
val hol_partial_types = ResHolClause.partial_types;
val hol_const_types_only = ResHolClause.const_types_only;
val hol_no_types = ResHolClause.no_types;
fun hol_typ_level () = ResHolClause.find_typ_level ();
fun is_typed_hol () = 
    let val tp_level = hol_typ_level()
    in
	not (tp_level = ResHolClause.T_NONE)
    end;
val include_combS = ResHolClause.include_combS;
val include_min_comb = ResHolClause.include_min_comb;

fun atp_input_file () =
    let val file = !problem_name 
    in
	if !destdir = "" then File.platform_path (File.tmp_path (Path.basic file))
	else if File.exists (File.unpack_platform_path (!destdir))
	then !destdir ^ "/" ^ file
	else error ("No such directory: " ^ !destdir)
    end;

val include_simpset = ref false;
val include_claset = ref false; 
val include_atpset = ref true;
val add_simpset = (fn () => include_simpset:=true);
val add_claset = (fn () => include_claset:=true);
val add_clasimp = (fn () => (include_simpset:=true;include_claset:=true));
val add_atpset = (fn () => include_atpset:=true);
val rm_simpset = (fn () => include_simpset:=false);
val rm_claset = (fn () => include_claset:=false);
val rm_clasimp = (fn () => (include_simpset:=false;include_claset:=false));
val rm_atpset = (fn () => include_atpset:=false);

(*** paths for HOL helper files ***)
fun full_typed_comb_inclS () =
    helper_path "E_HOME" "additionals/full_comb_inclS"
    handle _ => helper_path "VAMPIRE_HOME" "additionals/full_comb_inclS";

fun full_typed_comb_noS () =
    helper_path "E_HOME" "additionals/full_comb_noS"
    handle _ => helper_path "VAMPIRE_HOME" "additionals/full_comb_noS";
									      
fun partial_typed_comb_inclS () =
    helper_path "E_HOME" "additionals/par_comb_inclS"
    handle _ => helper_path "VAMPIRE_HOME" "additionals/par_comb_inclS";

fun partial_typed_comb_noS () =
    helper_path "E_HOME" "additionals/par_comb_noS"
    handle _ => helper_path "VAMPIRE_HOME" "additionals/par_comb_noS";

fun const_typed_comb_inclS () =
    helper_path "E_HOME" "additionals/const_comb_inclS"
    handle _ => helper_path "VAMPIRE_HOME" "additionals/const_comb_inclS";

fun const_typed_comb_noS () =
    helper_path "E_HOME" "additionals/const_comb_noS"
    handle _ => helper_path "VAMPIRE_HOME" "additionals/const_comb_noS";

fun untyped_comb_inclS () =
    helper_path "E_HOME" "additionals/u_comb_inclS"
    handle _ => helper_path "VAMPIRE_HOME" "additionals/u_comb_inclS";

fun untyped_comb_noS () =
    helper_path "E_HOME" "additionals/u_comb_noS"
    handle _ => helper_path "VAMPIRE_HOME" "additionals/u_comb_noS";

fun full_typed_HOL_helper1 () =
    helper_path "E_HOME" "additionals/full_helper1"
    handle _ => helper_path "VAMPIRE_HOME" "additionals/full_helper1";

fun partial_typed_HOL_helper1 () = 
    helper_path "E_HOME" "additionals/par_helper1"
    handle _ => helper_path "VAMPIRE_HOME" "additionals/par_helper1";

fun const_typed_HOL_helper1 () = 
    helper_path "E_HOME" "additionals/const_helper1"
    handle _ => helper_path "VAMPIRE_HOME" "additionals/const_helper1";

fun untyped_HOL_helper1 () = 
    helper_path "E_HOME" "additionals/u_helper1"
    handle _ => helper_path "VAMPIRE_HOME" "additionals/u_helper1";

fun get_full_typed_helpers () =
    (full_typed_HOL_helper1 (), full_typed_comb_noS (), full_typed_comb_inclS ());

fun get_partial_typed_helpers () =
    (partial_typed_HOL_helper1 (), partial_typed_comb_noS (), partial_typed_comb_inclS ());

fun get_const_typed_helpers () =
    (const_typed_HOL_helper1 (), const_typed_comb_noS (), const_typed_comb_inclS ());

fun get_untyped_helpers () =
    (untyped_HOL_helper1 (), untyped_comb_noS (), untyped_comb_inclS ());

fun get_all_helpers () =
    (get_full_typed_helpers (), get_partial_typed_helpers (), get_const_typed_helpers (), get_untyped_helpers ());


(**** relevance filter ****)
val run_relevance_filter = ref true;

(******************************************************************)
(* detect whether a given problem (clauses) is FOL/HOL/HOLC/HOLCS *)
(******************************************************************)

datatype logic = FOL | HOL | HOLC | HOLCS;

fun string_of_logic FOL = "FOL"
  | string_of_logic HOL = "HOL"
  | string_of_logic HOLC = "HOLC"
  | string_of_logic HOLCS = "HOLCS";


fun is_fol_logic FOL = true
  | is_fol_logic  _ = false


(*HOLCS will not occur here*)
fun upgrade_lg HOLC _ = HOLC
  | upgrade_lg HOL HOLC = HOLC
  | upgrade_lg HOL _ = HOL
  | upgrade_lg FOL lg = lg; 

(* check types *)
fun has_bool (Type("bool",_)) = true
  | has_bool (Type(_, Ts)) = exists has_bool Ts
  | has_bool _ = false;

fun has_bool_arg tp = 
    let val (targs,tr) = strip_type tp
    in
	exists has_bool targs
    end;

fun is_fn_tp (Type("fun",_)) = true
  | is_fn_tp _ = false;


exception FN_LG of term;

fun fn_lg (t as Const(f,tp)) (lg,seen) = 
    if has_bool tp then (upgrade_lg HOL lg, t ins seen) else (lg, t ins seen) 
  | fn_lg (t as Free(f,tp)) (lg,seen) = 
    if has_bool tp then (upgrade_lg HOL lg, t ins seen) else (lg, t ins seen) 
  | fn_lg (t as Var(f,tp)) (lg,seen) =
    if is_fn_tp tp orelse has_bool tp then (upgrade_lg HOL lg,t ins seen)
    else (lg,t ins seen)
  | fn_lg (t as Abs(_,_,_)) (lg,seen) = (upgrade_lg HOLC lg,t ins seen)
  | fn_lg f _ = raise FN_LG(f); 


fun term_lg [] (lg,seen) = (lg,seen)
  | term_lg (tm::tms) (FOL,seen) =
    let val (f,args) = strip_comb tm
	val (lg',seen') = if f mem seen then (FOL,seen) 
			  else fn_lg f (FOL,seen)

	 in
	     term_lg (args@tms) (lg',seen')
    end
  | term_lg _ (lg,seen) = (lg,seen)

exception PRED_LG of term;

fun pred_lg (t as Const(P,tp)) (lg,seen)= 
    if has_bool_arg tp then (upgrade_lg HOL lg, t ins seen) else (lg,t ins seen) 
  | pred_lg (t as Free(P,tp)) (lg,seen) =
    if has_bool_arg tp then (upgrade_lg HOL lg, t ins seen) else (lg,t ins seen)
  | pred_lg (t as Var(_,_)) (lg,seen) = (upgrade_lg HOL lg, t ins seen)
  | pred_lg P _ = raise PRED_LG(P);


fun lit_lg (Const("Not",_) $ P) (lg,seen) = lit_lg P (lg,seen)
  | lit_lg P (lg,seen) =
    let val (pred,args) = strip_comb P
	val (lg',seen') = if pred mem seen then (lg,seen) 
			  else pred_lg pred (lg,seen)
	val _ = if is_fol_logic lg' then () else warning ("Found a HOL predicate: " ^ (Term.str_of_term pred))
    in
	term_lg args (lg',seen')
    end;

fun lits_lg [] (lg,seen) = (lg,seen)
  | lits_lg (lit::lits) (FOL,seen) =
    let val (lg,seen') = lit_lg lit (FOL,seen)
	val _ =  if is_fol_logic lg then () else warning ("Found a HOL literal: " ^ (Term.str_of_term lit))
    in
	lits_lg lits (lg,seen')
    end
  | lits_lg lits (lg,seen) = (lg,seen);


fun dest_disj_aux (Const ("op |", _) $ t $ t') disjs = 
    dest_disj_aux t (dest_disj_aux t' disjs)
  | dest_disj_aux t disjs = t::disjs;

fun dest_disj t = dest_disj_aux t [];

fun logic_of_clause tm (lg,seen) =
    let val tm' = HOLogic.dest_Trueprop tm
	val disjs = dest_disj tm'
    in
	lits_lg disjs (lg,seen)
    end;

fun logic_of_clauses [] (lg,seen) = (lg,seen)
  | logic_of_clauses (cls::clss) (FOL,seen) =
    let val (lg,seen') = logic_of_clause cls (FOL,seen)
	val _ = if is_fol_logic lg then () else warning ("Found a HOL clause: " ^ (Term.str_of_term cls))
    in
	logic_of_clauses clss (lg,seen')
    end
  | logic_of_clauses (cls::clss) (lg,seen) = (lg,seen);

fun problem_logic_goals_aux [] (lg,seen) = lg
  | problem_logic_goals_aux (subgoal::subgoals) (lg,seen) = 
    problem_logic_goals_aux subgoals (logic_of_clauses subgoal (lg,seen));
    
fun problem_logic_goals subgoals = problem_logic_goals_aux subgoals (FOL,[]);


(***************************************************************)
(* ATP invocation methods setup                                *)
(***************************************************************)


(**** prover-specific format: TPTP ****)


fun cnf_hyps_thms ctxt = 
    let val ths = ProofContext.prems_of ctxt
    in
	ResClause.union_all (map ResAxioms.skolem_thm ths)
    end;


(**** write to files ****)

datatype mode = Auto | Fol | Hol;

val linkup_logic_mode = ref Fol;

fun tptp_writer logic goals filename (axioms,classrels,arities) =
    if is_fol_logic logic then ResClause.tptp_write_file goals filename (axioms, classrels, arities)
    else
	ResHolClause.tptp_write_file goals filename (axioms, classrels, arities) (get_all_helpers());


fun write_subgoal_file mode ctxt conjectures user_thms n =
    let val conj_cls = make_clauses conjectures 
	val hyp_cls = cnf_hyps_thms ctxt
	val goal_cls = conj_cls@hyp_cls
	val user_rules = map ResAxioms.pairname user_thms
	val (names_arr,axclauses_as_thms) = ResClasimp.get_clasimp_atp_lemmas ctxt (map prop_of goal_cls) user_rules (!include_claset,!include_simpset,!include_atpset) (!run_relevance_filter)  
	val thy = ProofContext.theory_of ctxt
	val prob_logic = case mode of Auto => problem_logic_goals [map prop_of goal_cls]
				    | Fol => FOL
				    | Hol => HOL
	val keep_types = if is_fol_logic prob_logic then !fol_keep_types else is_typed_hol ()
	val classrel_clauses = if keep_types then ResClause.classrel_clauses_thy thy else []
	val arity_clauses = if keep_types then ResClause.arity_clause_thy thy else []
	val writer = tptp_writer
	val file = atp_input_file()
    in
	(writer prob_logic goal_cls file (axclauses_as_thms,classrel_clauses,arity_clauses);
	 warning ("Writing to " ^ file);
	 file)
    end;


(**** remove tmp files ****)
fun cond_rm_tmp file = 
    if !keep_atp_input then warning "ATP input kept..." 
    else if !destdir <> "" then warning ("ATP input kept in directory " ^ (!destdir))
    else (warning "deleting ATP inputs..."; OS.FileSys.remove file);


(****** setup ATPs as Isabelle methods ******)
fun atp_meth' tac ths ctxt = 
    Method.SIMPLE_METHOD' HEADGOAL
    (tac ctxt ths);

fun atp_meth tac ths ctxt = 
    let val thy = ProofContext.theory_of ctxt
	val _ = ResClause.init thy
	val _ = ResHolClause.init thy
    in
	atp_meth' tac ths ctxt
    end;

fun atp_method tac = Method.thms_ctxt_args (atp_meth tac);

(***************************************************************)
(* automatic ATP invocation                                    *)
(***************************************************************)

(* call prover with settings and problem file for the current subgoal *)
fun watcher_call_provers sign sg_terms (childin, childout, pid) =
  let
    fun make_atp_list [] n = []
      | make_atp_list (sg_term::xs) n =
          let
            val probfile = prob_pathname n
            val time = Int.toString (!time_limit)
          in
            Output.debug ("problem file in watcher_call_provers is " ^ probfile);
            (*Avoid command arguments containing spaces: Poly/ML and SML/NJ
              versions of Unix.execute treat them differently!*)
            (*options are separated by Watcher.setting_sep, currently #"%"*)
            if !prover = "spass"
            then
              let val baseopts = "%-PGiven=0%-PProblem=0%-Splits=0%-FullRed=0%-DocProof%-TimeLimit=" ^ time
              val infopts = 
		      if !AtpCommunication.reconstruct 
		          (*Proof reconstruction needs a limited set of inf rules*)
                      then space_implode "%" (!custom_spass)                           
                      else "-Auto%-SOS=1"
                  val spass = helper_path "SPASS_HOME" "SPASS"
            in 
                ([("spass", spass, infopts ^ baseopts, probfile)] @ 
                  make_atp_list xs (n+1))
              end
            else if !prover = "vampire"
	    then 
              let val vampire = helper_path "VAMPIRE_HOME" "vampire"
              in
                ([("vampire", vampire, "-m 100000%-t " ^ time, probfile)] @
                 make_atp_list xs (n+1))       (*BEWARE! spaces in options!*)
              end
      	     else if !prover = "E"
      	     then
	       let val Eprover = helper_path "E_HOME" "eproof"
	       in
		  ([("E", Eprover, 
		     "--tptp-in%-l5%-xAuto%-tAuto%--cpu-limit=" ^ time,
		     probfile)] @
		   make_atp_list xs (n+1))
	       end
	     else error ("Invalid prover name: " ^ !prover)
          end

    val atp_list = make_atp_list sg_terms 1
  in
    Watcher.callResProvers(childout,atp_list);
    Output.debug "Sent commands to watcher!"
  end

(*We write out problem files for each subgoal. Argument pf generates filenames,
  and allows the suppression of the suffix "_1" in problem-generation mode.
  FIXME: does not cope with &&, and it isn't easy because one could have multiple
  subgoals, each involving &&.*)
fun write_problem_files pf (ctxt,th)  =
  let val goals = Thm.prems_of th
      val _ = Output.debug ("number of subgoals = " ^ Int.toString (length goals))
      val (names_arr, axclauses) = ResClasimp.get_clasimp_atp_lemmas ctxt goals [] (true,true,true) (!run_relevance_filter) (* no user supplied rules here, because no user invocation *)
      val _ = Output.debug ("claset, simprules and atprules total clauses = " ^ 
                     Int.toString (Array.length names_arr))
      val thy = ProofContext.theory_of ctxt
      fun get_neg_subgoals n =
	  if n=0 then []
	  else
	      let val st = Seq.hd (EVERY'
				       [rtac ccontr, ObjectLogic.atomize_tac, skolemize_tac] n th)
		  val negs = Option.valOf (metahyps_thms n st)
		  val negs_clauses = make_clauses negs
	      in
		  negs_clauses::(get_neg_subgoals (n - 1))
	      end
      val neg_subgoals = get_neg_subgoals (length goals) 
      val goals_logic = case !linkup_logic_mode of Auto => problem_logic_goals (map (map prop_of) neg_subgoals)
						 | Fol => FOL
						 | Hol => HOL
      val keep_types = if is_fol_logic goals_logic then !ResClause.keep_types else is_typed_hol ()
      val classrel_clauses = if keep_types then ResClause.classrel_clauses_thy thy else []
      val _ = Output.debug ("classrel clauses = " ^ Int.toString (length classrel_clauses))
      val arity_clauses = if keep_types then ResClause.arity_clause_thy thy else []
      val _ = Output.debug ("arity clauses = " ^ Int.toString (length arity_clauses))
      val writer = (*if !prover ~= "spass" then *)tptp_writer 
      fun write_all [] _ = []
	| write_all (subgoal::subgoals) k =
	  (writer goals_logic subgoal (pf k) (axclauses,classrel_clauses,arity_clauses); pf k):: (write_all subgoals (k - 1))
  in
      (write_all neg_subgoals (length goals), names_arr)
  end;

val last_watcher_pid = ref (NONE : (TextIO.instream * TextIO.outstream * 
                                    Posix.Process.pid * string list) option);

fun kill_last_watcher () =
    (case !last_watcher_pid of 
         NONE => ()
       | SOME (_, childout, pid, files) => 
	  (Output.debug ("Killing old watcher, pid = " ^ string_of_pid pid);
	   Watcher.killWatcher pid;  
	   ignore (map (try OS.FileSys.remove) files)))
     handle OS.SysErr _ => Output.debug "Attempt to kill watcher failed";

(*writes out the current clasimpset to a tptp file;
  turns off xsymbol at start of function, restoring it at end    *)
val isar_atp = setmp print_mode [] 
 (fn (ctxt, th) =>
  if Thm.no_prems th then ()
  else
    let
      val _ = kill_last_watcher()
      val (files,names_arr) = write_problem_files prob_pathname (ctxt,th)
      val (childin, childout, pid) = Watcher.createWatcher (th, names_arr)
    in
      last_watcher_pid := SOME (childin, childout, pid, files);
      Output.debug ("problem files: " ^ space_implode ", " files); 
      Output.debug ("pid: " ^ string_of_pid pid);
      watcher_call_provers (sign_of_thm th) (Thm.prems_of th) (childin, childout, pid)
    end);

val isar_atp_writeonly = setmp print_mode [] 
      (fn (ctxt,th) =>
       if Thm.no_prems th then ()
       else 
         let val pf = if Thm.nprems_of th = 1 then probfile_nosuffix 
         	      else prob_pathname
         in ignore (write_problem_files pf (ctxt,th)) end);


(** the Isar toplevel hook **)

fun invoke_atp_ml (ctxt, goal) =
  let val thy = ProofContext.theory_of ctxt;
  in
    Output.debug ("subgoals in isar_atp:\n" ^ 
		  Pretty.string_of (ProofContext.pretty_term ctxt
		    (Logic.mk_conjunction_list (Thm.prems_of goal))));
    Output.debug ("current theory: " ^ Context.theory_name thy);
    hook_count := !hook_count +1;
    Output.debug ("in hook for time: " ^ Int.toString (!hook_count));
    ResClause.init thy;
    ResHolClause.init thy;
    if !destdir = "" andalso !time_limit > 0 then isar_atp (ctxt, goal)
    else isar_atp_writeonly (ctxt, goal)
  end;

val invoke_atp = Toplevel.no_timing o Toplevel.unknown_proof o Toplevel.keep
 (fn state =>
  let val (ctxt, (_, goal)) = Proof.get_goal (Toplevel.proof_of state)
  in  invoke_atp_ml (ctxt, goal)  end);

val call_atpP =
  OuterSyntax.command 
    "ProofGeneral.call_atp" 
    "call automatic theorem provers" 
    OuterKeyword.diag
    (Scan.succeed invoke_atp);

val _ = OuterSyntax.add_parsers [call_atpP];

end;
