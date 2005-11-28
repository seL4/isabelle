(*  Author: Jia Meng, Cambridge University Computer Laboratory
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
  val writeln_strs: TextIO.outstream -> TextIO.vector list -> unit
end;

structure ResAtp: RES_ATP =
struct

val call_atp = ref false;
val hook_count = ref 0;
val time_limit = ref 60;

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


(**** For running in Isar ****)

(* same function as that in res_axioms.ML *)
fun repeat_RS thm1 thm2 =
    let val thm1' =  thm1 RS thm2 handle THM _ => thm1
    in
        if eq_thm(thm1,thm1') then thm1' else (repeat_RS thm1' thm2)
    end;

(* a special version of repeat_RS *)
fun repeat_someI_ex th = repeat_RS th someI_ex;

fun writeln_strs _   []      = ()
  | writeln_strs out (s::ss) = (TextIO.output (out, s); TextIO.output (out, "\n"); writeln_strs out ss);

(* write out a subgoal as tptp clauses to the file "xxxx_N"*)
fun tptp_inputs_tfrees ths pf n (axclauses,classrel_clauses,arity_clauses) =
  let
    val clss = ResClause.make_conjecture_clauses (map prop_of ths)
    val (tptp_clss,tfree_litss) = ListPair.unzip (map ResClause.clause2tptp clss)
    val tfree_clss = map ResClause.tfree_clause (foldl (op union_string) [] tfree_litss)
    val classrel_cls = map ResClause.tptp_classrelClause classrel_clauses
    val arity_cls = map ResClause.tptp_arity_clause arity_clauses
    val out = TextIO.openOut(pf n)
  in
    writeln_strs out (List.concat (map ResClause.tptp_clause axclauses));
    writeln_strs out (tfree_clss @ tptp_clss @ classrel_cls @ arity_cls);
    TextIO.closeOut out
  end;

(* write out a subgoal in DFG format to the file "xxxx_N"*)
fun dfg_inputs_tfrees ths pf n (axclauses,classrel_clauses,arity_clauses) = 
    let val clss = ResClause.make_conjecture_clauses (map prop_of ths)
        (*FIXME: classrel_clauses and arity_clauses*)
        val probN = ResClause.clauses2dfg clss (!problem_name ^ "_" ^ Int.toString n)
                        axclauses [] [] []    
	val out = TextIO.openOut(pf n)
    in
	writeln_strs out [probN]; TextIO.closeOut out
    end;


(* call prover with settings and problem file for the current subgoal *)
fun watcher_call_provers sign sg_terms (childin, childout, pid) =
  let
    fun make_atp_list [] n = []
      | make_atp_list (sg_term::xs) n =
          let
            val probfile = prob_pathname n
            val time = Int.toString (!time_limit)
          in
            debug ("problem file in watcher_call_provers is " ^ probfile);
            (*Avoid command arguments containing spaces: Poly/ML and SML/NJ
              versions of Unix.execute treat them differently!*)
            (*options are separated by Watcher.setting_sep, currently #"%"*)
            if !prover = "spass"
            then
              let val optionline = 
		      if !AtpCommunication.reconstruct 
		          (*Proof reconstruction works for only a limited set of 
		            inference rules*)
                      then space_implode "%" (!custom_spass) ^
                           "%-DocProof%-TimeLimit=" ^ time
                      else "-DocProof%-SOS%-FullRed=0%-TimeLimit=" ^ time (*Auto mode*)
                  val _ = debug ("SPASS option string is " ^ optionline)
                  val _ = helper_path "SPASS_HOME" "SPASS"
                    (*We've checked that SPASS is there for ATP/spassshell to run.*)
              in 
                  ([("spass", 
                     getenv "ISABELLE_HOME" ^ "/src/HOL/Tools/ATP/spassshell",
                     optionline, probfile)] @ 
                  (make_atp_list xs (n+1)))
              end
            else if !prover = "vampire"
	    then 
              let val vampire = helper_path "VAMPIRE_HOME" "vampire"
              in
                ([("vampire", vampire, "-m 100000%-t " ^ time, probfile)] @
                 (make_atp_list xs (n+1)))       (*BEWARE! spaces in options!*)
              end
      	     else if !prover = "E"
      	     then
	       let val Eprover = helper_path "E_HOME" "eproof"
	       in
		  ([("E", Eprover, 
		     "--tptp-in%-l5%-xAuto%-tAuto%--cpu-limit=" ^ time,
		     probfile)] @
		   (make_atp_list xs (n+1)))
	       end
	     else error ("Invalid prover name: " ^ !prover)
          end

    val atp_list = make_atp_list sg_terms 1
  in
    Watcher.callResProvers(childout,atp_list);
    debug "Sent commands to watcher!"
  end

(*We write out problem files for each subgoal. Argument pf generates filenames,
  and allows the suppression of the suffix "_1" in problem-generation mode.*)
fun write_problem_files pf (ctxt,th)  =
  let val prems = Thm.prems_of th
      val (clause_arr, axclauses) = ResClasimp.get_clasimp_lemmas ctxt (hd prems) 
              (*FIXME: hack!! need to consider relevance for all prems*)
      val _ = debug ("claset and simprules total clauses = " ^ 
                     Int.toString (Array.length clause_arr))
      val thy = ProofContext.theory_of ctxt
      val classrel_clauses = if !ResClause.keep_types then ResClause.classrel_clauses_thy thy else []
      val _ = debug ("classrel clauses = " ^ Int.toString (length classrel_clauses))
      val arity_clauses = if !ResClause.keep_types then ResClause.arity_clause_thy thy else []
      val _ = debug ("arity clauses = " ^ Int.toString (length arity_clauses))
      val write = if !prover = "spass" then dfg_inputs_tfrees else tptp_inputs_tfrees
      fun writenext n =
	if n=0 then []
	 else
	   (SELECT_GOAL
	    (EVERY1 [rtac ccontr, ObjectLogic.atomize_tac, skolemize_tac, 
	      METAHYPS(fn negs => 
		(write (make_clauses negs) pf n 
		       (axclauses,classrel_clauses,arity_clauses);
		 all_tac))]) n th;
	    pf n :: writenext (n-1))
      in (writenext (length prems), clause_arr) end;

val last_watcher_pid = ref (NONE : (TextIO.instream * TextIO.outstream * 
                                    Posix.Process.pid * string list) option);

fun kill_last_watcher () =
    (case !last_watcher_pid of 
         NONE => ()
       | SOME (_, childout, pid, files) => 
	  (debug ("Killing old watcher, pid = " ^ string_of_pid pid);
	   Watcher.killWatcher pid;  
	   ignore (map (try OS.FileSys.remove) files)))
     handle OS.SysErr _ => debug "Attempt to kill watcher failed";

(*writes out the current clasimpset to a tptp file;
  turns off xsymbol at start of function, restoring it at end    *)
val isar_atp = setmp print_mode [] 
 (fn (ctxt, th) =>
  if Thm.no_prems th then ()
  else
    let
      val _ = kill_last_watcher()
      val (files,clause_arr) = write_problem_files prob_pathname (ctxt,th)
      val (childin, childout, pid) = Watcher.createWatcher (th, clause_arr)
    in
      last_watcher_pid := SOME (childin, childout, pid, files);
      debug ("problem files: " ^ space_implode ", " files); 
      debug ("pid: " ^ string_of_pid pid);
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

val invoke_atp = Toplevel.unknown_proof o Toplevel.keep (fn state =>
  let
    val proof = Toplevel.proof_of state
    val (ctxt, (_, goal)) = Proof.get_goal proof
        handle Proof.STATE _ => error "No goal present";
    val thy = ProofContext.theory_of ctxt;
  in
    debug ("subgoals in isar_atp:\n" ^ 
           Pretty.string_of (ProofContext.pretty_term ctxt
             (Logic.mk_conjunction_list (Thm.prems_of goal))));
    debug ("number of subgoals in isar_atp: " ^ Int.toString (Thm.nprems_of goal));
    debug ("current theory: " ^ Context.theory_name thy);
    hook_count := !hook_count +1;
    debug ("in hook for time: " ^ Int.toString (!hook_count));
    ResClause.init thy;
    if !destdir = "" andalso !time_limit > 0 then isar_atp (ctxt, goal)
    else isar_atp_writeonly (ctxt, goal)
  end);

val call_atpP =
  OuterSyntax.command 
    "ProofGeneral.call_atp" 
    "call automatic theorem provers" 
    OuterKeyword.diag
    (Scan.succeed (Toplevel.no_timing o invoke_atp));

val _ = OuterSyntax.add_parsers [call_atpP];

end;
