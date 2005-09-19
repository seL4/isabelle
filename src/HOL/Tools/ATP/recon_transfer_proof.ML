(*  ID:         $Id$
    Author:     Claire Quigley
    Copyright   2004  University of Cambridge
*)

structure Recon_Transfer =
struct

open Recon_Parse

infixr 8 ++; infixr 7 >>; infixr 6 ||;


(* Versions that include type information *)
 
(* FIXME rename to str_of_thm *)
fun string_of_thm thm =
  setmp show_sorts true (Pretty.str_of o Display.pretty_thm) thm;


(* check separate args in the watcher program for separating strings with a * or ; or something *)

fun clause_strs_to_string [] str = str
|   clause_strs_to_string (x::xs) str = clause_strs_to_string xs (str^x^"%")

fun thmvars_to_string [] str = str
|   thmvars_to_string (x::xs) str = thmvars_to_string xs (str^x^"%")


fun proofstep_to_string Axiom = "Axiom()"
|   proofstep_to_string  (Binary ((a,b), (c,d)))=
      "Binary(("^(string_of_int a)^","^(string_of_int b)^"),("^(string_of_int c)^","^(string_of_int d)^"))"
|   proofstep_to_string (Factor (a,b,c)) =
      "Factor("^(string_of_int a)^","^(string_of_int b)^","^(string_of_int c)^")"
|   proofstep_to_string  (Para ((a,b), (c,d)))= 
      "Para(("^(string_of_int a)^","^(string_of_int b)^"),("^(string_of_int c)^","^(string_of_int d)^"))"
|   proofstep_to_string  (MRR ((a,b), (c,d))) =
      "MRR(("^(string_of_int a)^","^(string_of_int b)^"),("^(string_of_int c)^","^(string_of_int d)^"))"
(*|   proofstep_to_string (Rewrite((a,b),(c,d))) =
      "Rewrite(("^(string_of_int a)^","^(string_of_int b)^"),("^(string_of_int c)^","^(string_of_int d)^"))"*)


fun proof_to_string (num,(step,clause_strs, thmvars)) =
 (string_of_int num)^(proofstep_to_string step)^
 "["^(clause_strs_to_string clause_strs "")^"]["^(thmvars_to_string thmvars "")^"]"
 

fun proofs_to_string [] str = str
|   proofs_to_string (x::xs) str = let val newstr = proof_to_string x 
                                   in
                                       proofs_to_string xs (str^newstr)
                                   end



fun init_proofstep_to_string (num, step, clause_strs) =
 (string_of_int num)^" "^(proofstep_to_string step)^" "^
 (clause_strs_to_string clause_strs "")^" "

fun init_proofsteps_to_string [] str = str
|   init_proofsteps_to_string (x::xs) str = let val newstr = init_proofstep_to_string x 
                                   in
                                       init_proofsteps_to_string xs (str^newstr)
                                   end
  


(*** get a string representing the Isabelle ordered axioms ***)

fun origAx_to_string (num,(meta,thmvars)) =
    let val clause_strs = ReconOrderClauses.get_meta_lits_bracket meta
    in
       (string_of_int num)^"OrigAxiom()["^
       (clause_strs_to_string clause_strs "")^"]["^
       (thmvars_to_string thmvars "")^"]"
    end


fun  origAxs_to_string [] str = str
|   origAxs_to_string (x::xs) str = let val newstr = origAx_to_string x 
                                   in
                                       origAxs_to_string xs (str^newstr)
                                   end


(*** get a string representing the Isabelle ordered axioms not used in the spass proof***)

fun extraAx_to_string (num, (meta,thmvars)) =
   let val clause_strs = ReconOrderClauses.get_meta_lits_bracket meta
   in
      (string_of_int num)^"ExtraAxiom()["^
      (clause_strs_to_string clause_strs "")^"]"^
      "["^(thmvars_to_string thmvars "")^"]"
   end;

fun extraAxs_to_string [] str = str
|   extraAxs_to_string (x::xs) str =
      let val newstr = extraAx_to_string x 
      in
	  extraAxs_to_string xs (str^newstr)
      end;

fun is_axiom (_,Axiom,str) = true
|   is_axiom (_,_,_) = false

fun get_step_nums [] nums = nums
|   get_step_nums (( num:int,Axiom, str)::xs) nums = get_step_nums xs (nums@[num])

exception Noassoc;

fun assoc_snd a [] = raise Noassoc
  | assoc_snd a ((x, y)::t) = if a = y then x else assoc_snd a t;

(* change to be something using check_order  instead of a = y --> returns true if ASSERTION not raised in checkorder, false otherwise *)

(*fun get_assoc_snds [] xs assocs= assocs
|   get_assoc_snds (x::xs) ys assocs = get_assoc_snds xs ys (assocs@[((assoc_snd x ys))])
*)
(*FIX - should this have vars in it? *)
fun there_out_of_order xs ys = (ReconOrderClauses.checkorder xs ys [] ([],[],[]); true) 
                               handle _ => false

fun assoc_out_of_order a [] = raise Noassoc
|   assoc_out_of_order a ((b,c)::t) = if there_out_of_order a c then b else assoc_out_of_order a t;

fun get_assoc_snds [] xs assocs= assocs
|   get_assoc_snds (x::xs) ys assocs = get_assoc_snds xs ys (assocs@[((assoc_out_of_order x ys))])

fun add_if_not_inlist [] xs newlist = newlist
|   add_if_not_inlist (y::ys) xs newlist = if (not (y mem xs)) then 
                                      add_if_not_inlist ys xs (y::newlist)
                                        else add_if_not_inlist ys xs (newlist)

(*Flattens a list of list of strings to one string*)
fun onestr ls = String.concat (map String.concat ls);

fun is_clasimp_ax clasimp_num n = n <= clasimp_num 

fun subone x = x - 1

fun numstr [] = ""
|   numstr (x::xs) = (string_of_int x)^"%"^(numstr xs)


(* retrieve the axioms that were obtained from the clasimpset *)

fun get_clasimp_cls (clause_arr: (ResClause.clause * thm) array) step_nums = 
    let val clasimp_nums = List.filter (is_clasimp_ax (Array.length clause_arr - 1)) 
	                   (map subone step_nums)
(*	val _ = File.write (File.tmp_path (Path.basic "axnums")) 
                     (numstr clasimp_nums) *)
    in
	map (fn x =>  Array.sub(clause_arr, x)) clasimp_nums
    end


(*****************************************************)
(* get names of clasimp axioms used                  *)
(*****************************************************)

 fun get_axiom_names step_nums clause_arr =
   let 
     (* not sure why this is necessary again, but seems to be *)
      val _ = (print_mode := (Library.gen_rems (op =) (! print_mode, ["xsymbols", "symbols"])))
  
     (***********************************************)
     (* here need to add the clauses from clause_arr*)
     (***********************************************)
  
      val clasimp_names_cls = get_clasimp_cls clause_arr step_nums 
      val clasimp_names = map (ResClause.get_axiomName o #1) clasimp_names_cls
      val _ = File.write (File.tmp_path (Path.basic "clasimp_names"))                                                               
                         (concat clasimp_names)
      val _ = (print_mode := (["xsymbols", "symbols"] @ ! print_mode))
   in
      clasimp_names
   end
   

fun get_axiom_names_spass proofstr clause_arr =
  let (* parse spass proof into datatype *)
      val _ = File.write (File.tmp_path (Path.basic "parsing_progress")) 
                         ("Started parsing:\n" ^ proofstr)
      val tokens = #1(lex proofstr)
      val proof_steps = parse tokens
      val _ = File.append (File.tmp_path (Path.basic "parsing_progress")) "\nFinished!"
      (* get axioms as correctly numbered clauses w.r.t. the Spass proof *)
  in
    get_axiom_names (get_step_nums (List.filter is_axiom proof_steps) []) clause_arr
  end;
    
 (*String contains multiple lines, terminated with newline characters.
  A list consisting of the first number in each line is returned. *)
fun get_linenums proofstr = 
  let val numerics = String.tokens (not o Char.isDigit)
      fun firstno [] = NONE
        | firstno (x::xs) = Int.fromString x
      val lines = String.tokens (fn c => c = #"\n") proofstr
  in  List.mapPartial (firstno o numerics) lines  end

fun get_axiom_names_vamp_E proofstr clause_arr  =
   get_axiom_names (get_linenums proofstr) clause_arr;
    

(***********************************************)
(* get axioms for reconstruction               *)
(***********************************************)
fun numclstr (vars, []) str = str
|   numclstr ( vars, ((num, thm)::rest)) str =
      let val newstr = str^(string_of_int num)^" "^(string_of_thm thm)^" "
      in
        numclstr  (vars,rest) newstr
      end

fun addvars c (a,b)  = (a,b,c)

fun get_axioms_used proof_steps thms clause_arr  =
  let 
     val _=  (print_mode := (Library.gen_rems (op =) (! print_mode, ["xsymbols", "symbols"])))
     val axioms = (List.filter is_axiom) proof_steps
     val step_nums = get_step_nums axioms []

     val clauses = make_clauses thms    (*FIXME: must this be repeated??*)
     
     val vars = map thm_vars clauses
    
     val distvars = distinct (fold append vars [])
     val clause_terms = map prop_of clauses  
     val clause_frees = List.concat (map term_frees clause_terms)

     val frees = map lit_string_with_nums clause_frees;

     val distfrees = distinct frees

     val metas = map Meson.make_meta_clause clauses
     val ax_strs = map #3 axioms

     (* literals of -all- axioms, not just those used by spass *)
     val meta_strs = map ReconOrderClauses.get_meta_lits metas
    
     val metas_and_strs = ListPair.zip (metas,meta_strs)
     val _ = File.write(File.tmp_path (Path.basic "foo_clauses")) (onestr ax_strs)
     val _ = File.write(File.tmp_path (Path.basic "foo_metastrs")) (onestr meta_strs)

     (* get list of axioms as thms with their variables *)

     val ax_metas = get_assoc_snds ax_strs metas_and_strs []
     val ax_vars = map thm_vars ax_metas
     val ax_with_vars = ListPair.zip (ax_metas,ax_vars)

     (* get list of extra axioms as thms with their variables *)
     val extra_metas = add_if_not_inlist metas ax_metas []
     val extra_vars = map thm_vars extra_metas
     val extra_with_vars = if (not (extra_metas = []) ) 
			   then ListPair.zip (extra_metas,extra_vars)
			   else []
  in
     (distfrees,distvars, extra_with_vars,ax_with_vars, ListPair.zip (step_nums,ax_metas))
  end;
                                            

(*********************************************************************)
(* Pass in spass string of proof and string version of isabelle goal *)
(* Get out reconstruction steps as a string to be sent to Isabelle   *)
(*********************************************************************)

fun rules_to_string [] = "NONE"
  | rules_to_string xs = "[" ^ space_implode ", " xs ^ "]"

fun subst_for a b = String.translate (fn c => str (if c=a then b else c));

val remove_linebreaks = subst_for #"\n" #"\t";
val restore_linebreaks = subst_for #"\t" #"\n";


fun prover_lemma_list_aux getax proofstr goalstring toParent ppid clause_arr = 
 let val _ = File.append(File.tmp_path (Path.basic "prover_lemmastring"))
               ("proofstr is " ^ proofstr ^
                "\ngoalstr is " ^ goalstring ^
                "\nnum of clauses is " ^ string_of_int (Array.length clause_arr))
     val axiom_names = getax proofstr clause_arr
     val ax_str = rules_to_string axiom_names
    in 
	 File.append(File.tmp_path (Path.basic "prover_lemmastring"))
	            ("\nlemma list is: " ^ ax_str);
         TextIO.output (toParent, "Success. Lemmas used in automatic proof: " ^
                  ax_str ^ "\n");
	 TextIO.output (toParent, "goalstring: "^goalstring^"\n");
	 TextIO.flushOut toParent;

	 Posix.Process.kill(Posix.Process.K_PROC ppid, Posix.Signal.usr2);
	(* Attempt to prevent several signals from turning up simultaneously *)
	 Posix.Process.sleep(Time.fromSeconds 1); ()
    end
    handle exn => (*FIXME: exn handler is too general!*)
     (File.write(File.tmp_path (Path.basic "proverString_handler")) 
         ("In exception handler: " ^ Toplevel.exn_message exn);
      TextIO.output (toParent, "Translation failed for the proof: " ^ 
                     remove_linebreaks proofstr ^ "\n");
      TextIO.output (toParent, remove_linebreaks goalstring ^ "\n");
      TextIO.flushOut toParent;
      Posix.Process.kill(Posix.Process.K_PROC ppid, Posix.Signal.usr2);
      (* Attempt to prevent several signals from turning up simultaneously *)
      Posix.Process.sleep(Time.fromSeconds 1); ());

val prover_lemma_list = prover_lemma_list_aux get_axiom_names_vamp_E;

val spass_lemma_list = prover_lemma_list_aux get_axiom_names_spass;


(**** Full proof reconstruction for SPASS (not really working) ****)

fun spass_reconstruct proofstr goalstring toParent ppid thms clause_arr = 
  let val _ = File.write(File.tmp_path (Path.basic "prover_reconstruction")) 
                 ("proofstr is: "^proofstr)
      val tokens = #1(lex proofstr)

  (***********************************)
  (* parse spass proof into datatype *)
  (***********************************)
      val proof_steps = parse tokens

      val _ = File.append (File.tmp_path (Path.basic "prover_reconstruction"))
                      ("Did parsing on "^proofstr)
    
  (************************************)
  (* recreate original subgoal as thm *)
  (************************************)
      (* get axioms as correctly numbered clauses w.r.t. the Spass proof *)
      (* need to get prems_of thm, then get right one of the prems, relating to whichever*)
      (* subgoal this is, and turn it into meta_clauses *)
      (* should prob add array and table here, so that we can get axioms*)
      (* produced from the clasimpset rather than the problem *)
      val (frees,vars,extra_with_vars ,ax_with_vars,numcls) = get_axioms_used proof_steps  thms clause_arr
      
      (*val numcls_string = numclstr ( vars, numcls) ""*)
      val _ = File.append (File.tmp_path (Path.basic "prover_reconstruction")) "got axioms"
	
  (************************************)
  (* translate proof                  *)
  (************************************)
      val _ = File.append (File.tmp_path (Path.basic "prover_reconstruction"))                                                                           
                       ("about to translate proof, steps: "
                       ^(init_proofsteps_to_string proof_steps ""))
      val (newthm,proof) = translate_proof numcls  proof_steps vars
      val _ = File.append (File.tmp_path (Path.basic "prover_reconstruction"))                                                                       
                       ("translated proof, steps: "^(init_proofsteps_to_string proof_steps ""))
  (***************************************************)
  (* transfer necessary steps as strings to Isabelle *)
  (***************************************************)
      (* turn the proof into a string *)
      val reconProofStr = proofs_to_string proof ""
      (* do the bit for the Isabelle ordered axioms at the top *)
      val ax_nums = map #1 numcls
      val ax_strs = map ReconOrderClauses.get_meta_lits_bracket (map #2 numcls)
      val numcls_strs = ListPair.zip (ax_nums,ax_strs)
      val num_cls_vars =  map (addvars vars) numcls_strs;
      val reconIsaAxStr = origAxs_to_string (ListPair.zip (ax_nums,ax_with_vars)) ""
      
      val extra_nums = if (not (extra_with_vars = [])) then (1 upto (length extra_with_vars))
                       else []
      val reconExtraAxStr = extraAxs_to_string ( ListPair.zip (extra_nums,extra_with_vars)) ""
      val frees_str = "["^(thmvars_to_string frees "")^"]"
      val _ = File.write (File.tmp_path (Path.basic "reconstringfile"))
                          (frees_str^reconExtraAxStr^reconIsaAxStr^reconProofStr)
      val reconstr = (frees_str^reconExtraAxStr^reconIsaAxStr^reconProofStr)
  in 
       TextIO.output (toParent, reconstr^"\n");
       TextIO.output (toParent, goalstring^"\n");
       TextIO.flushOut toParent;

       Posix.Process.kill(Posix.Process.K_PROC ppid, Posix.Signal.usr2);
      (* Attempt to prevent several signals from turning up simultaneously *)
       Posix.Process.sleep(Time.fromSeconds 1) ; all_tac
  end
  handle exn => (*FIXME: exn handler is too general!*)
   (File.append(File.tmp_path (Path.basic "prover_reconstruction"))
       ("In exception handler: " ^ Toplevel.exn_message exn);
    TextIO.output (toParent,"Translation failed for the proof:"^
         (remove_linebreaks proofstr) ^"\n");
    TextIO.output (toParent, goalstring^"\n");
    TextIO.flushOut toParent;
    Posix.Process.kill(Posix.Process.K_PROC ppid, Posix.Signal.usr2);
    (* Attempt to prevent several signals from turning up simultaneously *)
    Posix.Process.sleep(Time.fromSeconds 1); all_tac)

(**********************************************************************************)
(* At other end, want to turn back into datatype so can apply reconstruct_proof.  *)
(* This will be done by the signal handler                                        *)
(**********************************************************************************)

(* Parse in the string version of the proof steps for reconstruction *)
(* Isar format: cl1 [BINARY 0 cl2 0];cl1 [PARAMOD 0 cl2 0]; cl1 [DEMOD 0 cl2];cl1 [FACTOR 1 2];*)


 val term_numstep =
        (number ++ (a (Other ",")) ++ number) >> (fn (a, (_, c)) => (a, c))

val extraaxiomstep = (a (Word "ExtraAxiom"))++ (a (Other "(")) ++(a (Other ")"))
            >> (fn (_) => ExtraAxiom)



val origaxiomstep = (a (Word "OrigAxiom"))++ (a (Other "(")) ++(a (Other ")"))
            >> (fn (_) => OrigAxiom)


 val axiomstep = (a (Word "Axiom"))++ (a (Other "(")) ++(a (Other ")"))
            >> (fn (_) => Axiom)
     


      
 val binarystep = (a (Word "Binary")) ++ (a (Other "(")) ++ (a (Other "(")) 
                   ++ term_numstep  ++ (a (Other ")")) ++ (a (Other ","))
                   ++ (a (Other "(")) ++ term_numstep ++ (a (Other ")")) ++ (a (Other ")"))
            >> (fn (_, (_, (_, (c, (_,(_,(_, (e,(_,_))))))))) => Binary (c,e))
      

 val parastep = (a (Word "Para")) ++ (a (Other "(")) ++ (a (Other "(")) 
                   ++ term_numstep  ++ (a (Other ")")) ++ (a (Other ","))
                   ++ (a (Other "(")) ++ term_numstep ++ (a (Other ")")) ++ (a (Other ")"))
            >> (fn (_, (_, (_, (c, (_,(_,(_, (e,(_,_))))))))) => Para(c, e))
      
 val mrrstep = (a (Word "MRR")) ++ (a (Other "(")) ++ (a (Other "(")) 
                   ++ term_numstep  ++ (a (Other ")")) ++ (a (Other ","))
                   ++ (a (Other "(")) ++ term_numstep ++ (a (Other ")")) ++ (a (Other ")"))
            >> (fn (_, (_, (_, (c, (_,(_,(_, (e,(_,_))))))))) => MRR(c, e))
      

 val factorstep = (a (Word "Factor")) ++ (a (Other "("))
                    ++ number ++ (a (Other ","))
                       ++ number ++ (a (Other ","))
                       ++ number ++  (a (Other ")"))
                   
            >> (fn (_, (_, (c, (_, (e,(_,(f,_))))))) =>  Factor (c,e,f))


(*val rewritestep = (a (Word "Rewrite"))  ++ (a (Other "(")) ++ (a (Other "(")) 
                   ++ term_numstep  ++ (a (Other ")")) ++ (a (Other ","))
                   ++ (a (Other "(")) ++ term_numstep ++ (a (Other ")")) ++ (a (Other ")"))
            >> (fn (_, (_, (_, (c, (_,(_,(_, (e,(_,_))))))))) => Rewrite (c,e))*)

val obviousstep = (a (Word "Obvious")) ++ (a (Other "(")) 
                   ++ term_numstep  ++ (a (Other ")")) 
            >> (fn (_, (_, (c,_))) => Obvious (c))

 val methodstep = extraaxiomstep || origaxiomstep || axiomstep ||binarystep || factorstep|| parastep || mrrstep || (*rewritestep ||*) obviousstep


 val number_list_step =
        ( number ++ many ((a (Other ",") ++ number)>> #2))
        >> (fn (a,b) => (a::b))
        
 val numberlist_step = a (Other "[")  ++ a (Other "]")
                        >>(fn (_,_) => ([]:int list))
                       || a (Other "[") ++ number_list_step ++ a (Other "]")
                        >>(fn (_,(a,_)) => a)
                    


(** change this to allow P (x U) *)
 fun arglist_step input = 
   ( word ++ many word >> (fn (a, b) => (a^" "^(space_implode " " b)))
    ||word >> (fn (a) => (a)))input
                

fun literal_step input = (word ++ a (Other "(") ++ arglist_step ++  a (Other ")")
                                          >>(fn (a, (b, (c,d))) => (a^" ("^(c)^")"))
                        || arglist_step >> (fn (a) => (a)))input
                           


(* fun term_step input = (a (Other "~") ++ arglist_step ++ a (Other "%")>> (fn (a,(b,c)) => ("~ "^b))
                     ||  arglist_step ++ a (Other "%")>> (fn (a,b) => a ))input
*)


 fun term_step input = (a (Other "~") ++ literal_step ++ a (Other "%")>> (fn (a,(b,c)) => ("~ "^b))
                     ||  literal_step ++ a (Other "%")>> (fn (a,b) => a ))input


         

 val term_list_step =
        (  term_step ++ many ( term_step))
        >> (fn (a,b) => (a::b))
        
 
val term_lists_step = a (Other "[")  ++ a (Other "]")
                        >>(fn (_,_) => ([]:string list))
                       || a (Other "[") ++ term_list_step ++ a (Other "]")
                        >>(fn (_,(a,_)) => a)
                     



fun anytoken_step input  = (word>> (fn (a) => a)  ) input
                       handle NOPARSE_WORD => (number>> (fn (a) => string_of_int a)  ) input
                      handle NOPARSE_NUMBER => (other_char >> (fn(a) => a)) input



fun goalstring_step input= (anytoken_step ++ many (anytoken_step )
                  >> (fn (a,b) =>  (a^" "^(implode b)))) input



 val linestep = number ++ methodstep ++ term_lists_step ++ term_lists_step
                >> (fn (a, (b, (c,d))) => (a,(b,c,d)))
    
 val lines_step = many linestep

 val alllines_step = (term_lists_step ++ lines_step ) ++ finished >> #1
    
 val parse_step = #1 o alllines_step


 (*
val reconstr ="[P%x%xa%xb%]1OrigAxiom()[P x%~ P U%][U%]3OrigAxiom()[P U%~ P x%][U%]5OrigAxiom()[~ P xa%~ P U%][U%]7OrigAxiom()[P U%P xb%][U%]1Axiom()[P x%~ P U%][U%]3Axiom()[P U%~ P x%][U%]5Axiom()[~ P U%~ P xa%][U%]7Axiom()[P U%P xb%][U%]9Factor(5,0,1)[~ P xa%][]10Binary((9,0),(3,0))[~ P x%][]11Binary((10,0),(1,0))[~ P U%][U%]12Factor(7,0,1)[P xb%][]14Binary((11,0),(12,0))[][]%(EX x::'a::type. ALL y::'a::type. (P::'a::type => bool) x = P y) -->(EX x::'a::type. P x) = (ALL y::'a::type. P y)"
*)

(************************************************************)
(* Construct an Isar style proof from a list of proof steps *)
(************************************************************)
(* want to assume all axioms, then do haves for the other clauses*)
(* then show for the last step *)

(* replace ~ by not here *)
val change_nots = String.translate (fn c => if c = #"~" then "\\<not>" else str c);

fun clstrs_to_string xs = space_implode "; " (map change_nots xs);

fun thmvars_to_quantstring [] str = str
|   thmvars_to_quantstring (x::[]) str =str^x^". "
|   thmvars_to_quantstring (x::xs) str = thmvars_to_quantstring xs (str^(x^" "))


fun clause_strs_to_isar clstrs [] =
      "\"\\<lbrakk>"^(clstrs_to_string clstrs)^"\\<rbrakk> \\<Longrightarrow> False\""
|   clause_strs_to_isar clstrs thmvars =
      "\"\\<And>"^(thmvars_to_quantstring thmvars "")^
      "\\<lbrakk>"^(clstrs_to_string clstrs)^"\\<rbrakk> \\<Longrightarrow> False\""

fun frees_to_isar_str clstrs = space_implode " " (map change_nots clstrs)


(***********************************************************************)
(* functions for producing assumptions for the Isabelle ordered axioms *)
(***********************************************************************)
(*val str = "[P%x%xa%xb%]1OrigAxiom()[P x%~ P U%][U%]3OrigAxiom()[P U%~ P x%][U%]5OrigAxiom()[~ P xa%~ P U%][U%]7OrigAxiom()[P U%P xb%][U%]1Axiom()[P x%~ P U%][U%]3Axiom()[P U%~ P x%][U%]5Axiom()[~ P U%~ P xa%][U%]7Axiom()[P U%P xb%][U%]9Factor(5,0,1)[~ P xa%][]10Binary((9,0),(3,0))[~ P x%][]11Binary((10,0),(1,0))[~ P U%][U%]12Factor(7,0,1)[P xb%][]14Binary((11,0),(12,0))[][]";       
num, rule, clausestrs, vars*)


(* assume the extra clauses - not used in Spass proof *)

fun is_extraaxiom_step ( num:int,(ExtraAxiom, str, tstr)) = true
|   is_extraaxiom_step (num, _) = false

fun get_extraaxioms xs = List.filter (is_extraaxiom_step) ( xs)

fun assume_isar_extraaxiom [] str  = str
|   assume_isar_extraaxiom ((numb,(step, clstr, thmvars))::xs) str  = assume_isar_extraaxiom xs (str^"and cl"^(string_of_int numb)^"': "^(clause_strs_to_isar clstr thmvars)^"\n " )



fun assume_isar_extraaxioms  [] = ""
|assume_isar_extraaxioms ((numb,(step, clstrs, thmstrs))::xs) = let val str = "assume cl"^(string_of_int numb)^"': "^(clause_strs_to_isar clstrs thmstrs)^"\n" 
                                         in
                                             assume_isar_extraaxiom xs str
                                         end

(* assume the Isabelle ordered clauses *)

fun is_origaxiom_step ( num:int,(OrigAxiom, str, tstr)) = true
|   is_origaxiom_step (num, _) = false

fun get_origaxioms xs = List.filter (is_origaxiom_step) ( xs)

fun assume_isar_origaxiom [] str  = str
|   assume_isar_origaxiom ((numb,(step, clstr, thmvars))::xs) str  = assume_isar_origaxiom xs (str^"and cl"^(string_of_int numb)^"': "^(clause_strs_to_isar clstr thmvars)^"\n " )



fun assume_isar_origaxioms ((numb,(step, clstrs, thmstrs))::xs) = let val str = "assume cl"^(string_of_int numb)^"': "^(clause_strs_to_isar clstrs thmstrs)^"\n" 
                                         in
                                             assume_isar_origaxiom xs str
                                         end



fun is_axiom_step ( num:int,(Axiom, str, tstr)) = true
|   is_axiom_step (num, _) = false

fun get_axioms xs = List.filter  (is_axiom_step) ( xs)

fun have_isar_axiomline (numb,(step, clstrs, thmstrs))="have cl"^(string_of_int numb)^": "^(clause_strs_to_isar clstrs thmstrs)^"\n"

fun  by_isar_axiomline (numb,(step, clstrs, thmstrs))="by (rule cl"^ (string_of_int numb)^"') \n"


fun isar_axiomline (numb, (step, clstrs, thmstrs))  = (have_isar_axiomline (numb,(step,clstrs, thmstrs )))^( by_isar_axiomline(numb,(step,clstrs, thmstrs )) )


fun isar_axiomlines [] str = str
|   isar_axiomlines (x::xs) str = isar_axiomlines xs (str^(isar_axiomline x))


fun have_isar_line (numb,(step, clstrs, thmstrs))="have cl"^(string_of_int numb)^": "^(clause_strs_to_isar clstrs thmstrs)^"\n"
(*FIX: ask Larry to add and mrr attribute *)

fun by_isar_line ((Binary ((a,b), (c,d)))) = 
    "by(rule cl"^
		(string_of_int a)^" [binary "^(string_of_int b)^" cl"^
		(string_of_int c)^" "^(string_of_int d)^"])\n"
|by_isar_line ((MRR ((a,b), (c,d)))) = 
    "by(rule cl"^
		(string_of_int a)^" [binary "^(string_of_int b)^" cl"^
		(string_of_int c)^" "^(string_of_int d)^"])\n"
|   by_isar_line ( (Para ((a,b), (c,d)))) =
    "by (rule cl"^
		(string_of_int a)^" [paramod "^(string_of_int b)^" cl"^
		(string_of_int c)^" "^(string_of_int d)^"])\n"
|   by_isar_line ((Factor ((a,b,c)))) = 
    "by (rule cl"^(string_of_int a)^" [factor "^(string_of_int b)^" "^
		(string_of_int c)^" ])\n"
(*|   by_isar_line ( (Rewrite ((a,b),(c,d)))) =
    "by (rule cl"^(string_of_int a)^" [demod "^(string_of_int b)^" "^
		(string_of_int c)^" "^(string_of_int d)^" ])\n"*)
|   by_isar_line ( (Obvious ((a,b)))) =
    "by (rule cl"^(string_of_int a)^" [obvious "^(string_of_int b)^" ])\n"

fun isar_line (numb, (step, clstrs, thmstrs))  = (have_isar_line (numb,(step,clstrs, thmstrs )))^( by_isar_line step)


fun isar_lines [] str = str
|   isar_lines (x::xs) str = isar_lines xs (str^(isar_line x))

fun last_isar_line (numb,( step, clstrs,thmstrs)) = "show \"False\"\n"^(by_isar_line step)


fun to_isar_proof (frees, xs, goalstring) =
    let val extraaxioms = get_extraaxioms xs
	val extraax_num = length extraaxioms
	val origaxioms_and_steps = Library.drop (extraax_num, xs)  
	
	val origaxioms = get_origaxioms origaxioms_and_steps
	val origax_num = length origaxioms
	val axioms_and_steps = Library.drop (origax_num + extraax_num, xs)  
	val axioms = get_axioms axioms_and_steps
	
	val steps = Library.drop (origax_num, axioms_and_steps)
	val firststeps = ReconOrderClauses.butlast steps
	val laststep = List.last steps
	val goalstring = implode(ReconOrderClauses.butlast(explode goalstring))
	
	val isar_proof = 
		("show \""^goalstring^"\"\n")^
		("proof (rule ccontr,skolemize, make_clauses) \n")^
		("fix "^(frees_to_isar_str frees)^"\n")^
		(assume_isar_extraaxioms extraaxioms)^
		(assume_isar_origaxioms origaxioms)^
		(isar_axiomlines axioms "")^
		(isar_lines firststeps "")^
		(last_isar_line laststep)^
		("qed")
	val _ = File.write (File.tmp_path (Path.basic "isar_proof_file")) isar_proof
    in
	isar_proof
    end;

(* get fix vars from axioms - all Frees *)
(* check each clause for meta-vars and /\ over them at each step*)

(*******************************************************)
(* This assumes the thm list  "numcls" is still there  *)
(* In reality, should probably label it with an        *)
(* ID number identifying the subgoal.  This could      *)
(* be passed over to the watcher, e.g.  numcls25       *)
(*******************************************************)

fun apply_res_thm str goalstring  = 
  let val tokens = #1 (lex str);
      val _ = File.append (File.tmp_path (Path.basic "apply_res_1")) 
	 ("str is: "^str^" goalstr is: "^goalstring^"\n")	
      val (frees,recon_steps) = parse_step tokens 
      val isar_str = to_isar_proof (frees, recon_steps, goalstring)
      val foo = File.write (File.tmp_path (Path.basic "apply_res_2")) isar_str
  in 
     Pretty.writeln(Pretty.str isar_str)
  end 

end;
