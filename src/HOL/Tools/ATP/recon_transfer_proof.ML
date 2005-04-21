(******************)
(* complete later *)
(******************)

structure Recon_Transfer =
struct

open Recon_Parse
infixr 8 ++; infixr 7 >>; infixr 6 ||;

fun not_newline ch = not (ch = "\n");



(* Versions that include type information *)
 
fun string_of_thm thm = let val _ = set show_sorts
                                val str = Display.string_of_thm thm
                                val no_returns =List.filter not_newline (explode str)
                                val _ = reset show_sorts
                            in 
                                implode no_returns
                            end


fun thm_of_string str = let val _ = set show_sorts
                                val term = read str
                                val propterm = HOLogic.mk_Trueprop term
                                val cterm = cterm_of Mainsign propterm
                                val _ = reset show_sorts
                            in
                                assume cterm
                            end

(* check separate args in the watcher program for separating strings with a * or ; or something *)

fun clause_strs_to_string [] str = str
|   clause_strs_to_string (x::xs) str = clause_strs_to_string xs (str^x^"%")



fun thmvars_to_string [] str = str
|   thmvars_to_string (x::xs) str = thmvars_to_string xs (str^x^"%")


fun proofstep_to_string Axiom = "Axiom()"
|   proofstep_to_string  (Binary ((a,b), (c,d)))= "Binary"^"("^"("^(string_of_int a)^","^(string_of_int b)^")"^","^"("^(string_of_int c)^","^(string_of_int d)^")"^")"
|   proofstep_to_string (Factor (a,b,c)) = "Factor"^"("^(string_of_int a)^","^(string_of_int b)^","^(string_of_int c)^")"
|   proofstep_to_string  (Para ((a,b), (c,d)))= "Para"^"("^"("^(string_of_int a)^","^(string_of_int b)^")"^","^"("^(string_of_int c)^","^(string_of_int d)^")"^")"
|   proofstep_to_string  (MRR ((a,b), (c,d)))= "MRR"^"("^"("^(string_of_int a)^","^(string_of_int b)^")"^","^"("^(string_of_int c)^","^(string_of_int d)^")"^")"
|   proofstep_to_string (Rewrite((a,b),(c,d))) = "Rewrite"^"("^"("^(string_of_int a)^","^(string_of_int b)^")"^","^"("^(string_of_int c)^","^(string_of_int d)^")"^")"

fun list_to_string [] liststr = liststr
|   list_to_string (x::[]) liststr = liststr^(string_of_int x)
|   list_to_string (x::xs) liststr = list_to_string xs (liststr^(string_of_int x)^",")


fun proof_to_string (num,(step,clause_strs, thmvars)) = (string_of_int num)^(proofstep_to_string step)^"["^(clause_strs_to_string clause_strs "")^"]"^"["^(thmvars_to_string thmvars "")^"]"
 

fun proofs_to_string [] str = str
|   proofs_to_string (x::xs) str = let val newstr = proof_to_string x 
                                   in
                                       proofs_to_string xs (str^newstr)
                                   end



fun init_proofstep_to_string (num, step, clause_strs) = (string_of_int num)^" "^(proofstep_to_string step)^" "^(clause_strs_to_string clause_strs "")^" "

fun init_proofsteps_to_string [] str = str
|   init_proofsteps_to_string (x::xs) str = let val newstr = init_proofstep_to_string x 
                                   in
                                       init_proofsteps_to_string xs (str^newstr)
                                   end
  


(*** get a string representing the Isabelle ordered axioms ***)

fun origAx_to_string (num,(meta,thmvars)) =let val clause_strs = get_meta_lits_bracket meta
                                         in
                                            (string_of_int num)^"OrigAxiom()"^"["^(clause_strs_to_string clause_strs "")^"]"^"["^(thmvars_to_string thmvars "")^"]"
                                         end


fun  origAxs_to_string [] str = str
|   origAxs_to_string (x::xs) str = let val newstr = origAx_to_string x 
                                   in
                                       origAxs_to_string xs (str^newstr)
                                   end


(*** get a string representing the Isabelle ordered axioms not used in the spass proof***)

fun extraAx_to_string (num, (meta,thmvars)) = let val clause_strs = get_meta_lits_bracket meta
                                           in
                                              (string_of_int num)^"ExtraAxiom()"^"["^(clause_strs_to_string clause_strs "")^"]"^"["^(thmvars_to_string thmvars "")^"]"
                                           end



fun  extraAxs_to_string [] str = str
|   extraAxs_to_string (x::xs) str = let val newstr = extraAx_to_string x 
                                   in
                                       extraAxs_to_string xs (str^newstr)
                                   end



fun is_axiom ( num:int,Axiom, str) = true
|   is_axiom (num, _,_) = false

fun get_init_axioms xs = List.filter (is_axiom) ( xs)

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
fun there_out_of_order xs ys = (checkorder xs ys [] ([],[],[]); true) 
                               handle _ => false

fun assoc_out_of_order a [] = raise Noassoc
|   assoc_out_of_order a ((b,c)::t) = if there_out_of_order a c then b else assoc_out_of_order a t;

fun get_assoc_snds [] xs assocs= assocs
|   get_assoc_snds (x::xs) ys assocs = get_assoc_snds xs ys (assocs@[((assoc_out_of_order x ys))])




fun add_if_not_inlist [] xs newlist = newlist
|   add_if_not_inlist (y::ys) xs newlist = if (not (inlist y xs)) then 
                                      add_if_not_inlist ys xs (y::newlist)
                                        else add_if_not_inlist ys xs (newlist)

(*Flattens a list of list of strings to one string*)
fun onestr ls = String.concat (map String.concat ls);

fun thmstrings [] str = str
|   thmstrings (x::xs) str = thmstrings xs (str^(string_of_thm x))


 fun get_axioms_used proof_steps thms = let 
                                             (*val  outfile = TextIO.openOut(File.sysify_path(File.tmp_path (Path.basic "foo_ax_thmstr")))                                                                      
                                             val _ = TextIO.output (outfile, thmstring)
                                             
                                             val _ =  TextIO.closeOut outfile*)
                                            (* not sure why this is necessary again, but seems to be *)

                                            val _=  (print_mode := (Library.gen_rems (op =) (! print_mode, ["xsymbols", "symbols"])))
                                            val axioms = get_init_axioms proof_steps
                                            val step_nums = get_step_nums axioms []
                                      
                                           
                                            val clauses = make_clauses thms
                                            
                                            val vars = map thm_vars clauses
                                           
                                            val distvars = distinct (fold append vars [])
                                            val clause_terms = map prop_of clauses  
                                            val clause_frees = List.concat (map term_frees clause_terms)

                                            val frees = map lit_string_with_nums clause_frees;

                                            val distfrees = distinct frees

                                            val metas = map Meson.make_meta_clause clauses
                                            val ax_strs = map #3 axioms

                                            (* literals of -all- axioms, not just those used by spass *)
                                            val meta_strs = map get_meta_lits metas
                                           
                                            val metas_and_strs = ListPair.zip (metas,meta_strs)
                                             val  outfile = TextIO.openOut(File.sysify_path(File.tmp_path (Path.basic "foo_clauses")));                                                                       
                                             val _ = TextIO.output (outfile, onestr ax_strs)
                                             
                                             val _ =  TextIO.closeOut outfile
                                             val  outfile = TextIO.openOut(File.sysify_path(File.tmp_path (Path.basic "foo_metastrs")));                                                                       
                                             val _ = TextIO.output (outfile, onestr meta_strs)
                                             val _ =  TextIO.closeOut outfile

                                            (* get list of axioms as thms with their variables *)

                                            val ax_metas = get_assoc_snds ax_strs metas_and_strs []
                                            val ax_vars = map thm_vars ax_metas
                                            val ax_with_vars = ListPair.zip (ax_metas,ax_vars)

                                            (* get list of extra axioms as thms with their variables *)
                                            val extra_metas = add_if_not_inlist metas ax_metas []
                                            val extra_vars = map thm_vars extra_metas
                                            val extra_with_vars = if (not (extra_metas = []) ) 
                                                                  then
 									 ListPair.zip (extra_metas,extra_vars)
                                                                  else
                                                                         []

                                           (* val _=  (print_mode := (Library.gen_rems (op =) (! print_mode, ["xsymbols", "symbols"])))
                                           val  outfile = TextIO.openOut(File.sysify_path(File.tmp_path (Path.basic "foo_metas")))

                                           val _ = TextIO.output (outfile, ((thmstrings ax_metas "")))
                                           val _ =  TextIO.closeOut outfile
                                          val foo_metas =  File.sysify_path(File.tmp_path (Path.basic "foo_metas"))
                                          val foo_metas2 =   File.sysify_path(File.tmp_path (Path.basic "foo_metas2"))
                                            val execperl = Unix.execute("/usr/bin/perl", ["remchars.pl", "  <", foo_metas, "  >", foo_metas2])
                                         val infile = TextIO.openIn(File.sysify_path(File.tmp_path (Path.basic "foo_metas2")))
                                        val ax_metas_str = TextIO.inputLine (infile)
                                        val _ = TextIO.closeIn infile
                                           val _= (print_mode := (["xsymbols", "symbols"] @ ! print_mode))*)
                                           
                                         in
                                            (distfrees,distvars, extra_with_vars,ax_with_vars, (ListPair.zip (step_nums,ax_metas)))
                                         end
                                        
fun numclstr (vars, []) str = str
|   numclstr ( vars, ((num, thm)::rest)) str = let val newstr = str^(string_of_int num)^" "^(string_of_thm thm)^" "
                               in
                                   numclstr  (vars,rest) newstr
                               end

(*

val proofstr = "Did parsing on Here is a proof with depth 4, length 9 :\
\1[0:Inp] || v_P(tconst_fun(typ__da_a,tconst_bool),v_x)*+ -> v_P(tconst_fun(typ__da_a,tconst_bool),U)*.\
\3[0:Inp] || v_P(tconst_fun(typ__da_a,tconst_bool),U)*+ -> v_P(tconst_fun(typ__da_a,tconst_bool),v_x)*.\
\5[0:Inp] ||  -> v_P(tconst_fun(typ__da_a,tconst_bool),U)* v_P(tconst_fun(typ__da_a,tconst_bool),v_xa)*.\
\7[0:Inp] || v_P(tconst_fun(typ__da_a,tconst_bool),U)*+ v_P(tconst_fun(typ__da_a,tconst_bool),v_xb)* -> .\
\9[0:Fac:5.0,5.1] ||  -> v_P(tconst_fun(typ__da_a,tconst_bool),v_xa)*.\
\10[0:Res:9.0,3.0] ||  -> v_P(tconst_fun(typ__da_a,tconst_bool),v_x)*.\
\11[0:Res:10.0,1.0] ||  -> v_P(tconst_fun(typ__da_a,tconst_bool),U)*.\
\12[0:Fac:7.0,7.1] || v_P(tconst_fun(typ__da_a,tconst_bool),v_xb)* -> .\
\14[0:Res:11.0,12.0] ||  -> .\
\Formulae used in the proof :"

*)


fun addvars  c (a,b)  = (a,b,c)



(*********************************************************************)
(* Pass in spass string of proof and string version of isabelle goal *)
(* Get out reconstruction steps as a string to be sent to Isabelle   *)
(*********************************************************************)


(*


val proofstr = "Here is a proof with depth 2, length 5 :\
\1[0:Inp] ||  -> v_P(tconst_fun(typ__asc39_a,tconst_bool),U)*.\
\3[0:Inp] || v_Q(tconst_fun(typ__asc39_a,tconst_bool),U)* -> .\
\5[0:Inp] || v_P(tconst_fun(typ__asc39_a,tconst_bool),v_x)* -> v_Q(tconst_fun(typ__asc39_a,tconst_bool),v_xa).\
\7[0:Res:1.0,5.0] ||  -> v_Q(tconst_fun(typ__asc39_a,tconst_bool),v_xa)*.\
\9[0:Res:7.0,3.0] ||  -> .\
\Formulae used in the proof :"


val proofstr = "Here is a proof with depth 4, length 9 :\
\1[0:Inp] || v_P(tconst_fun(typ__asc39_a,tconst_bool),v_x)*+ -> v_P(tconst_fun(typ__asc39_a,tconst_bool),U)*.\
\3[0:Inp] || v_P(tconst_fun(typ__asc39_a,tconst_bool),U)*+ -> v_P(tconst_fun(typ__asc39_a,tconst_bool),v_x)*.\
\5[0:Inp] ||  -> v_P(tconst_fun(typ__asc39_a,tconst_bool),U)* v_P(tconst_fun(typ__asc39_a,tconst_bool),v_xa)*.\
\7[0:Inp] || v_P(tconst_fun(typ__asc39_a,tconst_bool),U)*+ v_P(tconst_fun(typ__asc39_a,tconst_bool),v_xb)* -> .\
\9[0:Fac:5.0,5.1] ||  -> v_P(tconst_fun(typ__asc39_a,tconst_bool),v_xa)*.\
\10[0:Res:9.0,3.0] ||  -> v_P(tconst_fun(typ__asc39_a,tconst_bool),v_x)*.\
\11[0:Res:10.0,1.0] ||  -> v_P(tconst_fun(typ__asc39_a,tconst_bool),U)*.\
\12[0:Fac:7.0,7.1] || v_P(tconst_fun(typ__asc39_a,tconst_bool),v_xb)* -> .\
\14[0:Res:11.0,12.0] ||  -> .\
\Formulae used in the proof :";


val thmstring = " (~ (P::'a::type => bool) (x::'a::type) | P (U::'a::type)) & (~ (P::'a::type => bool) (U::'a::type) | P (x::'a::type)) & ((P::'a::type => bool) (xa::'a::type) | P (U::'a::type)) & (~ (P::'a::type => bool) (U::'a::type) | ~ P (xb::'a::type))";

val thmstring = "(ALL xb::'a::type.   (~ (P::'a::type => bool) ((x::'a::type => 'a::type) xb) |    (Q::'a::type => bool) ((xa::'a::type => 'a::type) xb)) &   P xb & ~ Q xb)"


val thmstring ="(ALL xb::'a::type.   (~ (P::'a::type => bool) ((x::'a::type => 'a::type) xb) |    (Q::'a::type => bool) ((xa::'a::type => 'a::type) xb)) &   P xb & ~ Q xb)"

val proofstr = "Did parsing on Here is a proof with depth 2, length 5 :\
\1[0:Inp] ||  -> v_P(tconst_fun(typ__asc39_a,tconst_bool),U)*.\
\3[0:Inp] || v_Q(tconst_fun(typ__asc39_a,tconst_bool),U)* -> .\
\5[0:Inp] || v_P(tconst_fun(typ__asc39_a,tconst_bool),v_x(tconst_fun(typ__asc39_a,typ__asc39_a),U))* -> v_Q(tconst_fun(typ__asc39_a,tconst_bool),v_xa(tconst_fun(typ__asc39_a,typ__asc39_a),U)).\
\7[0:Res:1.0,5.0] ||  -> v_Q(tconst_fun(typ__asc39_a,tconst_bool),v_xa(tconst_fun(typ__asc39_a,typ__asc39_a),U))*.\
\9[0:Res:7.0,3.0] ||  -> .\
\Formulae used in the proof :";

*)

val dummy_tac = PRIMITIVE(fn thm => thm );

fun spassString_to_reconString proofstr thmstring goalstring toParent ppid thms= 
                                              let val  outfile = TextIO.openOut(File.sysify_path(File.tmp_path (Path.basic "thmstringfile")));                                        
                                                  (* val sign = sign_of_thm thm
                                                 val prems = prems_of thm
                                                 val prems_string =  concat_with_and (map (Sign.string_of_term sign) prems) "" 
                                                  val _ = warning ("thmstring is: "^thmstring);(*("thm in spassStrtoRec: "^(concat_with_and (map string_of_thm thms) "")^*)*)
                                                  val _ = TextIO.output (outfile, (" thmstring is: "^thmstring^"proofstr is: "^proofstr))
             (*val _ = TextIO.output (outfile, (("in spassStrto Reconstr")));*)
                                                  val _ =  TextIO.closeOut outfile

                                                  val tokens = #1(lex proofstr)

                                                     
                                              (***********************************)
                                              (* parse spass proof into datatype *)
                                              (***********************************)

                                                  val proof_steps1 = parse tokens
                                                  val proof_steps = just_change_space proof_steps1

                                                  val  outfile = TextIO.openOut(File.sysify_path(File.tmp_path (Path.basic "foo_parse")));                                                                                          val _ = TextIO.output (outfile, ("Did parsing on "^proofstr))
                                                  val _ =  TextIO.closeOut outfile
                                                
                                                  val  outfile = TextIO.openOut(File.sysify_path(File.tmp_path (Path.basic "foo_thmstring_at_parse")));                                                                             val _ = TextIO.output (outfile, ("Parsing for thmstring: "^thmstring))
                                                  val _ =  TextIO.closeOut outfile
                                              (************************************)
                                              (* recreate original subgoal as thm *)
                                              (************************************)
                                                
                                                  (* get axioms as correctly numbered clauses w.r.t. the Spass proof *)
                                                  (* need to get prems_of thm, then get right one of the prems, relating to whichever*)
                                                  (* subgoal this is, and turn it into meta_clauses *)
                                                  val (frees,vars,extra_with_vars ,ax_with_vars,numcls) = get_axioms_used proof_steps  thms
                                                  
                                                  (*val numcls_string = numclstr ( vars, numcls) ""*)
                                                  val  outfile = TextIO.openOut(File.sysify_path(File.tmp_path (Path.basic "foo_axiom")));                                                                            val _ = TextIO.output (outfile,"got axioms")
                                                  val _ =  TextIO.closeOut outfile
                                                    
                                              (************************************)
                                              (* translate proof                  *)
                                              (************************************)
                                                  val  outfile = TextIO.openOut(File.sysify_path(File.tmp_path (Path.basic "foo_steps")));                                                          val _ = TextIO.output (outfile, ("about to translate proof, steps: "^(init_proofsteps_to_string proof_steps "")))
                                                  val _ =  TextIO.closeOut outfile
                                                  val (newthm,proof) = translate_proof numcls  proof_steps vars
                                                  val  outfile = TextIO.openOut(File.sysify_path(File.tmp_path (Path.basic "foo_steps2")));                                                                         val _ = TextIO.output (outfile, ("translated proof, steps: "^(init_proofsteps_to_string proof_steps "")))
                                                  val _ =  TextIO.closeOut outfile
                                              (***************************************************)
                                              (* transfer necessary steps as strings to Isabelle *)
                                              (***************************************************)
                                                  (* turn the proof into a string *)
                                                  val reconProofStr = proofs_to_string proof ""
                                                  (* do the bit for the Isabelle ordered axioms at the top *)
                                                  val ax_nums = map #1 numcls
                                                  val ax_strs = map get_meta_lits_bracket (map #2 numcls)
                                                  val numcls_strs = ListPair.zip (ax_nums,ax_strs)
                                                  val num_cls_vars =  map (addvars vars) numcls_strs;
                                                  val reconIsaAxStr = origAxs_to_string (ListPair.zip (ax_nums,ax_with_vars)) ""
                                                  
                                                  val extra_nums = if (not (extra_with_vars = [])) then (1 upto (length extra_with_vars)) else []
                                                  val reconExtraAxStr = extraAxs_to_string ( ListPair.zip (extra_nums,extra_with_vars)) ""
                                                  val frees_str = "["^(thmvars_to_string frees "")^"]"
                                                  val  outfile = TextIO.openOut(File.sysify_path(File.tmp_path (Path.basic "reconstringfile")));

                                                  val _ = TextIO.output (outfile, (frees_str^reconExtraAxStr^reconIsaAxStr^reconProofStr))
                                                  val _ =  TextIO.closeOut outfile
    						  val reconstr = (frees_str^reconExtraAxStr^reconIsaAxStr^reconProofStr)
                                              in 
                                                   TextIO.output (toParent, reconstr^"\n");
                                                   TextIO.flushOut toParent;
                                        	   TextIO.output (toParent, thmstring^"\n");
                                         	   TextIO.flushOut toParent;
                                         	   TextIO.output (toParent, goalstring^"\n");
                                         	   TextIO.flushOut toParent;
                                          
                                         	   Posix.Process.kill(Posix.Process.K_PROC ppid, Posix.Signal.usr2);
                                         	  (* Attempt to prevent several signals from turning up simultaneously *)
                                         	   OS.Process.sleep(Time.fromSeconds 1) ; dummy_tac
                                              end
                                              handle _ => (let val  outfile = TextIO.openOut(File.sysify_path(File.tmp_path (Path.basic "foo_handler")));

                                                  val _ = TextIO.output (outfile, ("In exception handler"));
                                                  val _ =  TextIO.closeOut outfile
                                              in 
                                                  TextIO.output (toParent,"Proof found but translation failed!" ^"\n");
                                                  TextIO.flushOut toParent;
            					  Posix.Process.kill(Posix.Process.K_PROC ppid, Posix.Signal.usr2);
                                         	  (* Attempt to prevent several signals from turning up simultaneously *)
                                         	  OS.Process.sleep(Time.fromSeconds 1) ;dummy_tac
                                              end)









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


val rewritestep = (a (Word "Rewrite"))  ++ (a (Other "(")) ++ (a (Other "(")) 
                   ++ term_numstep  ++ (a (Other ")")) ++ (a (Other ","))
                   ++ (a (Other "(")) ++ term_numstep ++ (a (Other ")")) ++ (a (Other ")"))
            >> (fn (_, (_, (_, (c, (_,(_,(_, (e,(_,_))))))))) => Rewrite (c,e))

val obviousstep = (a (Word "Obvious")) ++ (a (Other "(")) 
                   ++ term_numstep  ++ (a (Other ")")) 
            >> (fn (_, (_, (c,_))) => Obvious (c))

 val methodstep = extraaxiomstep || origaxiomstep || axiomstep ||binarystep || factorstep|| parastep || mrrstep || rewritestep || obviousstep


 val number_list_step =
        ( number ++ many ((a (Other ",") ++ number)>> #2))
        >> (fn (a,b) => (a::b))
        
 val numberlist_step = a (Other "[")  ++ a (Other "]")
                        >>(fn (_,_) => ([]:int list))
                       || a (Other "[") ++ number_list_step ++ a (Other "]")
                        >>(fn (_,(a,_)) => a)
                    


(** change this to allow P (x U) *)
 fun arglist_step input = ( word ++ many  word >> (fn (a, b) => (a^" "^(implode_with_space b)))
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
fun change_nots [] = []
|   change_nots (x::xs) = if x = "~" 
                          then 
                             ["\\", "<", "n", "o", "t", ">"]@(change_nots xs)
                          else (x::(change_nots xs))

(*
fun clstrs_to_string [] str = str
|   clstrs_to_string (x::[]) str = str^x
|   clstrs_to_string (x::xs) str = clstrs_to_string xs (str^(x^"; "))
*)
fun clstrs_to_string [] str = implode (change_nots (explode str))
|   clstrs_to_string (x::[]) str = implode (change_nots (explode (str^x)))
|   clstrs_to_string (x::xs) str = implode (change_nots (explode (clstrs_to_string xs (str^(x^"; ")))))



fun thmvars_to_quantstring [] str = str
|   thmvars_to_quantstring (x::[]) str =str^x^". "
|   thmvars_to_quantstring (x::xs) str = thmvars_to_quantstring xs (str^(x^" "))


fun clause_strs_to_isar clstrs [] =  "\"\\<lbrakk>"^(clstrs_to_string clstrs "")^"\\<rbrakk> "^" \\<Longrightarrow> False\""
|   clause_strs_to_isar clstrs thmvars = "\"\\<And>"^(thmvars_to_quantstring thmvars "")^"\\<lbrakk>"^(clstrs_to_string clstrs "")^"\\<rbrakk> "^"\\<Longrightarrow> False\""

fun frees_to_string [] str = implode (change_nots (explode str))
|   frees_to_string (x::[]) str = implode (change_nots (explode (str^x)))
|   frees_to_string  (x::xs) str = implode (change_nots (explode (frees_to_string xs (str^(x^" ")))))

fun frees_to_isar_str [] =  ""
|   frees_to_isar_str  clstrs = (frees_to_string clstrs "")


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


fun  by_isar_line ((Binary ((a,b), (c,d))))="by(rule cl"^
                                                  (string_of_int a)^" [BINARY "^(string_of_int b)^" "^"cl"^
                                                  (string_of_int c)^" "^(string_of_int d)^"])"^"\n"
|   by_isar_line ( (Para ((a,b), (c,d)))) ="by (rule cl"^
                                                  (string_of_int a)^" [PARAMOD "^(string_of_int b)^" "^"cl"^
                                                  (string_of_int c)^" "^(string_of_int d)^"])"^"\n"
|   by_isar_line ((Factor ((a,b,c)))) =    "by (rule cl"^(string_of_int a)^" [FACTOR "^(string_of_int b)^" "^
                                                  (string_of_int c)^" "^"])"^"\n"
|   by_isar_line ( (Rewrite ((a,b),(c,d)))) =  "by (rule cl"^(string_of_int a)^" [DEMOD "^(string_of_int b)^" "^
                                                  (string_of_int c)^" "^(string_of_int d)^" "^"])"^"\n"

|   by_isar_line ( (Obvious ((a,b)))) =  "by (rule cl"^(string_of_int a)^" [OBVIOUS "^(string_of_int b)^" ])"^"\n"

fun isar_line (numb, (step, clstrs, thmstrs))  = (have_isar_line (numb,(step,clstrs, thmstrs )))^( by_isar_line step)


fun isar_lines [] str = str
|   isar_lines (x::xs) str = isar_lines xs (str^(isar_line x))

fun last_isar_line (numb,( step, clstrs,thmstrs)) = "show \"False\"\n"^(by_isar_line step)


fun to_isar_proof (frees, xs, goalstring) = let val extraaxioms = get_extraaxioms xs
                           val extraax_num = length extraaxioms
                           val origaxioms_and_steps = Library.drop (extraax_num, xs)  
                          
  
                           val origaxioms = get_origaxioms origaxioms_and_steps
                           val origax_num = length origaxioms
                           val axioms_and_steps = Library.drop (origax_num + extraax_num, xs)  
                           val axioms = get_axioms axioms_and_steps
                           
                           val steps = Library.drop (origax_num, axioms_and_steps)
                           val firststeps = butlast steps
                           val laststep = last steps
                           val goalstring = implode(butlast(explode goalstring))
                        
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
                          val  outfile = TextIO.openOut(File.sysify_path(File.tmp_path (Path.basic "isar_proof_file")));

                                                  val _ = TextIO.output (outfile, isar_proof)
                                                  val _ =  TextIO.closeOut outfile


                       in
                           isar_proof
                       end

(* get fix vars from axioms - all Frees *)
(* check each clause for meta-vars and /\ over them at each step*)

(*******************************************************)
(* This assumes the thm list  "numcls" is still there  *)
(* In reality, should probably label it with an        *)
(* ID number identifying the subgoal.  This could      *)
(* be passed over to the watcher, e.g.  numcls25       *)
(*******************************************************)

(* val str = "[S%x%P%R%Q%]1ExtraAxiom()[~ Q U%~ R U%][U%]2ExtraAxiom()[~ Q U%~ P U%][U%]3ExtraAxiom()[Q U%R U%][U%]1OrigAxiom()[S x%][]2OrigAxiom()[P U%R U%][U%]6OrigAxiom()[~ S U%~ P U%][U%]7OrigAxiom()[~ S U%~ R U%][U%]1Axiom()[S x%][]2Axiom()[R U%P U%][U%]6Axiom()[~ P U%~ S U%][U%]7Axiom()[~ R U%~ S U%][U%]8Binary((6,1),(1,0))[~ P x%][]9Binary((7,1),(1,0))[~ R x%][]19Binary((9,0),(2,0))[P x%][]25Binary((8,0),(19,0))[][]";

val str = "[P%x%xa%xb%]1OrigAxiom()[P x%~ P U%][U%]3OrigAxiom()[P U%~ P x%][U%]5OrigAxiom()[~ P xa%~ P U%][U%]7OrigAxiom()[P U%P xb%][U%]1Axiom()[P x%~ P U%][U%]3Axiom()[P U%~ P x%][U%]5Axiom()[~ P U%~ P xa%][U%]7Axiom()[P U%P xb%][U%]9Factor(5,0,1)[~ P xa%][]10Binary((9,0),(3,0))[~ P x%][]11Binary((10,0),(1,0))[~ P U%][U%]12Factor(7,0,1)[P xb%][]14Binary((11,0),(12,0))[][]";

val reconstr = "[P%Q%x%xa%]1OrigAxiom()[~ P U%][U%]3OrigAxiom()[Q U%][U%]5OrigAxiom()[P (x U)%~ Q (xa U)%][U%]9Binary((7,0),(3,0))[][]7Binary((1,0),(5,0))[~ Q (xa U)%][U%]5Axiom()[P (x U)%~ Q (xa U)%][U%]3Axiom()[Q U%][U%]1Axiom()[~ P U%][U%](ALL xb::'a::type.   (~ (P::'a::type => bool) ((x::'a::type => 'a::type) xb) |    (Q::'a::type => bool) ((xa::'a::type => 'a::type) xb)) &   P xb & ~ Q xb)";


val reconstr = "[P%x%xa%xb%]1OrigAxiom()[P x%~ P U%][U%]3OrigAxiom()[P U%~ P x%][U%]5OrigAxiom()[~ P xa%~ P U%][U%]7OrigAxiom()[P U%P xb%][U%]1Axiom()[P x%~ P U%][U%]3Axiom()[P U%~ P x%][U%]5Axiom()[~ P U%~ P xa%][U%]7Axiom()[P U%P xb%][U%]9Factor(5,0,1)[~ P xa%][]10Binary((9,0),(3,0))[~ P x%][]11Binary((10,0),(1,0))[~ P U%][U%]12Factor(7,0,1)[P xb%][]14Binary((11,0),(12,0))[][]";

val thmstring = " (ALL xa::'a::type.   (~ (P::'a::type => bool) (x::'a::type) | P xa) & (~ P xa | P x)) & (((P::'a::type => bool) (xa::'a::type) | (ALL x::'a::type. P x)) &((ALL x::'a::type. ~ P x) | ~ P (xb::'a::type)))";
*)

fun apply_res_thm str goalstring  = let val tokens = #1 (lex str);

                                   val (frees,recon_steps) = parse_step tokens 
                                   val isar_str = to_isar_proof (frees, recon_steps, goalstring)
                                   val foo =   TextIO.openOut (File.sysify_path(File.tmp_path (Path.basic "foobar")));
                               in 
                                  TextIO.output(foo,(isar_str));TextIO.closeOut foo;Pretty.writeln(Pretty.str  isar_str); () 
                               end 


end;
