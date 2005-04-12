(* Get claset rules *)

fun remove_all [] rules = rules
|   remove_all (x::xs) rules = let val rules' = List.filter (not_equal x) rules
                              in
                                  remove_all xs rules'
                              end; 

fun has_name th = not((Thm.name_of_thm th)= "")

fun rule_is_fol th = let val tm = prop_of th
                     in 
                        Term.is_first_order tm
                     end


fun has_name_pair (a,b) = not_equal a "";
fun good_pair c (a,b) = not_equal b c;



val num_of_clauses = ref 0;
val clause_arr = Array.array(3500, ("empty", 0));



fun multi x 0 xlist = xlist
   |multi x n xlist = multi x (n -1 ) (x::xlist);


fun clause_numbering (name:string, cls) = let val num_of_cls = length cls
                                              val numbers = 0 upto (num_of_cls -1)
                                              val multi_name = multi name num_of_cls []
                                          in 
                                              zip multi_name numbers
                                          end;

fun stick []  = []
|   stick (x::xs)  = x@(stick xs )



fun fill_cls_array array n [] = ()
|   fill_cls_array array n (x::xs) = let val _ = Array.update (array, n,x)
                                     in
                                        fill_cls_array array (n+1) (xs)
                                     end;


   	      	    
val nc = ref (Symtab.empty : (thm list) Symtab.table)

 

fun memo_add_clauses (name:string, cls)=
                        nc := Symtab.update((name , cls), !nc);
      	       


fun memo_find_clause name = case Symtab.lookup (!nc,name) of
      	        NONE =>  []
                |SOME cls  => cls ;
      	        	

fun retr_thms ([]:MetaSimplifier.rrule list) = []
	  | retr_thms (r::rs) = (#name r, #thm r)::(retr_thms rs);

fun snds [] = []
   | snds ((x,y)::l) = y::(snds l);

fun simpset_rules_of_thy thy =
     let val simpset = simpset_of thy
	val rules = #rules(fst (rep_ss simpset))
	val thms = retr_thms (snds(Net.dest rules))
     in	thms  end;





fun not_second c (a,b)  = not_equal b c;

fun remove_all_simps [] name_rule_list:(string*thm) list = name_rule_list
|   remove_all_simps ((x:thm)::xs) (name_rule_list:(string*thm) list) = 
                              let val name_rules' = List.filter (not_second  x) name_rule_list
                              in
                                  remove_all_simps xs name_rules'
                              end; 



fun thm_is_fol (x, thm) = rule_is_fol thm


fun get_simp_metas [] = [[]]
|   get_simp_metas (x::xs) = let val metas = ResAxioms.meta_cnf_axiom x
                             in
                                 metas::(get_simp_metas xs)
                             end
                             handle THM _ => get_simp_metas xs


(* re-jig all these later as smaller functions for each bit *)
  val num_of_clauses = ref 0;
val clause_arr = Array.array(3500, ("empty", 0));
                               

fun write_out_clasimp filename = let 
                                   (****************************************)
                                   (* add claset rules to array and write out as strings *)
                                   (****************************************)
                                   val claset_rules = ResAxioms.claset_rules_of_thy (the_context())
                                   val claset = ResAxioms.clausify_classical_rules_thy (the_context())
                                   val (claset_clauses,badthms) =  claset;
                                   val clausifiable_rules = remove_all badthms claset_rules;
                                   val named_claset = List.filter has_name clausifiable_rules;
                                   val name_fol_cs = List.filter rule_is_fol  named_claset;
                                   (* length name_fol_cs is 93 *)
                                   val good_names = map Thm.name_of_thm name_fol_cs;
 
                                   (*******************************************)
                                    (* get (name, thm) pairs for claset rules *)
                                   (*******************************************)

                                   val names_rules = zip good_names name_fol_cs;
                                   
                                   val new_clasrls = (fst(ResAxioms.clausify_classical_rules name_fol_cs[]));

                                   val claset_tptp_strs = map ( map ResClause.tptp_clause) new_clasrls;

                                   (* list of lists of tptp string clauses *)
                                   val stick_clasrls =  map stick claset_tptp_strs;
                                   (* stick stick_clasrls length is 172*)

                                   val name_stick = zip good_names stick_clasrls;

                                   val cl_name_nums =map clause_numbering name_stick;
                                       
                                   val cl_long_name_nums = stick cl_name_nums;
                                   (*******************************************)
                                  (* create array and put clausename, number pairs into it *)
                                   (*******************************************)

                                        val _ = fill_cls_array clause_arr 1 cl_long_name_nums;
                                 

                                   val _= num_of_clauses := (List.length cl_long_name_nums);
                                   
                                   (*************************************)
                                   (* write claset out as tptp file      *)
                                    (*************************************)
                                  
                                    val claset_all_strs = stick stick_clasrls;
                                    val out = TextIO.openOut filename;
                                    val _=   ResLib.writeln_strs out claset_all_strs;
                                    val _= TextIO.flushOut out;
                                    val _=  TextIO.output (out,("\n \n"));
                                    val _= TextIO.flushOut out;
                                   (*val _= TextIO.closeOut out;*)

                                  (*********************)
                                  (* Get simpset rules *)
                                  (*********************)
                                  val (simpset_name_rules) =simpset_rules_of_thy (the_context());
                                  val named_simps = List.filter has_name_pair simpset_name_rules;

                                  val simp_names = map fst named_simps;
                                  val simp_rules = map snd named_simps;
                              
                                  val (simpset_cls,badthms) = ResAxioms.clausify_simpset_rules simp_rules [];
                                 (* 1137 clausif simps *)
                                  val clausifiable_simps = remove_all_simps badthms named_simps;
                                   
                                    val name_fol_simps = List.filter thm_is_fol clausifiable_simps ;
                                    val simp_names = map fst name_fol_simps;
                                    val simp_rules = map snd name_fol_simps;
                                    
                                     (* 995 of these *)
                                    (* need to get names of claset_cluases so we can make sure we've*)
                                    (* got the same ones (ie. the named ones ) as the claset rules *)
                                    (* length 1374*)
                                    val new_simps = fst(ResAxioms.clausify_simpset_rules simp_rules []);
                                    val simpset_tptp_strs = map (map ResClause.tptp_clause) new_simps;

                                    val stick_strs = map stick simpset_tptp_strs;
                                    val name_stick = zip simp_names stick_strs;

                                    val name_nums =map clause_numbering name_stick;
                                    (* length 2409*)
                                    val long_name_nums = stick name_nums;


                                    val _ =fill_cls_array clause_arr (!num_of_clauses + 1) long_name_nums;
                                    val _ =num_of_clauses := (!num_of_clauses) + (List.length long_name_nums);



                                    val tptplist =  (stick stick_strs) 


                              in 
                                   ResLib.writeln_strs out tptplist;
                                   TextIO.flushOut out;
                                   TextIO.closeOut out
                              end;

(*

 Array.sub(clause_arr,  2310);
*)
