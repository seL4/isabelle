(*  Title:      ZF/thy_syntax.ML
    ID:         $Id$
    Author:     Lawrence C Paulson
    Copyright   1994  University of Cambridge

Additional theory file sections for ZF
*)

structure ThySynData: THY_SYN_DATA =
struct

(*Inductive definitions theory section.   co is either "" or "Co"*)
fun inductive_decl co =
  let open ThyParse 
      fun mk_intr_name (s,_) =  (*the "op" cancels any infix status*)
	  if Syntax.is_identifier s then "op " ^ s  else "_"
      fun mk_params ((((((rec_tms, sdom_sum), ipairs), 
			monos), con_defs), type_intrs), type_elims) =
        let val big_rec_name = space_implode "_" 
		             (map (scan_to_id o trim) rec_tms)
	    and srec_tms = mk_list rec_tms
	    and sintrs   = mk_big_list (map snd ipairs)
            val stri_name = big_rec_name ^ "_Intrnl"
        in
	   (";\n\n\
            \structure " ^ stri_name ^ " =\n\
            \  struct\n\
            \  val _ = writeln \"" ^ co ^ 
	               "Inductive definition " ^ big_rec_name ^ "\"\n\
            \  val rec_tms\t= map (readtm (sign_of thy) Ind_Syntax.iT) "
	                     ^ srec_tms ^ "\n\
            \  and dom_sum\t= readtm (sign_of thy) Ind_Syntax.iT " ^ sdom_sum ^ "\n\
            \  and intr_tms\t= map (readtm (sign_of thy) propT)\n"
	                     ^ sintrs ^ "\n\
            \  end;\n\n\
            \val thy = thy |> " ^ co ^ "Ind.add_fp_def_i \n    (" ^ 
	       stri_name ^ ".rec_tms, " ^
               stri_name ^ ".dom_sum, " ^
               stri_name ^ ".intr_tms)"
           ,
	    "structure " ^ big_rec_name ^ " =\n\
            \ let\n\
            \  val _ = writeln \"Proofs for " ^ co ^ 
	               "Inductive definition " ^ big_rec_name ^ "\"\n\
            \  structure Result = " ^ co ^ "Ind_section_Fun\n\
            \\t  (open " ^ stri_name ^ "\n\
            \\t   val thy\t\t= thy\n\
            \\t   val monos\t\t= " ^ monos ^ "\n\
            \\t   val con_defs\t\t= " ^ con_defs ^ "\n\
            \\t   val type_intrs\t= " ^ type_intrs ^ "\n\
            \\t   val type_elims\t= " ^ type_elims ^ ")\n\
            \ in\n\
            \  struct\n\
            \  val " ^ mk_list (map mk_intr_name ipairs) ^ " = Result.intrs;\n\
            \  open Result\n\
            \  end\n\
            \ end;\n\n\
            \structure " ^ stri_name ^ " = struct end;\n\n"
	   )
	end
      val domains = "domains" $$-- enum1 "+" string --$$ "<=" -- !! string
      val ipairs  = "intrs"   $$-- repeat1 (ident -- !! string)
      fun optstring s = optional (s $$-- string) "\"[]\"" >> trim
  in domains -- ipairs -- optstring "monos" -- optstring "con_defs"
             -- optstring "type_intrs" -- optstring "type_elims"
     >> mk_params
  end;


(*Datatype definitions theory section.   co is either "" or "Co"*)
fun datatype_decl co =
  let open ThyParse 
      (*generate strings*)
      fun mk_const ((x, y), z) = mk_triple (x, mk_list y, z);
      val mk_data = mk_list o map mk_const o snd
      val mk_scons = mk_big_list o map mk_data
      fun mk_intr_name s =  (*the "op" cancels any infix status*)
	  if Syntax.is_identifier s then "op " ^ s ^ "_I" else "_"
      fun mk_params ((((dom, rec_pairs), monos), type_intrs), type_elims) =
        let val rec_names = map (scan_to_id o trim o fst) rec_pairs
	    val big_rec_name = space_implode "_" rec_names
	    and srec_tms = mk_list (map fst rec_pairs)
            and scons    = mk_scons rec_pairs
            and sdom_sum = 
		if dom = "" then  (*default domain: univ or quniv*)
		    "Ind_Syntax." ^ co ^ "data_domain rec_tms"
		else "readtm (sign_of thy) Ind_Syntax.iT " ^ dom
            val stri_name = big_rec_name ^ "_Intrnl"
            val con_names = flat (map (map (trim o #1 o #1) o snd) rec_pairs)
        in
	   (";\n\n\
            \structure " ^ stri_name ^ " =\n\
            \  struct\n\
            \  val _ = writeln \"" ^ co ^ 
	               "Datatype definition " ^ big_rec_name ^ "\"\n\
            \  val rec_tms\t= map (readtm (sign_of thy) Ind_Syntax.iT) " ^ srec_tms ^ "\n\
            \  val dom_sum\t= " ^ sdom_sum ^ "\n\
            \  and con_ty_lists\t= Ind_Syntax.read_constructs (sign_of thy)\n" 
	           ^ scons ^ "\n\
            \  val intr_tms\t= Ind_Syntax.mk_all_intr_tms (rec_tms, con_ty_lists)\n\
            \  end;\n\n\
            \val thy = thy |> " ^ co ^ "Ind.add_constructs_def(" ^ 
	         mk_list (map quote rec_names) ^ ", " ^ 
                 stri_name ^ ".con_ty_lists) \n\
            \              |> " ^ co ^ "Ind.add_fp_def_i \n    (" ^ 
	       stri_name ^ ".rec_tms, " ^
               stri_name ^ ".dom_sum, " ^
               stri_name ^ ".intr_tms)"
           ,
	    "structure " ^ big_rec_name ^ " =\n\
            \ let\n\
            \  val _ = writeln \"Proofs for " ^ co ^ 
	               "Datatype definition " ^ big_rec_name ^ "\"\n\
            \  structure Result = " ^ co ^ "Data_section_Fun\n\
            \\t  (open " ^ stri_name ^ "\n\
            \\t   val thy\t\t= thy\n\
            \\t   val big_rec_name\t= \"" ^ big_rec_name ^ "\"\n\
            \\t   val monos\t\t= " ^ monos ^ "\n\
            \\t   val type_intrs\t= " ^ type_intrs ^ "\n\
            \\t   val type_elims\t= " ^ type_elims ^ ");\n\
            \ in\n\
            \  struct\n\
            \  val " ^ mk_list (map mk_intr_name con_names) ^ " = Result.intrs;\n\
            \  open Result\n\
            \  end\n\
            \ end;\n\n\
            \structure " ^ stri_name ^ " = struct end;\n\n"
	   )
	end
      fun optstring s = optional (s $$-- string) "\"[]\"" >> trim
      val string_list = "(" $$-- list1 string --$$ ")" || ThyParse.empty;
      val construct = name -- string_list -- opt_mixfix;
  in optional ("<=" $$-- string) "" --
     enum1 "and" (string --$$ "=" -- enum1 "|" construct) --
     optstring "monos" -- optstring "type_intrs" -- optstring "type_elims"
     >> mk_params
end;


(** Section specifications **)

val user_keywords = ["inductive", "coinductive", "datatype", "codatatype", 
		     "and", "|", "<=", "domains", "intrs", "monos", 
		     "con_defs", "type_intrs", "type_elims"];

val user_sections = [("inductive",  inductive_decl ""),
		     ("coinductive",  inductive_decl "Co"),
		     ("datatype",  datatype_decl ""),
		     ("codatatype",  datatype_decl "Co")];
end;


structure ThySyn = ThySynFun(ThySynData);
init_thy_reader ();
