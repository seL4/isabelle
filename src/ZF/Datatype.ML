(*  Title:      ZF/Datatype.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

(Co)Datatype Definitions for Zermelo-Fraenkel Set Theory
*)


(*For most datatypes involving univ*)
val datatype_intrs = 
    [SigmaI, InlI, InrI,
     Pair_in_univ, Inl_in_univ, Inr_in_univ, 
     zero_in_univ, A_into_univ, nat_into_univ, UnCI];

(*Needed for mutual recursion*)
val datatype_elims = [make_elim InlD, make_elim InrD];

(*For most codatatypes involving quniv*)
val codatatype_intrs = 
    [QSigmaI, QInlI, QInrI,
     QPair_in_quniv, QInl_in_quniv, QInr_in_quniv, 
     zero_in_quniv, A_into_quniv, nat_into_quniv, UnCI];

val codatatype_elims = [make_elim QInlD, make_elim QInrD];

signature INDUCTIVE_THMS =
  sig
  val monos      : thm list		(*monotonicity of each M operator*)
  val type_intrs : thm list		(*type-checking intro rules*)
  val type_elims : thm list		(*type-checking elim rules*)
  end;

functor Data_section_Fun
 (Arg: sig include CONSTRUCTOR_ARG INDUCTIVE_I INDUCTIVE_THMS end)  
    : sig include CONSTRUCTOR_RESULT INTR_ELIM INDRULE end =
struct

structure Con = Constructor_Fun 
 	(structure Const = Arg and Pr=Standard_Prod and Su=Standard_Sum);

structure Inductive = Ind_section_Fun
   (open Arg; 
    val con_defs = Con.con_defs
    val type_intrs = Arg.type_intrs @ datatype_intrs
    val type_elims = Arg.type_elims @ datatype_elims);

open Inductive Con
end;


functor CoData_section_Fun
 (Arg: sig include CONSTRUCTOR_ARG INDUCTIVE_I INDUCTIVE_THMS end)  
    : sig include CONSTRUCTOR_RESULT INTR_ELIM COINDRULE end =
struct

structure Con = Constructor_Fun 
 	(structure Const = Arg and Pr=Quine_Prod and Su=Quine_Sum);

structure CoInductive = CoInd_section_Fun
   (open Arg; 
    val con_defs = Con.con_defs
    val type_intrs = Arg.type_intrs @ codatatype_intrs
    val type_elims = Arg.type_elims @ codatatype_elims);

open CoInductive Con
end;


(*For installing the theory section.   co is either "" or "Co"*)
fun datatype_decl co =
  let open ThyParse Ind_Syntax
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
		if dom = ""  then co ^ "data_domain rec_tms" (*default*)
		else "readtm (sign_of thy) iT " ^ dom
            val stri_name = big_rec_name ^ "_Intrnl"
            val con_names = flat (map (map (trim o #1 o #1) o snd) rec_pairs)
        in
	   (";\n\n\
            \structure " ^ stri_name ^ " =\n\
            \ let open Ind_Syntax in\n\
            \  struct\n\
            \  val _ = writeln \"" ^ co ^ 
	               "Datatype definition " ^ big_rec_name ^ "\"\n\
            \  val rec_tms\t= map (readtm (sign_of thy) iT) " ^ srec_tms ^ "\n\
            \  val dom_sum\t= " ^ sdom_sum ^ "\n\
            \  and con_ty_lists\t= read_constructs (sign_of thy)\n" 
	           ^ scons ^ "\n\
            \  val intr_tms\t= mk_all_intr_tms (rec_tms, con_ty_lists)\n\
            \  end\n\
            \ end;\n\n\
            \val thy = thy |> " ^ co ^ "Ind.add_constructs_def(" ^ 
	         mk_list (map quote rec_names) ^ ", " ^ 
                 stri_name ^ ".con_ty_lists) \n\
            \              |> " ^ co ^ "Ind.add_fp_def_i \n    (" ^ 
	       stri_name ^ ".rec_tms, " ^
               stri_name ^ ".dom_sum, " ^
               stri_name ^ ".intr_tms)"
           ,
	    "structure " ^ big_rec_name ^ " =\n\
            \  struct\n\
            \  val _ = writeln \"Proofs for " ^ co ^ 
	               "Datatype definition " ^ big_rec_name ^ "\"\n\
            \  structure Result = " ^ co ^ "Data_section_Fun\n\
            \  (open " ^ stri_name ^ "\n\
            \   val thy\t\t= thy\n\
            \   val big_rec_name\t= \"" ^ big_rec_name ^ "\"\n\
            \   val monos\t\t= " ^ monos ^ "\n\
            \   val type_intrs\t= " ^ type_intrs ^ "\n\
            \   val type_elims\t= " ^ type_elims ^ ");\n\n\
            \  val " ^ mk_list (map mk_intr_name con_names) ^ " = Result.intrs;\n\
            \  open Result\n\
            \  end\n"
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
