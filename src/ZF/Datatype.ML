(*  Title:      ZF/Datatype.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

(Co)Datatype Definitions for Zermelo-Fraenkel Set Theory
*)


(*Typechecking rules for most datatypes involving univ*)
structure Data_Arg =
  struct
  val intrs = 
      [SigmaI, InlI, InrI,
       Pair_in_univ, Inl_in_univ, Inr_in_univ, 
       zero_in_univ, A_into_univ, nat_into_univ, UnCI];


  val elims = [make_elim InlD, make_elim InrD,   (*for mutual recursion*)
               SigmaE, sumE];                    (*allows * and + in spec*)
  end;


structure Data_Package = 
  Add_datatype_def_Fun
   (structure Fp=Lfp and Pr=Standard_Prod and CP=Standard_CP
    and Su=Standard_Sum
    and Ind_Package = Ind_Package
    and Datatype_Arg = Data_Arg
    val coind = false);


(*Typechecking rules for most codatatypes involving quniv*)
structure CoData_Arg =
  struct
  val intrs = 
      [QSigmaI, QInlI, QInrI,
       QPair_in_quniv, QInl_in_quniv, QInr_in_quniv, 
       zero_in_quniv, A_into_quniv, nat_into_quniv, UnCI];

  val elims = [make_elim QInlD, make_elim QInrD,   (*for mutual recursion*)
               QSigmaE, qsumE];                    (*allows * and + in spec*)
  end;

structure CoData_Package = 
  Add_datatype_def_Fun
   (structure Fp=Gfp and Pr=Quine_Prod and CP=Quine_CP
    and Su=Quine_Sum
    and Ind_Package = CoInd_Package
    and Datatype_Arg = CoData_Arg
    val coind = true);



(*Simproc for freeness reasoning: compare datatype constructors for equality*)
structure DataFree =
struct
  val trace = ref false;

  fun mk_new ([],[]) = Const("True",FOLogic.oT)
    | mk_new (largs,rargs) =
        fold_bal FOLogic.mk_conj
                 (map FOLogic.mk_eq (ListPair.zip (largs,rargs)));

 val datatype_ss = simpset_of (the_context ());

 fun proc sg _ old =
   let val _ = if !trace then writeln ("data_free: OLD = " ^ 
                                       string_of_cterm (cterm_of sg old))
               else ()
       val (lhs,rhs) = FOLogic.dest_eq old
       val (lhead, largs) = strip_comb lhs
       and (rhead, rargs) = strip_comb rhs
       val lname = #1 (dest_Const lhead) handle TERM _ => raise Match;
       val rname = #1 (dest_Const rhead) handle TERM _ => raise Match;
       val lcon_info = the (Symtab.lookup (ConstructorsData.get_sg sg, lname))
         handle Library.OPTION => raise Match;
       val rcon_info = the (Symtab.lookup (ConstructorsData.get_sg sg, rname))
         handle Library.OPTION => raise Match;
       val new = 
           if #big_rec_name lcon_info = #big_rec_name rcon_info 
               andalso not (null (#free_iffs lcon_info)) then
               if lname = rname then mk_new (largs, rargs)
               else Const("False",FOLogic.oT)
           else raise Match
       val _ = if !trace then 
                 writeln ("NEW = " ^ string_of_cterm (Thm.cterm_of sg new))
               else ();
       val goal = Logic.mk_equals (old, new)
       val thm = Tactic.prove sg [] [] goal (fn _ => rtac iff_reflection 1 THEN
           simp_tac (datatype_ss addsimps #free_iffs lcon_info) 1)
         handle ERROR_MESSAGE msg =>
         (warning (msg ^ "\ndata_free simproc:\nfailed to prove " ^ Sign.string_of_term sg goal);
          raise Match)
   in Some thm end
   handle Match => None;


 val conv = 
     Simplifier.simproc (Theory.sign_of ZF.thy) "data_free" ["(x::i) = y"] proc;
end;


Addsimprocs [DataFree.conv];
