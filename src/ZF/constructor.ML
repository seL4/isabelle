(*  Title:      ZF/constructor.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Constructor function module -- for (Co)Datatype Definitions
*)

signature CONSTRUCTOR_ARG =
  sig
  val thy          : theory             (*parent containing constructor defs*)
  val big_rec_name : string             (*name of mutually recursive set*)
  val con_ty_lists : ((string*typ*mixfix) * 
                      string * term list * term list) list list
                                        (*description of constructors*)
  end;

signature CONSTRUCTOR_RESULT =
  sig
  val con_defs   : thm list             (*definitions made in thy*)
  val case_eqns  : thm list             (*equations for case operator*)
  val free_iffs  : thm list             (*freeness rewrite rules*)
  val free_SEs   : thm list             (*freeness destruct rules*)
  val mk_free    : string -> thm        (*makes freeness theorems*)
  end;


(*Proves theorems relating to constructors*)
functor Constructor_Fun (structure Const: CONSTRUCTOR_ARG and
                      Pr : PR and Su : SU) : CONSTRUCTOR_RESULT =
let

(*1st element is the case definition; others are the constructors*)
val big_case_name = Const.big_rec_name ^ "_case";

val con_defs = get_def Const.thy big_case_name :: 
               map (get_def Const.thy o #2) (flat Const.con_ty_lists);

(** Prove the case theorem **)

(*Get the case term from its definition*)
val Const("==",_) $ big_case_tm $ _ =
    hd con_defs |> rep_thm |> #prop |> Logic.unvarify;

val (_, big_case_args) = strip_comb big_case_tm;

(*Each equation has the form 
  rec_case(f_con1,...,f_conn)(coni(args)) = f_coni(args) *)
fun mk_case_equation (((id,T,syn), name, args, prems), case_free) = 
  Ind_Syntax.mk_tprop
    (Ind_Syntax.eq_const $
      (big_case_tm $
        (list_comb (Const (Sign.intern_const (sign_of Const.thy) name,T), args))) $
      (list_comb (case_free, args)));

val case_trans = hd con_defs RS Ind_Syntax.def_trans
and split_trans = Pr.split_eq RS meta_eq_to_obj_eq RS trans;

(*Proves a single case equation.  Could use simp_tac, but it's slower!*)
fun case_tacsf con_def _ = 
  [rewtac con_def,
   rtac case_trans 1,
   REPEAT (resolve_tac [refl, split_trans, 
                        Su.case_inl RS trans, 
                        Su.case_inr RS trans] 1)];

fun prove_case_equation (arg,con_def) =
    prove_goalw_cterm [] 
        (cterm_of (sign_of Const.thy) (mk_case_equation arg))
        (case_tacsf con_def);

val con_iffs = con_defs RL [Ind_Syntax.def_swap_iff];

in
  struct
  val con_defs = con_defs

  val free_iffs = con_iffs @ 
    [Su.distinct, Su.distinct', Su.inl_iff, Su.inr_iff, Pr.pair_iff];

  val free_SEs = Ind_Syntax.mk_free_SEs con_iffs @ Su.free_SEs;

  (*Typical theorems have the form ~con1=con2, con1=con2==>False,
    con1(x)=con1(y) ==> x=y, con1(x)=con1(y) <-> x=y, etc.  *)
  fun mk_free s =
      prove_goalw Const.thy con_defs s
        (fn prems => [cut_facts_tac prems 1, 
                      fast_tac (ZF_cs addSEs free_SEs) 1]);

  val case_eqns = map prove_case_equation 
              (flat Const.con_ty_lists ~~ big_case_args ~~ tl con_defs);
  end
end;


