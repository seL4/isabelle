(*  Title: 	ZF/constructor.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Constructor function module -- for Datatype Definitions

Defines constructors and a case-style eliminator (no primitive recursion)

Features:
* least or greatest fixedpoints
* user-specified product and sum constructions
* mutually recursive datatypes
* recursion over arbitrary monotone operators
* flexible: can derive any reasonable set of introduction rules
* automatically constructs a case analysis operator (but no recursion op)
* efficient treatment of large declarations (e.g. 60 constructors)
*)

(** STILL NEEDS: some treatment of recursion **)

signature CONSTRUCTOR =
  sig
  val thy        : theory		(*parent theory*)
  val rec_specs  : (string * string * (string list * string * mixfix)list) list
                      (*recursion ops, types, domains, constructors*)
  val rec_styp	 : string		(*common type of all recursion ops*)
  val sintrs     : string list		(*desired introduction rules*)
  val monos      : thm list		(*monotonicity of each M operator*)
  val type_intrs : thm list		(*type-checking intro rules*)
  val type_elims : thm list		(*type-checking elim rules*)
  end;

signature CONSTRUCTOR_RESULT =
  sig
  val con_thy	 : theory		(*theory defining the constructors*)
  val con_defs	 : thm list		(*definitions made in con_thy*)
  val case_eqns  : thm list		(*equations for case operator*)
  val free_iffs  : thm list		(*freeness rewrite rules*)
  val free_SEs   : thm list		(*freeness destruct rules*)
  val mk_free    : string -> thm	(*makes freeness theorems*)
  end;


functor Constructor_Fun (structure Const: CONSTRUCTOR and
                      Pr : PR and Su : SU) : CONSTRUCTOR_RESULT =
struct
open Logic Const;

val dummy = writeln"Defining the constructor functions...";

val case_name = "f";		(*name for case variables*)

(** Extract basic information from arguments **)

val sign = sign_of thy;
val rdty = typ_of o read_ctyp sign;

val rec_names = map #1 rec_specs;

val dummy = assert_all Syntax.is_identifier rec_names
   (fn a => "Name of recursive set not an identifier: " ^ a);

(*Expands multiple constant declarations*)
fun flatten_consts ((names, typ, mfix) :: cs) =
      let fun mk_const name = (name, typ, mfix)
      in (map mk_const names) @ (flatten_consts cs) end
  | flatten_consts [] = [];

(*Constructors with types and arguments*)
fun mk_con_ty_list cons_pairs = 
  let fun mk_con_ty (id, st, syn) =
	  let val T = rdty st;
	      val args = mk_frees "xa" (binder_types T);
              val name = const_name id syn;
                            (* because of mixfix annotations the internal name 
                               can be different from 'id' *)
	  in (name, T, args) end;

      fun pairtypes c = flatten_consts [c];
  in map mk_con_ty (flat (map pairtypes cons_pairs))  end;

val con_ty_lists = map (mk_con_ty_list o #3) rec_specs;

(** Define the constructors **)

(*We identify 0 (the empty set) with the empty tuple*)
fun mk_tuple [] = Const("0",iT)
  | mk_tuple args = foldr1 (app Pr.pair) args;

fun mk_inject n k u = access_bal(ap Su.inl, ap Su.inr, u) n k;

val npart = length rec_names;		(*number of mutually recursive parts*)

(*Make constructor definition*)
fun mk_con_defs (kpart, con_ty_list) = 
  let val ncon = length con_ty_list	   (*number of constructors*)
      fun mk_def ((a,T,args), kcon) = (*kcon = index of this constructor*)
	  mk_defpair sign 
	     (list_comb (Const(a,T), args),
	      mk_inject npart kpart (mk_inject ncon kcon (mk_tuple args)))
  in  map mk_def (con_ty_list ~~ (1 upto ncon))  end;

(** Define the case operator **)

(*Combine split terms using case; yields the case operator for one part*)
fun call_case case_list = 
  let fun call_f (free,args) = 
          ap_split Pr.split_const free (map (#2 o dest_Free) args)
  in  fold_bal (app Su.elim) (map call_f case_list)  end;

(** Generating function variables for the case definition
    Non-identifiers (e.g. infixes) get a name of the form f_op_nnn. **)

(*Treatment of a single constructor*)
fun add_case ((a,T,args), (opno,cases)) =
    if Syntax.is_identifier a
    then (opno,   
	  (Free(case_name ^ "_" ^ a, T), args) :: cases)
    else (opno+1, 
	  (Free(case_name ^ "_op_" ^ string_of_int opno, T), args) :: cases);

(*Treatment of a list of constructors, for one part*)
fun add_case_list (con_ty_list, (opno,case_lists)) =
    let val (opno',case_list) = foldr add_case (con_ty_list, (opno,[]))
    in (opno', case_list :: case_lists) end;

(*Treatment of all parts*)
val (_, case_lists) = foldr add_case_list (con_ty_lists, (1,[]));

val big_case_typ = flat (map (map #2) con_ty_lists) ---> (iT-->iT);

val big_rec_name = space_implode "_" rec_names;

val big_case_name = big_rec_name ^ "_case";

(*The list of all the function variables*)
val big_case_args = flat (map (map #1) case_lists);

val big_case_tm = 
    list_comb (Const(big_case_name, big_case_typ), big_case_args); 

val big_case_def = 
  mk_defpair sign 
    (big_case_tm, fold_bal (app Su.elim) (map call_case case_lists)); 

(** Build the new theory **)

val axpairs =
    big_case_def :: flat (map mk_con_defs ((1 upto npart) ~~ con_ty_lists));

val const_decs = flatten_consts
		   (([big_case_name], flatten_typ sign big_case_typ, NoSyn) ::
		    (big_rec_name ins rec_names, rec_styp, NoSyn) ::
		    flat (map #3 rec_specs));

val con_thy = thy
              |> add_consts const_decs
              |> add_axioms axpairs
              |> add_thyname (big_rec_name ^ "_Constructors");

(*1st element is the case definition; others are the constructors*)
val con_defs = map (get_axiom con_thy o #1) axpairs;

(** Prove the case theorem **)

(*Each equation has the form 
  rec_case(f_con1,...,f_conn)(coni(args)) = f_coni(args) *)
fun mk_case_equation ((a,T,args), case_free) = 
  mk_tprop 
   (eq_const $ (big_case_tm $ (list_comb (Const(a,T), args)))
	     $ (list_comb (case_free, args)));

val case_trans = hd con_defs RS def_trans;

(*proves a single case equation*)
fun case_tacsf con_def _ = 
  [rewtac con_def,
   rtac case_trans 1,
   REPEAT (resolve_tac [refl, Pr.split_eq RS trans, 
			Su.case_inl RS trans, 
			Su.case_inr RS trans] 1)];

fun prove_case_equation (arg,con_def) =
    prove_term (sign_of con_thy) [] 
        (mk_case_equation arg, case_tacsf con_def);

val free_iffs = 
    map standard (con_defs RL [def_swap_iff]) @
    [Su.distinct, Su.distinct', Su.inl_iff, Su.inr_iff, Pr.pair_iff];

val free_SEs   = map (gen_make_elim [conjE,FalseE]) (free_iffs RL [iffD1]);

val free_cs = ZF_cs addSEs free_SEs;

(*Typical theorems have the form ~con1=con2, con1=con2==>False,
  con1(x)=con1(y) ==> x=y, con1(x)=con1(y) <-> x=y, etc.  *)
fun mk_free s =
    prove_goalw con_thy con_defs s
      (fn prems => [cut_facts_tac prems 1, fast_tac free_cs 1]);

val case_eqns = map prove_case_equation 
		    (flat con_ty_lists ~~ big_case_args ~~ tl con_defs);

end;


