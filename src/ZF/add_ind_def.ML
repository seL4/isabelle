(*  Title: 	ZF/add_ind_def.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Fixedpoint definition module -- for Inductive/Coinductive Definitions

Features:
* least or greatest fixedpoints
* user-specified product and sum constructions
* mutually recursive definitions
* definitions involving arbitrary monotone operators
* automatically proves introduction and elimination rules

The recursive sets must *already* be declared as constants in parent theory!

  Introduction rules have the form
  [| ti:M(Sj), ..., P(x), ... |] ==> t: Sk |]
  where M is some monotone operator (usually the identity)
  P(x) is any (non-conjunctive) side condition on the free variables
  ti, t are any terms
  Sj, Sk are two of the sets being defined in mutual recursion

Sums are used only for mutual recursion;
Products are used only to derive "streamlined" induction rules for relations
*)

signature FP =		(** Description of a fixed point operator **)
  sig
  val oper	: term			(*fixed point operator*)
  val bnd_mono	: term			(*monotonicity predicate*)
  val bnd_monoI	: thm			(*intro rule for bnd_mono*)
  val subs	: thm			(*subset theorem for fp*)
  val Tarski	: thm			(*Tarski's fixed point theorem*)
  val induct	: thm			(*induction/coinduction rule*)
  end;

signature PR =			(** Description of a Cartesian product **)
  sig
  val sigma	: term			(*Cartesian product operator*)
  val pair	: term			(*pairing operator*)
  val split_const  : term		(*splitting operator*)
  val fsplit_const : term		(*splitting operator for formulae*)
  val pair_iff	: thm			(*injectivity of pairing, using <->*)
  val split_eq	: thm			(*equality rule for split*)
  val fsplitI	: thm			(*intro rule for fsplit*)
  val fsplitD	: thm			(*destruct rule for fsplit*)
  val fsplitE	: thm			(*elim rule for fsplit*)
  end;

signature SU =			(** Description of a disjoint sum **)
  sig
  val sum	: term			(*disjoint sum operator*)
  val inl	: term			(*left injection*)
  val inr	: term			(*right injection*)
  val elim	: term			(*case operator*)
  val case_inl	: thm			(*inl equality rule for case*)
  val case_inr	: thm			(*inr equality rule for case*)
  val inl_iff	: thm			(*injectivity of inl, using <->*)
  val inr_iff	: thm			(*injectivity of inr, using <->*)
  val distinct	: thm			(*distinctness of inl, inr using <->*)
  val distinct'	: thm			(*distinctness of inr, inl using <->*)
  end;

signature ADD_INDUCTIVE_DEF =
  sig 
  val add_fp_def_i : term list * term list * term list -> theory -> theory
  val add_fp_def   : (string*string) list * string list -> theory -> theory
  val add_constructs_def :
        string list * ((string*typ*mixfix) * 
                       string * term list * term list) list list ->
        theory -> theory
  end;



(*Declares functions to add fixedpoint/constructor defs to a theory*)
functor Add_inductive_def_Fun 
    (structure Fp: FP and Pr : PR and Su : SU) : ADD_INDUCTIVE_DEF =
struct
open Logic Ind_Syntax;

(*internal version*)
fun add_fp_def_i (rec_tms, domts, intr_tms) thy = 
  let
    val sign = sign_of thy;

    (*recT and rec_params should agree for all mutually recursive components*)
    val (Const(_,recT),rec_params) = strip_comb (hd rec_tms)
    and rec_hds = map head_of rec_tms;

    val rec_names = map (#1 o dest_Const) rec_hds;

    val _ = assert_all Syntax.is_identifier rec_names
       (fn a => "Name of recursive set not an identifier: " ^ a);

    val _ = assert_all (is_some o lookup_const sign) rec_names
       (fn a => "Recursive set not previously declared as constant: " ^ a);

    local (*Checking the introduction rules*)
      val intr_sets = map (#2 o rule_concl_msg sign) intr_tms;
      fun intr_ok set =
	  case head_of set of Const(a,recT) => a mem rec_names | _ => false;
    in
      val _ =  assert_all intr_ok intr_sets
	 (fn t => "Conclusion of rule does not name a recursive set: " ^ 
		  Sign.string_of_term sign t);
    end;

    val _ = assert_all is_Free rec_params
	(fn t => "Param in recursion term not a free variable: " ^
		 Sign.string_of_term sign t);

    (*** Construct the lfp definition ***)
    val mk_variant = variant (foldr add_term_names (intr_tms,[]));

    val z' = mk_variant"z" and X' = mk_variant"X" and w' = mk_variant"w";

    fun dest_tprop (Const("Trueprop",_) $ P) = P
      | dest_tprop Q = error ("Ill-formed premise of introduction rule: " ^ 
			      Sign.string_of_term sign Q);

    (*Makes a disjunct from an introduction rule*)
    fun lfp_part intr = (*quantify over rule's free vars except parameters*)
      let val prems = map dest_tprop (strip_imp_prems intr)
	  val _ = seq (fn rec_hd => seq (chk_prem rec_hd) prems) rec_hds
	  val exfrees = term_frees intr \\ rec_params
	  val zeq = eq_const $ (Free(z',iT)) $ (#1 (rule_concl intr))
      in foldr mk_exists (exfrees, fold_bal (app conj) (zeq::prems)) end;

    val dom_sum = fold_bal (app Su.sum) domts;

    (*The Part(A,h) terms -- compose injections to make h*)
    fun mk_Part (Bound 0) = Free(X',iT)	(*no mutual rec, no Part needed*)
      | mk_Part h         = Part_const $ Free(X',iT) $ Abs(w',iT,h);

    (*Access to balanced disjoint sums via injections*)
    val parts = 
	map mk_Part (accesses_bal (ap Su.inl, ap Su.inr, Bound 0) 
				  (length rec_tms));

    (*replace each set by the corresponding Part(A,h)*)
    val part_intrs = map (subst_free (rec_tms ~~ parts) o lfp_part) intr_tms;

    val lfp_abs = absfree(X', iT, 
		     mk_Collect(z', dom_sum, fold_bal (app disj) part_intrs));

    val lfp_rhs = Fp.oper $ dom_sum $ lfp_abs

    val _ = seq (fn rec_hd => deny (rec_hd occs lfp_rhs) 
			       "Illegal occurrence of recursion operator")
	     rec_hds;

    (*** Make the new theory ***)

    (*A key definition:
      If no mutual recursion then it equals the one recursive set.
      If mutual recursion then it differs from all the recursive sets. *)
    val big_rec_name = space_implode "_" rec_names;

    (*Big_rec... is the union of the mutually recursive sets*)
    val big_rec_tm = list_comb(Const(big_rec_name,recT), rec_params);

    (*The individual sets must already be declared*)
    val axpairs = map mk_defpair 
	  ((big_rec_tm, lfp_rhs) ::
	   (case parts of 
	       [_] => [] 			(*no mutual recursion*)
	     | _ => rec_tms ~~		(*define the sets as Parts*)
		    map (subst_atomic [(Free(X',iT),big_rec_tm)]) parts));

    val _ = seq (writeln o Sign.string_of_term sign o #2) axpairs
  
  in  thy |> add_defs_i axpairs  end


(*external, string-based version; needed?*)
fun add_fp_def (rec_doms, sintrs) thy = 
  let val sign = sign_of thy;
      val rec_tms = map (readtm sign iT o fst) rec_doms
      and domts   = map (readtm sign iT o snd) rec_doms
      val intr_tms = map (readtm sign propT) sintrs
  in  add_fp_def_i (rec_tms, domts, intr_tms) thy  end


(*Expects the recursive sets to have been defined already.
  con_ty_lists specifies the constructors in the form (name,prems,mixfix) *)
fun add_constructs_def (rec_names, con_ty_lists) thy = 
  let
    val _ = writeln"  Defining the constructor functions...";
    val case_name = "f";		(*name for case variables*)

    (** Define the constructors **)

    (*The empty tuple is 0*)
    fun mk_tuple [] = Const("0",iT)
      | mk_tuple args = foldr1 (app Pr.pair) args;

    fun mk_inject n k u = access_bal(ap Su.inl, ap Su.inr, u) n k;

    val npart = length rec_names;	(*total # of mutually recursive parts*)

    (*Make constructor definition; kpart is # of this mutually recursive part*)
    fun mk_con_defs (kpart, con_ty_list) = 
      let val ncon = length con_ty_list	   (*number of constructors*)
	  fun mk_def (((id,T,syn), name, args, prems), kcon) =
		(*kcon is index of constructor*)
	      mk_defpair (list_comb (Const(name,T), args),
			  mk_inject npart kpart
			  (mk_inject ncon kcon (mk_tuple args)))
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
    fun add_case (((id,T,syn), name, args, prems), (opno,cases)) =
	if Syntax.is_identifier id
	then (opno,   
	      (Free(case_name ^ "_" ^ id, T), args) :: cases)
	else (opno+1, 
	      (Free(case_name ^ "_op_" ^ string_of_int opno, T), args) :: 
	      cases)

    (*Treatment of a list of constructors, for one part*)
    fun add_case_list (con_ty_list, (opno,case_lists)) =
	let val (opno',case_list) = foldr add_case (con_ty_list, (opno,[]))
	in (opno', case_list :: case_lists) end;

    (*Treatment of all parts*)
    val (_, case_lists) = foldr add_case_list (con_ty_lists, (1,[]));

    val big_case_typ = flat (map (map (#2 o #1)) con_ty_lists) ---> (iT-->iT);

    val big_rec_name = space_implode "_" rec_names;

    val big_case_name = big_rec_name ^ "_case";

    (*The list of all the function variables*)
    val big_case_args = flat (map (map #1) case_lists);

    val big_case_tm = 
	list_comb (Const(big_case_name, big_case_typ), big_case_args); 

    val big_case_def = mk_defpair  
	(big_case_tm, fold_bal (app Su.elim) (map call_case case_lists)); 

    (** Build the new theory **)

    val const_decs =
	(big_case_name, big_case_typ, NoSyn) :: map #1 (flat con_ty_lists);

    val axpairs =
	big_case_def :: flat (map mk_con_defs ((1 upto npart) ~~ con_ty_lists))

    in  thy |> add_consts_i const_decs |> add_defs_i axpairs  end;
end;
