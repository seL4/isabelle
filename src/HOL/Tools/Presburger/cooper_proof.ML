(*  Title:      HOL/Integ/cooper_proof.ML
    ID:         $Id$
    Author:     Amine Chaieb and Tobias Nipkow, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

File containing the implementation of the proof
generation for Cooper Algorithm
*)

signature COOPER_PROOF =
sig
  val qe_Not : thm
  val qe_conjI : thm
  val qe_disjI : thm
  val qe_impI : thm
  val qe_eqI : thm
  val qe_exI : thm
  val list_to_set : typ -> term list -> term
  val qe_get_terms : thm -> term * term
  val cooper_prv : Sign.sg -> term -> term -> thm
  val proof_of_evalc : Sign.sg -> term -> thm
  val proof_of_cnnf : Sign.sg -> term -> (term -> thm) -> thm
  val proof_of_linform : Sign.sg -> string list -> term -> thm
  val proof_of_adjustcoeffeq : Sign.sg -> term -> int -> term -> thm
  val prove_elementar : Sign.sg -> string -> term -> thm
  val thm_of : Sign.sg -> (term -> (term list * (thm list -> thm))) -> term -> thm
end;

structure CooperProof : COOPER_PROOF =
struct
open CooperDec;

(*
val presburger_ss = simpset_of (theory "Presburger")
  addsimps [zdiff_def] delsimps [symmetric zdiff_def];
*)

val presburger_ss = simpset_of (theory "Presburger")
  addsimps[diff_int_def] delsimps [thm"diff_int_def_symmetric"];
val cboolT = ctyp_of (sign_of HOL.thy) HOLogic.boolT;

(*Theorems that will be used later for the proofgeneration*)

val zdvd_iff_zmod_eq_0 = thm "zdvd_iff_zmod_eq_0";
val unity_coeff_ex = thm "unity_coeff_ex";

(* Thorems for proving the adjustment of the coeffitients*)

val ac_lt_eq =  thm "ac_lt_eq";
val ac_eq_eq = thm "ac_eq_eq";
val ac_dvd_eq = thm "ac_dvd_eq";
val ac_pi_eq = thm "ac_pi_eq";

(* The logical compination of the sythetised properties*)
val qe_Not = thm "qe_Not";
val qe_conjI = thm "qe_conjI";
val qe_disjI = thm "qe_disjI";
val qe_impI = thm "qe_impI";
val qe_eqI = thm "qe_eqI";
val qe_exI = thm "qe_exI";
val qe_ALLI = thm "qe_ALLI";

(*Modulo D property for Pminusinf an Plusinf *)
val fm_modd_minf = thm "fm_modd_minf";
val not_dvd_modd_minf = thm "not_dvd_modd_minf";
val dvd_modd_minf = thm "dvd_modd_minf";

val fm_modd_pinf = thm "fm_modd_pinf";
val not_dvd_modd_pinf = thm "not_dvd_modd_pinf";
val dvd_modd_pinf = thm "dvd_modd_pinf";

(* the minusinfinity proprty*)

val fm_eq_minf = thm "fm_eq_minf";
val neq_eq_minf = thm "neq_eq_minf";
val eq_eq_minf = thm "eq_eq_minf";
val le_eq_minf = thm "le_eq_minf";
val len_eq_minf = thm "len_eq_minf";
val not_dvd_eq_minf = thm "not_dvd_eq_minf";
val dvd_eq_minf = thm "dvd_eq_minf";

(* the Plusinfinity proprty*)

val fm_eq_pinf = thm "fm_eq_pinf";
val neq_eq_pinf = thm "neq_eq_pinf";
val eq_eq_pinf = thm "eq_eq_pinf";
val le_eq_pinf = thm "le_eq_pinf";
val len_eq_pinf = thm "len_eq_pinf";
val not_dvd_eq_pinf = thm "not_dvd_eq_pinf";
val dvd_eq_pinf = thm "dvd_eq_pinf";

(*Logical construction of the Property*)
val eq_minf_conjI = thm "eq_minf_conjI";
val eq_minf_disjI = thm "eq_minf_disjI";
val modd_minf_disjI = thm "modd_minf_disjI";
val modd_minf_conjI = thm "modd_minf_conjI";

val eq_pinf_conjI = thm "eq_pinf_conjI";
val eq_pinf_disjI = thm "eq_pinf_disjI";
val modd_pinf_disjI = thm "modd_pinf_disjI";
val modd_pinf_conjI = thm "modd_pinf_conjI";

(*Cooper Backwards...*)
(*Bset*)
val not_bst_p_fm = thm "not_bst_p_fm";
val not_bst_p_ne = thm "not_bst_p_ne";
val not_bst_p_eq = thm "not_bst_p_eq";
val not_bst_p_gt = thm "not_bst_p_gt";
val not_bst_p_lt = thm "not_bst_p_lt";
val not_bst_p_ndvd = thm "not_bst_p_ndvd";
val not_bst_p_dvd = thm "not_bst_p_dvd";

(*Aset*)
val not_ast_p_fm = thm "not_ast_p_fm";
val not_ast_p_ne = thm "not_ast_p_ne";
val not_ast_p_eq = thm "not_ast_p_eq";
val not_ast_p_gt = thm "not_ast_p_gt";
val not_ast_p_lt = thm "not_ast_p_lt";
val not_ast_p_ndvd = thm "not_ast_p_ndvd";
val not_ast_p_dvd = thm "not_ast_p_dvd";

(*Logical construction of the prop*)
(*Bset*)
val not_bst_p_conjI = thm "not_bst_p_conjI";
val not_bst_p_disjI = thm "not_bst_p_disjI";
val not_bst_p_Q_elim = thm "not_bst_p_Q_elim";

(*Aset*)
val not_ast_p_conjI = thm "not_ast_p_conjI";
val not_ast_p_disjI = thm "not_ast_p_disjI";
val not_ast_p_Q_elim = thm "not_ast_p_Q_elim";

(*Cooper*)
val cppi_eq = thm "cppi_eq";
val cpmi_eq = thm "cpmi_eq";

(*Others*)
val simp_from_to = thm "simp_from_to";
val P_eqtrue = thm "P_eqtrue";
val P_eqfalse = thm "P_eqfalse";

(*For Proving NNF*)

val nnf_nn = thm "nnf_nn";
val nnf_im = thm "nnf_im";
val nnf_eq = thm "nnf_eq";
val nnf_sdj = thm "nnf_sdj";
val nnf_ncj = thm "nnf_ncj";
val nnf_nim = thm "nnf_nim";
val nnf_neq = thm "nnf_neq";
val nnf_ndj = thm "nnf_ndj";

(*For Proving term linearizition*)
val linearize_dvd = thm "linearize_dvd";
val lf_lt = thm "lf_lt";
val lf_eq = thm "lf_eq";
val lf_dvd = thm "lf_dvd";


(* ------------------------------------------------------------------------- *)
(*This function norm_zero_one  replaces the occurences of Numeral1 and Numeral0*)
(*Respectively by their abstract representation Const("1",..) and COnst("0",..)*)
(*this is necessary because the theorems use this representation.*)
(* This function should be elminated in next versions...*)
(* ------------------------------------------------------------------------- *)

fun norm_zero_one fm = case fm of
  (Const ("op *",_) $ c $ t) => 
    if c = one then (norm_zero_one t)
    else if (dest_numeral c = ~1) 
         then (Const("uminus",HOLogic.intT --> HOLogic.intT) $ (norm_zero_one t))
         else (HOLogic.mk_binop "op *" (norm_zero_one c,norm_zero_one t))
  |(node $ rest) => ((norm_zero_one node)$(norm_zero_one rest))
  |(Abs(x,T,p)) => (Abs(x,T,(norm_zero_one p)))
  |_ => fm;

(* ------------------------------------------------------------------------- *)
(*function list to Set, constructs a set containing all elements of a given list.*)
(* ------------------------------------------------------------------------- *)
fun list_to_set T1 l = let val T = (HOLogic.mk_setT T1) in 
	case l of 
		[] => Const ("{}",T)
		|(h::t) => Const("insert", T1 --> (T --> T)) $ h $(list_to_set T1 t)
		end;
		
(* ------------------------------------------------------------------------- *)
(* Returns both sides of an equvalence in the theorem*)
(* ------------------------------------------------------------------------- *)
fun qe_get_terms th = let val (_$(Const("op =",Type ("fun",[Type ("bool", []),_])) $ A $ B )) = prop_of th in (A,B) end;

(* ------------------------------------------------------------------------- *)
(* Modified version of the simple version with minimal amount of checking and postprocessing*)
(* ------------------------------------------------------------------------- *)

fun simple_prove_goal_cterm2 G tacs =
  let
    fun check None = error "prove_goal: tactic failed"
      | check (Some (thm, _)) = (case nprems_of thm of
            0 => thm
          | i => !result_error_fn thm (string_of_int i ^ " unsolved goals!"))
  in check (Seq.pull (EVERY tacs (trivial G))) end;

(*-------------------------------------------------------------*)
(*-------------------------------------------------------------*)

fun cert_Trueprop sg t = cterm_of sg (HOLogic.mk_Trueprop t);

(* ------------------------------------------------------------------------- *)
(*This function proove elementar will be used to generate proofs at runtime*)
(*It is is based on the isabelle function proove_goalw_cterm and is thought to *)
(*prove properties such as a dvd b (essentially) that are only to make at
runtime.*)
(* ------------------------------------------------------------------------- *)
fun prove_elementar sg s fm2 = case s of 
  (*"ss" like simplification with simpset*)
  "ss" =>
    let
      val ss = presburger_ss addsimps
        [zdvd_iff_zmod_eq_0,unity_coeff_ex]
      val ct =  cert_Trueprop sg fm2
    in 
      simple_prove_goal_cterm2 ct [simp_tac ss 1, TRY (simple_arith_tac 1)]
    end

  (*"bl" like blast tactic*)
  (* Is only used in the harrisons like proof procedure *)
  | "bl" =>
     let val ct = cert_Trueprop sg fm2
     in
       simple_prove_goal_cterm2 ct [blast_tac HOL_cs 1]
     end

  (*"ed" like Existence disjunctions ...*)
  (* Is only used in the harrisons like proof procedure *)
  | "ed" =>
    let
      val ex_disj_tacs =
        let
          val tac1 = EVERY[REPEAT(resolve_tac [disjI1,disjI2] 1), etac exI 1]
          val tac2 = EVERY[etac exE 1, rtac exI 1,
            REPEAT(resolve_tac [disjI1,disjI2] 1), assumption 1]
	in [rtac iffI 1,
          etac exE 1, REPEAT(EVERY[etac disjE 1, tac1]), tac1,
          REPEAT(EVERY[etac disjE 1, tac2]), tac2]
        end

      val ct = cert_Trueprop sg fm2
    in 
      simple_prove_goal_cterm2 ct ex_disj_tacs
    end

  | "fa" =>
    let val ct = cert_Trueprop sg fm2
    in simple_prove_goal_cterm2 ct [simple_arith_tac 1]
    end

  | "sa" =>
    let
      val ss = presburger_ss addsimps zadd_ac
      val ct = cert_Trueprop sg fm2
    in 
      simple_prove_goal_cterm2 ct [simp_tac ss 1, TRY (simple_arith_tac 1)]
    end
  (* like Existance Conjunction *)
  | "ec" =>
    let
      val ss = presburger_ss addsimps zadd_ac
      val ct = cert_Trueprop sg fm2
    in 
      simple_prove_goal_cterm2 ct [simp_tac ss 1, TRY (blast_tac HOL_cs 1)]
    end

  | "ac" =>
    let
      val ss = HOL_basic_ss addsimps zadd_ac
      val ct = cert_Trueprop sg fm2
    in 
      simple_prove_goal_cterm2 ct [simp_tac ss 1]
    end

  | "lf" =>
    let
      val ss = presburger_ss addsimps zadd_ac
      val ct = cert_Trueprop sg fm2
    in 
      simple_prove_goal_cterm2 ct [simp_tac ss 1, TRY (simple_arith_tac 1)]
    end;

(*=============================================================*)
(*-------------------------------------------------------------*)
(*              The new compact model                          *)
(*-------------------------------------------------------------*)
(*=============================================================*)

fun thm_of sg decomp t = 
    let val (ts,recomb) = decomp t 
    in recomb (map (thm_of sg decomp) ts) 
    end;

(*==================================================*)
(*     Compact Version for adjustcoeffeq            *)
(*==================================================*)

fun decomp_adjustcoeffeq sg x l fm = case fm of
    (Const("Not",_)$(Const("op <",_) $(Const("0",_)) $(rt as (Const ("op +", _)$(Const ("op *",_) $    c $ y ) $z )))) => 
     let  
        val m = l div (dest_numeral c) 
        val n = if (x = y) then abs (m) else 1
        val xtm = (HOLogic.mk_binop "op *" ((mk_numeral ((m div n)*l) ), x)) 
        val rs = if (x = y) 
                 then (HOLogic.mk_binrel "op <" (zero,linear_sub [] (mk_numeral n) (HOLogic.mk_binop "op +" ( xtm ,( linear_cmul n z) )))) 
                 else HOLogic.mk_binrel "op <" (zero,linear_sub [] one rt )
        val ck = cterm_of sg (mk_numeral n)
        val cc = cterm_of sg c
        val ct = cterm_of sg z
        val cx = cterm_of sg y
        val pre = prove_elementar sg "lf" 
            (HOLogic.mk_binrel "op <" (Const("0",HOLogic.intT),(mk_numeral n)))
        val th1 = (pre RS (instantiate' [] [Some ck,Some cc, Some cx, Some ct] (ac_pi_eq)))
        in ([], fn [] => [th1,(prove_elementar sg "sa" (HOLogic.mk_eq (snd (qe_get_terms th1) ,rs)))] MRS trans)
        end

  |(Const(p,_) $a $( Const ("op +", _)$(Const ("op *",_) $ 
      c $ y ) $t )) => 
   if (is_arith_rel fm) andalso (x = y) 
   then  
        let val m = l div (dest_numeral c) 
           val k = (if p = "op <" then abs(m) else m)  
           val xtm = (HOLogic.mk_binop "op *" ((mk_numeral ((m div k)*l) ), x))
           val rs = (HOLogic.mk_binrel p ((linear_cmul k a),(HOLogic.mk_binop "op +" ( xtm ,( linear_cmul k t) )))) 

           val ck = cterm_of sg (mk_numeral k)
           val cc = cterm_of sg c
           val ct = cterm_of sg t
           val cx = cterm_of sg x
           val ca = cterm_of sg a

	   in 
	case p of
	  "op <" => 
	let val pre = prove_elementar sg "lf" 
	    (HOLogic.mk_binrel "op <" (Const("0",HOLogic.intT),(mk_numeral k)))
            val th1 = (pre RS (instantiate' [] [Some ck,Some ca,Some cc, Some cx, Some ct] (ac_lt_eq)))
	in ([], fn [] => [th1,(prove_elementar sg "lf" (HOLogic.mk_eq (snd (qe_get_terms th1) ,rs)))] MRS trans)
         end

           |"op =" =>
	     let val pre = prove_elementar sg "lf" 
	    (HOLogic.Not $ (HOLogic.mk_binrel "op =" (Const("0",HOLogic.intT),(mk_numeral k))))
	         val th1 = (pre RS(instantiate' [] [Some ck,Some ca,Some cc, Some cx, Some ct] (ac_eq_eq)))
	     in ([], fn [] => [th1,(prove_elementar sg "lf" (HOLogic.mk_eq (snd (qe_get_terms th1) ,rs)))] MRS trans)
             end

             |"Divides.op dvd" =>
	       let val pre = prove_elementar sg "lf" 
	   (HOLogic.Not $ (HOLogic.mk_binrel "op =" (Const("0",HOLogic.intT),(mk_numeral k))))
                   val th1 = (pre RS (instantiate' [] [Some ck,Some ca,Some cc, Some cx, Some ct]) (ac_dvd_eq))
               in ([], fn [] => [th1,(prove_elementar sg "lf" (HOLogic.mk_eq (snd (qe_get_terms th1) ,rs)))] MRS trans)
                        
               end
              end
  else ([], fn [] => instantiate' [Some cboolT] [Some (cterm_of sg fm)] refl)

 |( Const ("Not", _) $ p) => ([p], fn [th] => th RS qe_Not)
  |( Const ("op &",_) $ p $ q) => ([p,q], fn [th1,th2] => [th1,th2] MRS qe_conjI)
  |( Const ("op |",_) $ p $ q) =>([p,q], fn [th1,th2] => [th1,th2] MRS qe_disjI)

  |_ => ([], fn [] => instantiate' [Some cboolT] [Some (cterm_of sg fm)] refl);

fun proof_of_adjustcoeffeq sg x l = thm_of sg (decomp_adjustcoeffeq sg x l);



(*==================================================*)
(*   Finding rho for modd_minusinfinity             *)
(*==================================================*)
fun rho_for_modd_minf x dlcm sg fm1 =
let
    (*Some certified Terms*)
    
   val ctrue = cterm_of sg HOLogic.true_const
   val cfalse = cterm_of sg HOLogic.false_const
   val fm = norm_zero_one fm1
  in  case fm1 of 
      (Const ("Not", _) $ (Const("op =",Type ("fun",[Type ("IntDef.int", []),_])) $ c1 $ (Const ("op +", _) $(Const ("op *",_) $ c2 $ y) $z))) => 
         if (x=y) andalso (c1= zero) andalso (c2= one) then (instantiate' [Some cboolT] [Some ctrue] (fm_modd_minf))
           else (instantiate' [Some cboolT] [Some (cterm_of sg fm)] (fm_modd_minf))

      |(Const("op =",Type ("fun",[Type ("IntDef.int", []),_])) $ c1 $(Const ("op +", _) $(Const ("op *",_) $ c2 $ y) $z)) =>
  	   if (is_arith_rel fm) andalso (x=y) andalso (c1= zero) andalso (c2= one) 
	   then (instantiate' [Some cboolT] [Some cfalse] (fm_modd_minf))
	 	 else (instantiate' [Some cboolT] [Some (cterm_of sg fm)] (fm_modd_minf)) 

      |(Const("op <",_) $ c1 $(Const ("op +", _) $(Const ("op *",_) $ pm1 $ y ) $ z )) =>
           if (y=x) andalso (c1 = zero) then 
            if (pm1 = one) then (instantiate' [Some cboolT] [Some cfalse] (fm_modd_minf)) else
	     (instantiate' [Some cboolT] [Some ctrue] (fm_modd_minf))
	    else (instantiate' [Some cboolT] [Some (cterm_of sg fm)] (fm_modd_minf))
  
      |Const ("Not",_) $ (Const("Divides.op dvd",_)$ d $ (Const ("op +",_) $ (Const ("op *",_) $ c $ y ) $ z)) => 
         if y=x then  let val cz = cterm_of sg (norm_zero_one z)
			  val fm2 = HOLogic.mk_binrel "op =" (HOLogic.mk_binop "Divides.op mod" (dlcm,d),norm_zero_one zero)
	 	      in(instantiate' [] [Some cz ] ((((prove_elementar sg "ss" fm2)) RS(((zdvd_iff_zmod_eq_0)RS sym) RS iffD1) ) RS (not_dvd_modd_minf)))
		      end
		else (instantiate' [Some cboolT] [Some (cterm_of sg fm)] (fm_modd_minf))
      |(Const("Divides.op dvd",_)$ d $ (db as (Const ("op +",_) $ (Const ("op *",_) $
      c $ y ) $ z))) => 
         if y=x then  let val cz = cterm_of sg (norm_zero_one z)
			  val fm2 = HOLogic.mk_binrel "op =" (HOLogic.mk_binop "Divides.op mod" (dlcm,d),norm_zero_one zero)
	 	      in(instantiate' [] [Some cz ] ((((prove_elementar sg "ss" fm2)) RS (((zdvd_iff_zmod_eq_0)RS sym) RS iffD1) ) RS (dvd_modd_minf)))
		      end
		else (instantiate' [Some cboolT] [Some (cterm_of sg fm)] (fm_modd_minf))
		
    
   |_ => instantiate' [Some cboolT] [Some (cterm_of sg fm)] (fm_modd_minf)
   end;	 
(*=========================================================================*)
(*=========================================================================*)
fun rho_for_eq_minf x dlcm  sg fm1 =  
   let
   val fm = norm_zero_one fm1
    in  case fm1 of 
      (Const ("Not", _) $ (Const("op =",Type ("fun",[Type ("IntDef.int", []),_])) $ c1 $ (Const ("op +", _) $(Const ("op *",_) $ c2 $ y) $z))) => 
         if  (x=y) andalso (c1=zero) andalso (c2=one) 
	   then (instantiate' [] [Some (cterm_of sg (norm_zero_one z))] (neq_eq_minf))
           else (instantiate' [Some cboolT] [Some (cterm_of sg fm)] (fm_eq_minf))

      |(Const("op =",Type ("fun",[Type ("IntDef.int", []),_])) $ c1 $(Const ("op +", _) $(Const ("op *",_) $ c2 $ y) $z)) =>
  	   if (is_arith_rel fm) andalso (x=y) andalso ((c1=zero) orelse (c1 = norm_zero_one zero)) andalso ((c2=one) orelse (c1 = norm_zero_one one))
	     then (instantiate' [] [Some (cterm_of sg (norm_zero_one z))] (eq_eq_minf))
	     else (instantiate' [Some cboolT] [Some (cterm_of sg fm)] (fm_eq_minf)) 

      |(Const("op <",_) $ c1 $(Const ("op +", _) $(Const ("op *",_) $ pm1 $ y ) $ z )) =>
           if (y=x) andalso (c1 =zero) then 
            if pm1 = one then (instantiate' [] [Some (cterm_of sg (norm_zero_one z))] (le_eq_minf)) else
	     (instantiate' [] [Some (cterm_of sg (norm_zero_one z))] (len_eq_minf))
	    else (instantiate' [Some cboolT] [Some (cterm_of sg fm)] (fm_eq_minf))
      |Const ("Not",_) $ (Const("Divides.op dvd",_)$ d $ (Const ("op +",_) $ (Const ("op *",_) $ c $ y ) $ z)) => 
         if y=x then  let val cd = cterm_of sg (norm_zero_one d)
	 		  val cz = cterm_of sg (norm_zero_one z)
	 	      in(instantiate' [] [Some cd,  Some cz] (not_dvd_eq_minf)) 
		      end

		else (instantiate' [Some cboolT] [Some (cterm_of sg fm)] (fm_eq_minf))
		
      |(Const("Divides.op dvd",_)$ d $ (Const ("op +",_) $ (Const ("op *",_) $ c $ y ) $ z)) => 
         if y=x then  let val cd = cterm_of sg (norm_zero_one d)
	 		  val cz = cterm_of sg (norm_zero_one z)
	 	      in(instantiate' [] [Some cd, Some cz ] (dvd_eq_minf))
		      end
		else (instantiate' [Some cboolT] [Some (cterm_of sg fm)] (fm_eq_minf))

      		
    |_ => (instantiate' [Some cboolT] [Some (cterm_of sg fm)] (fm_eq_minf))
 end;

(*=====================================================*)
(*=====================================================*)
(*=========== minf proofs with the compact version==========*)
fun decomp_minf_eq x dlcm sg t =  case t of
   Const ("op &",_) $ p $q => ([p,q],fn [th1,th2] => [th1,th2] MRS eq_minf_conjI)
   |Const ("op |",_) $ p $q => ([p,q],fn [th1,th2] => [th1,th2] MRS eq_minf_disjI)
   |_ => ([],fn [] => rho_for_eq_minf x dlcm sg t);

fun decomp_minf_modd x dlcm sg t = case t of
   Const ("op &",_) $ p $q => ([p,q],fn [th1,th2] => [th1,th2] MRS modd_minf_conjI)
   |Const ("op |",_) $ p $q => ([p,q],fn [th1,th2] => [th1,th2] MRS modd_minf_disjI)
   |_ => ([],fn [] => rho_for_modd_minf x dlcm sg t);

(* -------------------------------------------------------------*)
(*                    Finding rho for pinf_modd                 *)
(* -------------------------------------------------------------*)
fun rho_for_modd_pinf x dlcm sg fm1 = 
let
    (*Some certified Terms*)
    
  val ctrue = cterm_of sg HOLogic.true_const
  val cfalse = cterm_of sg HOLogic.false_const
  val fm = norm_zero_one fm1
 in  case fm1 of 
      (Const ("Not", _) $ (Const("op =",Type ("fun",[Type ("IntDef.int", []),_])) $ c1 $ (Const ("op +", _) $(Const ("op *",_) $ c2 $ y) $z))) => 
         if ((x=y) andalso (c1= zero) andalso (c2= one))
	 then (instantiate' [Some cboolT] [Some ctrue] (fm_modd_pinf))
         else (instantiate' [Some cboolT] [Some (cterm_of sg fm)] (fm_modd_pinf))

      |(Const("op =",Type ("fun",[Type ("IntDef.int", []),_])) $ c1 $(Const ("op +", _) $(Const ("op *",_) $ c2 $ y) $z)) =>
  	if ((is_arith_rel fm) andalso (x = y) andalso (c1 = zero)  andalso (c2 = one)) 
	then (instantiate' [Some cboolT] [Some cfalse] (fm_modd_pinf))
	else (instantiate' [Some cboolT] [Some (cterm_of sg fm)] (fm_modd_pinf))

      |(Const("op <",_) $ c1 $(Const ("op +", _) $(Const ("op *",_) $ pm1 $ y ) $ z )) =>
        if ((y=x) andalso (c1 = zero)) then 
          if (pm1 = one) 
	  then (instantiate' [Some cboolT] [Some ctrue] (fm_modd_pinf)) 
	  else (instantiate' [Some cboolT] [Some cfalse] (fm_modd_pinf))
	else (instantiate' [Some cboolT] [Some (cterm_of sg fm)] (fm_modd_pinf))
  
      |Const ("Not",_) $ (Const("Divides.op dvd",_)$ d $ (Const ("op +",_) $ (Const ("op *",_) $ c $ y ) $ z)) => 
         if y=x then  let val cz = cterm_of sg (norm_zero_one z)
			  val fm2 = HOLogic.mk_binrel "op =" (HOLogic.mk_binop "Divides.op mod" (dlcm,d),norm_zero_one zero)
	 	      in(instantiate' [] [Some cz ] ((((prove_elementar sg "ss" fm2)) RS(((zdvd_iff_zmod_eq_0)RS sym) RS iffD1) ) RS (not_dvd_modd_pinf)))
		      end
		else (instantiate' [Some cboolT] [Some (cterm_of sg fm)] (fm_modd_pinf))
      |(Const("Divides.op dvd",_)$ d $ (db as (Const ("op +",_) $ (Const ("op *",_) $
      c $ y ) $ z))) => 
         if y=x then  let val cz = cterm_of sg (norm_zero_one z)
			  val fm2 = HOLogic.mk_binrel "op =" (HOLogic.mk_binop "Divides.op mod" (dlcm,d),norm_zero_one zero)
	 	      in(instantiate' [] [Some cz ] ((((prove_elementar sg "ss" fm2)) RS (((zdvd_iff_zmod_eq_0)RS sym) RS iffD1) ) RS (dvd_modd_pinf)))
		      end
		else (instantiate' [Some cboolT] [Some (cterm_of sg fm)] (fm_modd_pinf))
		
    
   |_ => instantiate' [Some cboolT] [Some (cterm_of sg fm)] (fm_modd_pinf)
   end;	
(* -------------------------------------------------------------*)
(*                    Finding rho for pinf_eq                 *)
(* -------------------------------------------------------------*)
fun rho_for_eq_pinf x dlcm sg fm1 = 
  let
					val fm = norm_zero_one fm1
    in  case fm1 of 
      (Const ("Not", _) $ (Const("op =",Type ("fun",[Type ("IntDef.int", []),_])) $ c1 $ (Const ("op +", _) $(Const ("op *",_) $ c2 $ y) $z))) => 
         if  (x=y) andalso (c1=zero) andalso (c2=one) 
	   then (instantiate' [] [Some (cterm_of sg (norm_zero_one z))] (neq_eq_pinf))
           else (instantiate' [Some cboolT] [Some (cterm_of sg fm)] (fm_eq_pinf))

      |(Const("op =",Type ("fun",[Type ("IntDef.int", []),_])) $ c1 $(Const ("op +", _) $(Const ("op *",_) $ c2 $ y) $z)) =>
  	   if (is_arith_rel fm) andalso (x=y) andalso ((c1=zero) orelse (c1 = norm_zero_one zero)) andalso ((c2=one) orelse (c1 = norm_zero_one one))
	     then (instantiate' [] [Some (cterm_of sg (norm_zero_one z))] (eq_eq_pinf))
	     else (instantiate' [Some cboolT] [Some (cterm_of sg fm)] (fm_eq_pinf)) 

      |(Const("op <",_) $ c1 $(Const ("op +", _) $(Const ("op *",_) $ pm1 $ y ) $ z )) =>
           if (y=x) andalso (c1 =zero) then 
            if pm1 = one then (instantiate' [] [Some (cterm_of sg (norm_zero_one z))] (le_eq_pinf)) else
	     (instantiate' [] [Some (cterm_of sg (norm_zero_one z))] (len_eq_pinf))
	    else (instantiate' [Some cboolT] [Some (cterm_of sg fm)] (fm_eq_pinf))
      |Const ("Not",_) $ (Const("Divides.op dvd",_)$ d $ (Const ("op +",_) $ (Const ("op *",_) $ c $ y ) $ z)) => 
         if y=x then  let val cd = cterm_of sg (norm_zero_one d)
	 		  val cz = cterm_of sg (norm_zero_one z)
	 	      in(instantiate' [] [Some cd,  Some cz] (not_dvd_eq_pinf)) 
		      end

		else (instantiate' [Some cboolT] [Some (cterm_of sg fm)] (fm_eq_pinf))
		
      |(Const("Divides.op dvd",_)$ d $ (Const ("op +",_) $ (Const ("op *",_) $ c $ y ) $ z)) => 
         if y=x then  let val cd = cterm_of sg (norm_zero_one d)
	 		  val cz = cterm_of sg (norm_zero_one z)
	 	      in(instantiate' [] [Some cd, Some cz ] (dvd_eq_pinf))
		      end
		else (instantiate' [Some cboolT] [Some (cterm_of sg fm)] (fm_eq_pinf))

      		
    |_ => (instantiate' [Some cboolT] [Some (cterm_of sg fm)] (fm_eq_pinf))
 end;



fun  minf_proof_of_c sg x dlcm t =
  let val minf_eqth   = thm_of sg (decomp_minf_eq x dlcm sg) t
      val minf_moddth = thm_of sg (decomp_minf_modd x dlcm sg) t
  in (minf_eqth, minf_moddth)
end;

(*=========== pinf proofs with the compact version==========*)
fun decomp_pinf_eq x dlcm sg t = case t of
   Const ("op &",_) $ p $q => ([p,q],fn [th1,th2] => [th1,th2] MRS eq_pinf_conjI)
   |Const ("op |",_) $ p $q => ([p,q],fn [th1,th2] => [th1,th2] MRS eq_pinf_disjI)
   |_ =>([],fn [] => rho_for_eq_pinf x dlcm sg t) ;

fun decomp_pinf_modd x dlcm sg t =  case t of
   Const ("op &",_) $ p $q => ([p,q],fn [th1,th2] => [th1,th2] MRS modd_pinf_conjI)
   |Const ("op |",_) $ p $q => ([p,q],fn [th1,th2] => [th1,th2] MRS modd_pinf_disjI)
   |_ => ([],fn [] => rho_for_modd_pinf x dlcm sg t);

fun  pinf_proof_of_c sg x dlcm t =
  let val pinf_eqth   = thm_of sg (decomp_pinf_eq x dlcm sg) t
      val pinf_moddth = thm_of sg (decomp_pinf_modd x dlcm sg) t
  in (pinf_eqth,pinf_moddth)
end;


(* ------------------------------------------------------------------------- *)
(* Here we generate the theorem for the Bset Property in the simple direction*)
(* It is just an instantiation*)
(* ------------------------------------------------------------------------- *)
(*
fun bsetproof_of sg (x as Free(xn,xT)) fm bs dlcm   = 
  let
    val cp = cterm_of sg (absfree (xn,xT,(norm_zero_one fm)))
    val cdlcm = cterm_of sg dlcm
    val cB = cterm_of sg (list_to_set HOLogic.intT (map norm_zero_one bs))
  in instantiate' [] [Some cdlcm,Some cB, Some cp] (bst_thm)
end;

fun asetproof_of sg (x as Free(xn,xT)) fm ast dlcm = 
  let
    val cp = cterm_of sg (absfree (xn,xT,(norm_zero_one fm)))
    val cdlcm = cterm_of sg dlcm
    val cA = cterm_of sg (list_to_set HOLogic.intT (map norm_zero_one ast))
  in instantiate' [] [Some cdlcm,Some cA, Some cp] (ast_thm)
end;
*)

(* For the generation of atomic Theorems*)
(* Prove the premisses on runtime and then make RS*)
(* ------------------------------------------------------------------------- *)

(*========= this is rho ============*)
fun generate_atomic_not_bst_p sg (x as Free(xn,xT)) fm dlcm B at = 
  let
    val cdlcm = cterm_of sg dlcm
    val cB = cterm_of sg B
    val cfma = cterm_of sg (absfree (xn,xT,(norm_zero_one fm)))
    val cat = cterm_of sg (norm_zero_one at)
  in
  case at of 
   (Const ("Not", _) $ (Const("op =",Type ("fun",[Type ("IntDef.int", []),_])) $ c1 $ (Const ("op +", _) $(Const ("op *",_) $ c2 $ y) $z))) => 
      if  (x=y) andalso (c1=zero) andalso (c2=one) 
	 then let val th1 = prove_elementar sg "ss" (Const ("op :",HOLogic.intT --> (HOLogic.mk_setT HOLogic.intT) --> HOLogic.boolT) $ (norm_zero_one (linear_cmul ~1 z)) $ B)
	          val th2 =  prove_elementar sg "ss" (HOLogic.mk_eq ((norm_zero_one (linear_cmul ~1 z)),Const("uminus",HOLogic.intT --> HOLogic.intT) $(norm_zero_one  z)))
		  val th3 = prove_elementar sg "ss" (HOLogic.mk_binrel "op <" (Const("0",HOLogic.intT),dlcm))
	 in  (instantiate' [] [Some cfma]([th3,th1,th2] MRS (not_bst_p_ne)))
	 end
         else (instantiate' [] [Some cfma,  Some cdlcm, Some cB,Some cat] (not_bst_p_fm))

   |(Const("op =",Type ("fun",[Type ("IntDef.int", []),_])) $ c1 $(Const ("op +", T) $(Const ("op *",_) $ c2 $ y) $z)) =>
     if (is_arith_rel at) andalso (x=y)
	then let val bst_z = norm_zero_one (linear_neg (linear_add [] z (mk_numeral 1)))
	         in let val th1 = prove_elementar sg "ss" (Const ("op :",HOLogic.intT --> (HOLogic.mk_setT HOLogic.intT) --> HOLogic.boolT) $ bst_z $ B)
	          val th2 =  prove_elementar sg "ss" (HOLogic.mk_eq (bst_z,Const("op -",T) $ (Const("uminus",HOLogic.intT --> HOLogic.intT) $(norm_zero_one z)) $ (Const("1",HOLogic.intT))))
		  val th3 = prove_elementar sg "ss" (HOLogic.mk_binrel "op <" (Const("0",HOLogic.intT),dlcm))
	 in  (instantiate' [] [Some cfma] ([th3,th1,th2] MRS (not_bst_p_eq)))
	 end
       end
         else (instantiate' [] [Some cfma,  Some cdlcm, Some cB,Some cat] (not_bst_p_fm))

   |(Const("op <",_) $ c1 $(Const ("op +", _) $(Const ("op *",_) $ pm1 $ y ) $ z )) =>
        if (y=x) andalso (c1 =zero) then 
        if pm1 = one then 
	  let val th1 = prove_elementar sg "ss" (Const ("op :",HOLogic.intT --> (HOLogic.mk_setT HOLogic.intT) --> HOLogic.boolT) $ (norm_zero_one (linear_cmul ~1 z)) $ B)
              val th2 =  prove_elementar sg "ss" (HOLogic.mk_eq ((norm_zero_one (linear_cmul ~1 z)),Const("uminus",HOLogic.intT --> HOLogic.intT) $(norm_zero_one z)))
	  in  (instantiate' [] [Some cfma,  Some cdlcm]([th1,th2] MRS (not_bst_p_gt)))
	    end
	 else let val th1 = prove_elementar sg "ss" (HOLogic.mk_binrel "op <" (Const("0",HOLogic.intT),dlcm))
	      in (instantiate' [] [Some cfma, Some cB,Some (cterm_of sg (norm_zero_one z))] (th1 RS (not_bst_p_lt)))
	      end
      else (instantiate' [] [Some cfma,  Some cdlcm, Some cB,Some cat] (not_bst_p_fm))

   |Const ("Not",_) $ (Const("Divides.op dvd",_)$ d $ (Const ("op +",_) $ (Const ("op *",_) $ c $ y ) $ z)) => 
      if y=x then  
           let val cz = cterm_of sg (norm_zero_one z)
	       val th1 = (prove_elementar sg "ss"  (HOLogic.mk_binrel "op =" (HOLogic.mk_binop "Divides.op mod" (dlcm,d),norm_zero_one zero))) RS (((zdvd_iff_zmod_eq_0)RS sym) RS iffD1)
 	     in (instantiate' []  [Some cfma, Some cB,Some cz] (th1 RS (not_bst_p_ndvd)))
	     end
      else (instantiate' [] [Some cfma,  Some cdlcm, Some cB,Some cat] (not_bst_p_fm))

   |(Const("Divides.op dvd",_)$ d $ (Const ("op +",_) $ (Const ("op *",_) $ c $ y ) $ z)) => 
       if y=x then  
	 let val cz = cterm_of sg (norm_zero_one z)
	     val th1 = (prove_elementar sg "ss"  (HOLogic.mk_binrel "op =" (HOLogic.mk_binop "Divides.op mod" (dlcm,d),norm_zero_one zero))) RS (((zdvd_iff_zmod_eq_0)RS sym) RS iffD1)
 	    in (instantiate' []  [Some cfma,Some cB,Some cz] (th1 RS (not_bst_p_dvd)))
	  end
      else (instantiate' [] [Some cfma,  Some cdlcm, Some cB,Some cat] (not_bst_p_fm))
      		
   |_ => (instantiate' [] [Some cfma,  Some cdlcm, Some cB,Some cat] (not_bst_p_fm))
      		
    end;
    

(* ------------------------------------------------------------------------- *)    
(* Main interpretation function for this backwards dirction*)
(* if atomic do generate atomis formulae else Construct theorems and then make RS with the construction theorems*)
(*Help Function*)
(* ------------------------------------------------------------------------- *)

(*==================== Proof with the compact version   *)

fun decomp_nbstp sg x dlcm B fm t = case t of 
   Const("op &",_) $ ls $ rs => ([ls,rs],fn [th1,th2] => [th1,th2] MRS not_bst_p_conjI )
  |Const("op |",_) $ ls $ rs => ([ls,rs],fn [th1,th2] => [th1,th2] MRS not_bst_p_disjI)
  |_ => ([], fn [] => generate_atomic_not_bst_p sg x fm dlcm B t);

fun not_bst_p_proof_of_c sg (x as Free(xn,xT)) fm dlcm B t =
  let 
       val th =  thm_of sg (decomp_nbstp sg x dlcm (list_to_set xT (map norm_zero_one B)) fm) t
      val fma = absfree (xn,xT, norm_zero_one fm)
  in let val th1 =  prove_elementar sg "ss"  (HOLogic.mk_eq (fma,fma))
     in [th,th1] MRS (not_bst_p_Q_elim)
     end
  end;


(* ------------------------------------------------------------------------- *)    
(* Protokol interpretation function for the backwards direction for cooper's Theorem*)

(* For the generation of atomic Theorems*)
(* Prove the premisses on runtime and then make RS*)
(* ------------------------------------------------------------------------- *)
(*========= this is rho ============*)
fun generate_atomic_not_ast_p sg (x as Free(xn,xT)) fm dlcm A at = 
  let
    val cdlcm = cterm_of sg dlcm
    val cA = cterm_of sg A
    val cfma = cterm_of sg (absfree (xn,xT,(norm_zero_one fm)))
    val cat = cterm_of sg (norm_zero_one at)
  in
  case at of 
   (Const ("Not", _) $ (Const("op =",Type ("fun",[Type ("IntDef.int", []),_])) $ c1 $ (Const ("op +", _) $(Const ("op *",_) $ c2 $ y) $z))) => 
      if  (x=y) andalso (c1=zero) andalso (c2=one) 
	 then let val th1 = prove_elementar sg "ss" (Const ("op :",HOLogic.intT --> (HOLogic.mk_setT HOLogic.intT) --> HOLogic.boolT) $ (norm_zero_one (linear_cmul ~1 z)) $ A)
	          val th2 =  prove_elementar sg "ss" (HOLogic.mk_eq ((norm_zero_one (linear_cmul ~1 z)),Const("uminus",HOLogic.intT --> HOLogic.intT) $(norm_zero_one  z)))
		  val th3 = prove_elementar sg "ss" (HOLogic.mk_binrel "op <" (Const("0",HOLogic.intT),dlcm))
	 in  (instantiate' [] [Some cfma]([th3,th1,th2] MRS (not_ast_p_ne)))
	 end
         else (instantiate' [] [Some cfma,  Some cdlcm, Some cA,Some cat] (not_ast_p_fm))

   |(Const("op =",Type ("fun",[Type ("IntDef.int", []),_])) $ c1 $(Const ("op +", T) $(Const ("op *",_) $ c2 $ y) $z)) =>
     if (is_arith_rel at) andalso (x=y)
	then let val ast_z = norm_zero_one (linear_sub [] one z )
	         val th1 = prove_elementar sg "ss" (Const ("op :",HOLogic.intT --> (HOLogic.mk_setT HOLogic.intT) --> HOLogic.boolT) $ ast_z $ A)
	         val th2 =  prove_elementar sg "ss" (HOLogic.mk_eq (ast_z,Const("op +",T) $ (Const("uminus",HOLogic.intT --> HOLogic.intT) $(norm_zero_one z)) $ (Const("1",HOLogic.intT))))
		 val th3 = prove_elementar sg "ss" (HOLogic.mk_binrel "op <" (Const("0",HOLogic.intT),dlcm))
	 in  (instantiate' [] [Some cfma] ([th3,th1,th2] MRS (not_ast_p_eq)))
       end
         else (instantiate' [] [Some cfma,  Some cdlcm, Some cA,Some cat] (not_ast_p_fm))

   |(Const("op <",_) $ c1 $(Const ("op +", _) $(Const ("op *",_) $ pm1 $ y ) $ z )) =>
        if (y=x) andalso (c1 =zero) then 
        if pm1 = (mk_numeral ~1) then 
	  let val th1 = prove_elementar sg "ss" (Const ("op :",HOLogic.intT --> (HOLogic.mk_setT HOLogic.intT) --> HOLogic.boolT) $ (norm_zero_one z) $ A)
              val th2 =  prove_elementar sg "ss" (HOLogic.mk_binrel "op <" (zero,dlcm))
	  in  (instantiate' [] [Some cfma]([th2,th1] MRS (not_ast_p_lt)))
	    end
	 else let val th1 = prove_elementar sg "ss" (HOLogic.mk_binrel "op <" (Const("0",HOLogic.intT),dlcm))
	      in (instantiate' [] [Some cfma, Some cA,Some (cterm_of sg (norm_zero_one z))] (th1 RS (not_ast_p_gt)))
	      end
      else (instantiate' [] [Some cfma,  Some cdlcm, Some cA,Some cat] (not_ast_p_fm))

   |Const ("Not",_) $ (Const("Divides.op dvd",_)$ d $ (Const ("op +",_) $ (Const ("op *",_) $ c $ y ) $ z)) => 
      if y=x then  
           let val cz = cterm_of sg (norm_zero_one z)
	       val th1 = (prove_elementar sg "ss"  (HOLogic.mk_binrel "op =" (HOLogic.mk_binop "Divides.op mod" (dlcm,d),norm_zero_one zero))) RS (((zdvd_iff_zmod_eq_0)RS sym) RS iffD1)
 	     in (instantiate' []  [Some cfma, Some cA,Some cz] (th1 RS (not_ast_p_ndvd)))
	     end
      else (instantiate' [] [Some cfma,  Some cdlcm, Some cA,Some cat] (not_ast_p_fm))

   |(Const("Divides.op dvd",_)$ d $ (Const ("op +",_) $ (Const ("op *",_) $ c $ y ) $ z)) => 
       if y=x then  
	 let val cz = cterm_of sg (norm_zero_one z)
	     val th1 = (prove_elementar sg "ss"  (HOLogic.mk_binrel "op =" (HOLogic.mk_binop "Divides.op mod" (dlcm,d),norm_zero_one zero))) RS (((zdvd_iff_zmod_eq_0)RS sym) RS iffD1)
 	    in (instantiate' []  [Some cfma,Some cA,Some cz] (th1 RS (not_ast_p_dvd)))
	  end
      else (instantiate' [] [Some cfma,  Some cdlcm, Some cA,Some cat] (not_ast_p_fm))
      		
   |_ => (instantiate' [] [Some cfma,  Some cdlcm, Some cA,Some cat] (not_ast_p_fm))
      		
    end;

(* ------------------------------------------------------------------------ *)
(* Main interpretation function for this backwards dirction*)
(* if atomic do generate atomis formulae else Construct theorems and then make RS with the construction theorems*)
(*Help Function*)
(* ------------------------------------------------------------------------- *)

fun decomp_nastp sg x dlcm A fm t = case t of 
   Const("op &",_) $ ls $ rs => ([ls,rs],fn [th1,th2] => [th1,th2] MRS not_ast_p_conjI )
  |Const("op |",_) $ ls $ rs => ([ls,rs],fn [th1,th2] => [th1,th2] MRS not_ast_p_disjI)
  |_ => ([], fn [] => generate_atomic_not_ast_p sg x fm dlcm A t);

fun not_ast_p_proof_of_c sg (x as Free(xn,xT)) fm dlcm A t =
  let 
       val th =  thm_of sg (decomp_nastp sg x dlcm (list_to_set xT (map norm_zero_one A)) fm) t
      val fma = absfree (xn,xT, norm_zero_one fm)
  in let val th1 =  prove_elementar sg "ss"  (HOLogic.mk_eq (fma,fma))
     in [th,th1] MRS (not_ast_p_Q_elim)
     end
  end;


(* -------------------------------*)
(* Finding rho and beta for evalc *)
(* -------------------------------*)

fun rho_for_evalc sg at = case at of  
    (Const (p,_) $ s $ t) =>(  
    case assoc (operations,p) of 
        Some f => 
           ((if (f ((dest_numeral s),(dest_numeral t))) 
             then prove_elementar sg "ss" (HOLogic.mk_eq(at,HOLogic.true_const)) 
             else prove_elementar sg "ss" (HOLogic.mk_eq(at, HOLogic.false_const)))  
		   handle _ => instantiate' [Some cboolT] [Some (cterm_of sg at)] refl
        | _ => instantiate' [Some cboolT] [Some (cterm_of sg at)] refl )) 
     |Const("Not",_)$(Const (p,_) $ s $ t) =>(  
       case assoc (operations,p) of 
         Some f => 
           ((if (f ((dest_numeral s),(dest_numeral t))) 
             then prove_elementar sg "ss" (HOLogic.mk_eq(at, HOLogic.false_const))  
             else prove_elementar sg "ss" (HOLogic.mk_eq(at,HOLogic.true_const)))  
		      handle _ => instantiate' [Some cboolT] [Some (cterm_of sg at)] refl) 
         | _ => instantiate' [Some cboolT] [Some (cterm_of sg at)] refl ) 
     | _ =>   instantiate' [Some cboolT] [Some (cterm_of sg at)] refl;


(*=========================================================*)
fun decomp_evalc sg t = case t of
   (Const("op &",_)$A$B) => ([A,B], fn [th1,th2] => [th1,th2] MRS qe_conjI)
   |(Const("op |",_)$A$B) => ([A,B], fn [th1,th2] => [th1,th2] MRS qe_disjI)
   |(Const("op -->",_)$A$B) => ([A,B], fn [th1,th2] => [th1,th2] MRS qe_impI)
   |(Const("op =", Type ("fun",[Type ("bool", []),_]))$A$B) => ([A,B], fn [th1,th2] => [th1,th2] MRS qe_eqI)
   |_ => ([], fn [] => rho_for_evalc sg t);


fun proof_of_evalc sg fm = thm_of sg (decomp_evalc sg) fm;

(*==================================================*)
(*     Proof of linform with the compact model      *)
(*==================================================*)


fun decomp_linform sg vars t = case t of
   (Const("op &",_)$A$B) => ([A,B], fn [th1,th2] => [th1,th2] MRS qe_conjI)
   |(Const("op |",_)$A$B) => ([A,B], fn [th1,th2] => [th1,th2] MRS qe_disjI)
   |(Const("op -->",_)$A$B) => ([A,B], fn [th1,th2] => [th1,th2] MRS qe_impI)
   |(Const("op =", Type ("fun",[Type ("bool", []),_]))$A$B) => ([A,B], fn [th1,th2] => [th1,th2] MRS qe_eqI)
   |(Const("Not",_)$p) => ([p],fn [th] => th RS qe_Not)
   |(Const("Divides.op dvd",_)$d$r) => ([], fn [] => (prove_elementar sg "lf" (HOLogic.mk_eq (r, lint vars r))) RS (instantiate' [] [None , None, Some (cterm_of sg d)](linearize_dvd)))
   |_ => ([], fn [] => prove_elementar sg "lf" (HOLogic.mk_eq (t, linform vars t)));

fun proof_of_linform sg vars f = thm_of sg (decomp_linform sg vars) f;

(* ------------------------------------------------------------------------- *)
(* Interpretaion of Protocols of the cooper procedure : minusinfinity version*)
(* ------------------------------------------------------------------------- *)
fun coopermi_proof_of sg (x as Free(xn,xT)) fm B dlcm =
  (* Get the Bset thm*)
  let val (minf_eqth, minf_moddth) = minf_proof_of_c sg x dlcm fm 
      val dpos = prove_elementar sg "ss" (HOLogic.mk_binrel "op <" (zero,dlcm));
      val nbstpthm = not_bst_p_proof_of_c sg x fm dlcm B fm
  in (dpos,minf_eqth,nbstpthm,minf_moddth)
end;

(* ------------------------------------------------------------------------- *)
(* Interpretaion of Protocols of the cooper procedure : plusinfinity version *)
(* ------------------------------------------------------------------------- *)
fun cooperpi_proof_of sg (x as Free(xn,xT)) fm A dlcm =
  let val (pinf_eqth,pinf_moddth) = pinf_proof_of_c sg x dlcm fm
      val dpos = prove_elementar sg "ss" (HOLogic.mk_binrel "op <" (zero,dlcm));
      val nastpthm = not_ast_p_proof_of_c sg x fm dlcm A fm
  in (dpos,pinf_eqth,nastpthm,pinf_moddth)
end;

(* ------------------------------------------------------------------------- *)
(* Interpretaion of Protocols of the cooper procedure : full version*)
(* ------------------------------------------------------------------------- *)
fun cooper_thm sg s (x as Free(xn,xT)) cfm dlcm ast bst= case s of
  "pi" => let val (dpsthm,pinf_eqth,nbpth,pinf_moddth) = cooperpi_proof_of sg x cfm ast dlcm 
	      in [dpsthm,pinf_eqth,nbpth,pinf_moddth] MRS (cppi_eq)
           end
  |"mi" => let val (dpsthm,minf_eqth,nbpth,minf_moddth) = coopermi_proof_of sg x cfm bst dlcm
	       in [dpsthm,minf_eqth,nbpth,minf_moddth] MRS (cpmi_eq)
                end
 |_ => error "parameter error";

(* ------------------------------------------------------------------------- *)
(* This function should evoluate to the end prove Procedure for one quantifier elimination for Presburger arithmetic*)
(* It shoud be plugged in the qfnp argument of the quantifier elimination proof function*)
(* ------------------------------------------------------------------------- *)

fun cooper_prv sg (x as Free(xn,xT)) efm = let 
   (* lfm_thm : efm = linearized form of efm*)
   val lfm_thm = proof_of_linform sg [xn] efm
   (*efm2 is the linearized form of efm *) 
   val efm2 = snd(qe_get_terms lfm_thm)
   (* l is the lcm of all coefficients of x *)
   val l = formlcm x efm2
   (*ac_thm: efm = efm2 with adjusted coefficients of x *)
   val ac_thm = [lfm_thm , (proof_of_adjustcoeffeq sg x l efm2)] MRS trans
   (* fm is efm2 with adjusted coefficients of x *)
   val fm = snd (qe_get_terms ac_thm)
  (* cfm is l dvd x & fm' where fm' is fm where l*x is replaced by x*)
   val  cfm = unitycoeff x fm
   (*afm is fm where c*x is replaced by 1*x or -1*x *)
   val afm = adjustcoeff x l fm
   (* P = %x.afm*)
   val P = absfree(xn,xT,afm)
   (* This simpset allows the elimination of the sets in bex {1..d} *)
   val ss = presburger_ss addsimps
     [simp_from_to] delsimps [P_eqtrue, P_eqfalse, bex_triv, insert_iff]
   (* uth : EX x.P(l*x) = EX x. l dvd x & P x*)
   val uth = instantiate' [] [Some (cterm_of sg P) , Some (cterm_of sg (mk_numeral l))] (unity_coeff_ex)
   (* e_ac_thm : Ex x. efm = EX x. fm*)
   val e_ac_thm = (forall_intr (cterm_of sg x) ac_thm) COMP (qe_exI)
   (* A and B set of the formula*)
   val A = aset x cfm
   val B = bset x cfm
   (* the divlcm (delta) of the formula*)
   val dlcm = mk_numeral (divlcm x cfm)
   (* Which set is smaller to generate the (hoepfully) shorter proof*)
   val cms = if ((length A) < (length B )) then "pi" else "mi"
   (* synthesize the proof of cooper's theorem*)
    (* cp_thm: EX x. cfm = Q*)
   val cp_thm = cooper_thm sg cms x cfm dlcm A B
   (* Exxpand the right hand side to get rid of EX j : {1..d} to get a huge disjunction*)
   (* exp_cp_thm: EX x.cfm = Q' , where Q' is a simplified version of Q*)
   val exp_cp_thm = refl RS (simplify ss (cp_thm RSN (2,trans)))
   (* lsuth = EX.P(l*x) ; rsuth = EX x. l dvd x & P x*)
   val (lsuth,rsuth) = qe_get_terms (uth)
   (* lseacth = EX x. efm; rseacth = EX x. fm*)
   val (lseacth,rseacth) = qe_get_terms(e_ac_thm)
   (* lscth = EX x. cfm; rscth = Q' *)
   val (lscth,rscth) = qe_get_terms (exp_cp_thm)
   (* u_c_thm: EX x. P(l*x) = Q'*)
   val  u_c_thm = [([uth,prove_elementar sg "ss" (HOLogic.mk_eq (rsuth,lscth))] MRS trans),exp_cp_thm] MRS trans
   (* result: EX x. efm = Q'*)
 in  ([e_ac_thm,[(prove_elementar sg "ss" (HOLogic.mk_eq (rseacth,lsuth))),u_c_thm] MRS trans] MRS trans)
   end
|cooper_prv _ _ _ =  error "Parameters format";



fun decomp_cnnf sg lfnp P = case P of 
     Const ("op &",_) $ p $q => ([p,q] , fn [th1,th2] => [th1,th2] MRS qe_conjI )
   |Const ("op |",_) $ p $q => ([p,q] , fn [th1,th2] => [th1,th2] MRS  qe_disjI)
   |Const ("Not",_) $ (Const("Not",_) $ p) => ([p], fn [th] => th RS nnf_nn)
   |Const("Not",_) $ (Const(opn,T) $ p $ q) => 
     if opn = "op |" 
      then case (p,q) of 
         (A as (Const ("op &",_) $ r $ s),B as (Const ("op &",_) $ r1 $ t)) =>
          if r1 = negate r 
          then  ([r,HOLogic.Not$s,r1,HOLogic.Not$t],fn [th1_1,th1_2,th2_1,th2_2] => [[th1_1,th1_1] MRS qe_conjI,[th2_1,th2_2] MRS qe_conjI] MRS nnf_sdj)

          else ([HOLogic.Not $ p,HOLogic.Not $ q ], fn [th1,th2] => [th1,th2] MRS nnf_ndj)
        |(_,_) => ([HOLogic.Not $ p,HOLogic.Not $ q ], fn [th1,th2] => [th1,th2] MRS nnf_ndj)
      else (
         case (opn,T) of 
           ("op &",_) => ([HOLogic.Not $ p,HOLogic.Not $ q ], fn [th1,th2] =>[th1,th2] MRS nnf_ncj )
           |("op -->",_) => ([p,HOLogic.Not $ q ], fn [th1,th2] =>[th1,th2] MRS nnf_nim )
           |("op =",Type ("fun",[Type ("bool", []),_])) => 
           ([HOLogic.conj $ p $ (HOLogic.Not $ q),HOLogic.conj $ (HOLogic.Not $ p) $ q], fn [th1,th2] => [th1,th2] MRS nnf_neq)
            |(_,_) => ([], fn [] => lfnp P)
)

   |(Const ("op -->",_) $ p $ q) => ([HOLogic.Not$p,q], fn [th1,th2] => [th1,th2] MRS nnf_im)

   |(Const ("op =", Type ("fun",[Type ("bool", []),_])) $ p $ q) =>
     ([HOLogic.conj $ p $ q,HOLogic.conj $ (HOLogic.Not $ p) $ (HOLogic.Not $ q) ], fn [th1,th2] =>[th1,th2] MRS nnf_eq )
   |_ => ([], fn [] => lfnp P);




fun proof_of_cnnf sg p lfnp = 
 let val th1 = thm_of sg (decomp_cnnf sg lfnp) p
     val rs = snd(qe_get_terms th1)
     val th2 = prove_elementar sg "ss" (HOLogic.mk_eq(rs,simpl rs))
  in [th1,th2] MRS trans
  end;

end;
