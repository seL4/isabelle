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
  val qe_get_terms : thm -> term * term
  val cooper_prv : Sign.sg -> term -> term -> string list -> thm
  val proof_of_evalc : Sign.sg -> term -> thm
  val proof_of_cnnf : Sign.sg -> term -> (term -> thm) -> thm
  val proof_of_linform : Sign.sg -> string list -> term -> thm
end;

structure CooperProof : COOPER_PROOF =
struct

open CooperDec;

(*-----------------------------------------------------------------*)
(*-----------------------------------------------------------------*)
(*-----------------------------------------------------------------*)
(*---                                                           ---*)
(*---                                                           ---*)
(*---         Protocoling part                                  ---*)
(*---                                                           ---*)
(*---           includes the protocolling datastructure         ---*)
(*---                                                           ---*)
(*---          and the protocolling fuctions                    ---*)
(*---                                                           ---*)
(*---                                                           ---*)
(*-----------------------------------------------------------------*)
(*-----------------------------------------------------------------*)
(*-----------------------------------------------------------------*)

val presburger_ss = simpset_of (theory "Presburger")
  addsimps [zdiff_def] delsimps [symmetric zdiff_def];
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

(*A/B - set Theorem *)

val bst_thm = thm "bst_thm";
val ast_thm = thm "ast_thm";

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
(*Datatatype declarations for Proofprotocol for the cooperprocedure.*)
(* ------------------------------------------------------------------------- *)



(* ------------------------------------------------------------------------- *)
(*Datatatype declarations for Proofprotocol for the adjustcoeff step.*)
(* ------------------------------------------------------------------------- *)
datatype CpLog = No
                |Simp of term*CpLog
		|Blast of CpLog*CpLog
		|Aset of (term*term*(term list)*term)
		|Bset of (term*term*(term list)*term)
		|Minusinf of CpLog*CpLog
		|Cooper of term*CpLog*CpLog*CpLog
		|Eq_minf of term*term
		|Modd_minf of term*term
		|Eq_minf_conjI of CpLog*CpLog
		|Modd_minf_conjI of CpLog*CpLog	
		|Modd_minf_disjI of CpLog*CpLog
		|Eq_minf_disjI of CpLog*CpLog	
		|Not_bst_p of term*term*term*term*CpLog
		|Not_bst_p_atomic of term
		|Not_bst_p_conjI of CpLog*CpLog
		|Not_bst_p_disjI of CpLog*CpLog
		|Not_ast_p of term*term*term*term*CpLog
		|Not_ast_p_atomic of term
		|Not_ast_p_conjI of CpLog*CpLog
		|Not_ast_p_disjI of CpLog*CpLog
		|CpLogError;



datatype ACLog = ACAt of int*term
                |ACPI of int*term
                |ACfm of term
                |ACNeg of ACLog
		|ACConst of string*ACLog*ACLog;



(* ------------------------------------------------------------------------- *)
(*Datatatype declarations for Proofprotocol for the CNNF step.*)
(* ------------------------------------------------------------------------- *)


datatype NNFLog = NNFAt of term
                |NNFSimp of NNFLog
                |NNFNN of NNFLog
		|NNFConst of string*NNFLog*NNFLog;

(* ------------------------------------------------------------------------- *)
(*Datatatype declarations for Proofprotocol for the linform  step.*)
(* ------------------------------------------------------------------------- *)


datatype LfLog = LfAt of term
                |LfAtdvd of term
                |Lffm of term
                |LfConst of string*LfLog*LfLog
		|LfNot of LfLog
		|LfQ of string*string*typ*LfLog;


(* ------------------------------------------------------------------------- *)
(*Datatatype declarations for Proofprotocol for the evaluation- evalc-  step.*)
(* ------------------------------------------------------------------------- *)


datatype EvalLog = EvalAt of term
                |Evalfm of term
		|EvalConst of string*EvalLog*EvalLog;

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
(* Intended to tell that here we changed the structure of the formula with respect to the posineq theorem : ~(0 < t) = 0 < 1-t*)
(* ------------------------------------------------------------------------- *)
fun adjustcoeffeq_wp  x l fm = 
    case fm of  
  (Const("Not",_)$(Const("op <",_) $(Const("0",_)) $(rt as (Const ("op +", _)$(Const ("op *",_) $    c $ y ) $z )))) => 
  if (x = y) 
  then let  
       val m = l div (dest_numeral c) 
       val n = abs (m)
       val xtm = (HOLogic.mk_binop "op *" ((mk_numeral ((m div n)*l) ), x)) 
       val rs = (HOLogic.mk_binrel "op <" (zero,linear_sub [] (mk_numeral n) (HOLogic.mk_binop "op +" ( xtm ,( linear_cmul n z) )))) 
       in (ACPI(n,fm),rs)
       end
  else  let val rs = (HOLogic.mk_binrel "op <" (zero,linear_sub [] one rt )) 
        in (ACPI(1,fm),rs)
        end

  |(Const(p,_) $d $( Const ("op +", _)$(Const ("op *",_) $ 
      c $ y ) $z )) => if (is_arith_rel fm) andalso (x = y) then  
        let val m = l div (dest_numeral c) 
           val n = (if p = "op <" then abs(m) else m)  
           val xtm = (HOLogic.mk_binop "op *" ((mk_numeral ((m div n)*l) ), x))
           val rs = (HOLogic.mk_binrel p ((linear_cmul n d),(HOLogic.mk_binop "op +" ( xtm ,( linear_cmul n z) )))) 
	   in (ACAt(n,fm),rs)
	   end
        else (ACfm(fm),fm) 
  |( Const ("Not", _) $ p) => let val (rsp,rsr) = adjustcoeffeq_wp x l p 
                              in (ACNeg(rsp),HOLogic.Not $ rsr) 
                              end
  |( Const ("op &",_) $ p $ q) =>let val (rspp,rspr) = adjustcoeffeq_wp x l p
                                     val (rsqp,rsqr) = adjustcoeffeq_wp x l q

                                  in (ACConst ("CJ",rspp,rsqp), HOLogic.mk_conj (rspr,rsqr)) 
                                  end 
  |( Const ("op |",_) $ p $ q) =>let val (rspp,rspr) = adjustcoeffeq_wp x l p
                                     val (rsqp,rsqr) = adjustcoeffeq_wp x l q

                                  in (ACConst ("DJ",rspp,rsqp), HOLogic.mk_disj (rspr,rsqr)) 
                                  end

  |_ => (ACfm(fm),fm);


(*_________________________________________*)
(*-----------------------------------------*)
(* Protocol generation for the liform step *)
(*_________________________________________*)
(*-----------------------------------------*)


fun linform_wp fm = 
  let fun at_linform_wp at =
    case at of
      (Const("op <=",_)$s$t) => LfAt(at)
      |(Const("op <",_)$s$t) => LfAt(at)
      |(Const("op =",_)$s$t) => LfAt(at)
      |(Const("Divides.op dvd",_)$s$t) => LfAtdvd(at)
  in
  if is_arith_rel fm 
  then at_linform_wp fm 
  else case fm of
    (Const("Not",_) $ A) => LfNot(linform_wp A)
   |(Const("op &",_)$ A $ B) => LfConst("CJ",linform_wp A, linform_wp B)
   |(Const("op |",_)$ A $ B) => LfConst("DJ",linform_wp A, linform_wp B)
   |(Const("op -->",_)$ A $ B) => LfConst("IM",linform_wp A, linform_wp B)
   |(Const("op =",Type ("fun",[Type ("bool", []),_]))$ A $ B) => LfConst("EQ",linform_wp A, linform_wp B)
   |Const("Ex",_)$Abs(x,T,p) => 
     let val (xn,p1) = variant_abs(x,T,p)
     in LfQ("Ex",xn,T,linform_wp p1)
     end 
   |Const("All",_)$Abs(x,T,p) => 
     let val (xn,p1) = variant_abs(x,T,p)
     in LfQ("All",xn,T,linform_wp p1)
     end 
end;


(* ------------------------------------------------------------------------- *)
(*For simlified formulas we just notice the original formula, for whitch we habe been
intendes to make the proof.*)
(* ------------------------------------------------------------------------- *)
fun simpl_wp (fm,pr) = let val fm2 = simpl fm
				in (fm2,Simp(fm,pr))
				end;

	
(* ------------------------------------------------------------------------- *)
(*Help function for the generation of the proof EX.P_{minus \infty} --> EX. P(x) *)
(* ------------------------------------------------------------------------- *)
fun minusinf_wph x fm = let fun mk_atomar_minusinf_proof x fm = (Modd_minf(x,fm),Eq_minf(x,fm))
  
	      fun combine_minusinf_proofs opr (ppr1,ppr2) (qpr1,qpr2) = case opr of 
		 "CJ" => (Modd_minf_conjI(ppr1,qpr1),Eq_minf_conjI(ppr2,qpr2))
		|"DJ" => (Modd_minf_disjI(ppr1,qpr1),Eq_minf_disjI(ppr2,qpr2))
	in 
 
 case fm of 
 (Const ("Not", _) $  (Const("op =",Type ("fun",[Type ("IntDef.int", []),_])) $ c1 $ (Const ("op +", _) $(Const ("op *",_) $ c2 $ y) $z))) => 
     if (x=y) andalso (c1= zero) andalso (c2= one) then (HOLogic.true_const ,(mk_atomar_minusinf_proof x fm))
        else (fm ,(mk_atomar_minusinf_proof x fm))
 |(Const("op =",Type ("fun",[Type ("IntDef.int", []),_])) $ c1 $(Const ("op +", _) $(Const ("op *",_) $ c2 $ y) $z)) =>
  	 if (is_arith_rel fm) andalso (x=y) andalso (c1= zero) andalso (c2= one)
	 then (HOLogic.false_const ,(mk_atomar_minusinf_proof x fm))
	 				 else (fm,(mk_atomar_minusinf_proof x fm)) 
 |(Const("op <",_) $ c1 $(Const ("op +", _) $(Const ("op *",_) $ c2 $ y ) $ z )) =>
       if (y=x) andalso (c1 = zero) then 
        if c2 = one then (HOLogic.false_const,(mk_atomar_minusinf_proof x fm)) else
	(HOLogic.true_const,(mk_atomar_minusinf_proof x fm))
	else (fm,(mk_atomar_minusinf_proof x fm))
  
  |(Const("Not",_)$(Const ("Divides.op dvd",_) $_ )) => (fm,mk_atomar_minusinf_proof x fm)
  
  |(Const ("Divides.op dvd",_) $_ ) => (fm,mk_atomar_minusinf_proof x fm)
  
  |(Const ("op &",_) $ p $ q) => let val (pfm,ppr) = minusinf_wph x p
  				    val (qfm,qpr) = minusinf_wph x q
				    val pr = (combine_minusinf_proofs "CJ" ppr qpr)
				     in 
				     (HOLogic.conj $ pfm $qfm , pr)
				     end 
  |(Const ("op |",_) $ p $ q) => let val (pfm,ppr) = minusinf_wph x p
  				     val (qfm,qpr) = minusinf_wph x q
				     val pr = (combine_minusinf_proofs "DJ" ppr qpr)
				     in 
				     (HOLogic.disj $ pfm $qfm , pr)
				     end 

  |_ => (fm,(mk_atomar_minusinf_proof x fm))
  
  end;					 
(* ------------------------------------------------------------------------- *)	    (* Protokol for the Proof of the property of the minusinfinity formula*)
(* Just combines the to protokols *)
(* ------------------------------------------------------------------------- *)
fun minusinf_wp x fm  = let val (fm2,pr) = (minusinf_wph x fm)
                       in (fm2,Minusinf(pr))
                        end;

(* ------------------------------------------------------------------------- *)
(*Help function for the generation of the proof EX.P_{plus \infty} --> EX. P(x) *)
(* ------------------------------------------------------------------------- *)

fun plusinf_wph x fm = let fun mk_atomar_plusinf_proof x fm = (Modd_minf(x,fm),Eq_minf(x,fm))
  
	      fun combine_plusinf_proofs opr (ppr1,ppr2) (qpr1,qpr2) = case opr of 
		 "CJ" => (Modd_minf_conjI(ppr1,qpr1),Eq_minf_conjI(ppr2,qpr2))
		|"DJ" => (Modd_minf_disjI(ppr1,qpr1),Eq_minf_disjI(ppr2,qpr2))
	in 
 
 case fm of 
 (Const ("Not", _) $  (Const("op =",Type ("fun",[Type ("IntDef.int", []),_])) $ c1 $ (Const ("op +", _) $(Const ("op *",_) $ c2 $ y) $z))) => 
     if (x=y) andalso (c1= zero) andalso (c2= one) then (HOLogic.true_const ,(mk_atomar_plusinf_proof x fm))
        else (fm ,(mk_atomar_plusinf_proof x fm))
 |(Const("op =",Type ("fun",[Type ("IntDef.int", []),_])) $ c1 $(Const ("op +", _) $(Const ("op *",_) $ c2 $ y) $z)) =>
  	 if (is_arith_rel fm) andalso (x=y) andalso (c1= zero) andalso (c2= one)
	 then (HOLogic.false_const ,(mk_atomar_plusinf_proof x fm))
	 				 else (fm,(mk_atomar_plusinf_proof x fm)) 
 |(Const("op <",_) $ c1 $(Const ("op +", _) $(Const ("op *",_) $ c2 $ y ) $ z )) =>
       if (y=x) andalso (c1 = zero) then 
        if c2 = one then (HOLogic.true_const,(mk_atomar_plusinf_proof x fm)) else
	(HOLogic.false_const,(mk_atomar_plusinf_proof x fm))
	else (fm,(mk_atomar_plusinf_proof x fm))
  
  |(Const("Not",_)$(Const ("Divides.op dvd",_) $_ )) => (fm,mk_atomar_plusinf_proof x fm)
  
  |(Const ("Divides.op dvd",_) $_ ) => (fm,mk_atomar_plusinf_proof x fm)
  
  |(Const ("op &",_) $ p $ q) => let val (pfm,ppr) = plusinf_wph x p
  				    val (qfm,qpr) = plusinf_wph x q
				    val pr = (combine_plusinf_proofs "CJ" ppr qpr)
				     in 
				     (HOLogic.conj $ pfm $qfm , pr)
				     end 
  |(Const ("op |",_) $ p $ q) => let val (pfm,ppr) = plusinf_wph x p
  				     val (qfm,qpr) = plusinf_wph x q
				     val pr = (combine_plusinf_proofs "DJ" ppr qpr)
				     in 
				     (HOLogic.disj $ pfm $qfm , pr)
				     end 

  |_ => (fm,(mk_atomar_plusinf_proof x fm))
  
  end;					 
(* ------------------------------------------------------------------------- *)	    (* Protokol for the Proof of the property of the minusinfinity formula*)
(* Just combines the to protokols *)
(* ------------------------------------------------------------------------- *)
fun plusinf_wp x fm  = let val (fm2,pr) = (plusinf_wph x fm)
                       in (fm2,Minusinf(pr))
                        end;


(* ------------------------------------------------------------------------- *)
(*Protocol that we here uses Bset.*)
(* ------------------------------------------------------------------------- *)
fun bset_wp x fm = let val bs = bset x fm in
				(bs,Bset(x,fm,bs,mk_numeral (divlcm x fm)))
				end;

(* ------------------------------------------------------------------------- *)
(*Protocol that we here uses Aset.*)
(* ------------------------------------------------------------------------- *)
fun aset_wp x fm = let val ast = aset x fm in
				(ast,Aset(x,fm,ast,mk_numeral (divlcm x fm)))
				end;
 


(* ------------------------------------------------------------------------- *)
(*function list to Set, constructs a set containing all elements of a given list.*)
(* ------------------------------------------------------------------------- *)
fun list_to_set T1 l = let val T = (HOLogic.mk_setT T1) in 
	case l of 
		[] => Const ("{}",T)
		|(h::t) => Const("insert", T1 --> (T --> T)) $ h $(list_to_set T1 t)
		end;
		

(*====================================================================*)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(*Protocol for the proof of the backward direction of the cooper theorem.*)
(* Helpfunction - Protokols evereything about the proof reconstruction*)
(* ------------------------------------------------------------------------- *)
fun not_bst_p_wph fm = case fm of
	Const("Not",_) $ R => if (is_arith_rel R) then (Not_bst_p_atomic (fm)) else CpLogError
	|Const("op &",_) $ ls $ rs => Not_bst_p_conjI((not_bst_p_wph ls),(not_bst_p_wph rs))
	|Const("op |",_) $ ls $ rs => Not_bst_p_disjI((not_bst_p_wph ls),(not_bst_p_wph rs))
	|_ => Not_bst_p_atomic (fm);
(* ------------------------------------------------------------------------- *)	
(* Main protocoling function for the backward direction gives the Bset and the divlcm and the Formula herself. Needed as inherited attributes for the proof reconstruction*)
(* ------------------------------------------------------------------------- *)
fun not_bst_p_wp x fm = let val prt = not_bst_p_wph fm
			    val D = mk_numeral (divlcm x fm)
			    val B = map norm_zero_one (bset x fm)
			in (Not_bst_p (x,fm,D,(list_to_set HOLogic.intT B) , prt))
			end;
(*====================================================================*)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(*Protocol for the proof of the backward direction of the cooper theorem.*)
(* Helpfunction - Protokols evereything about the proof reconstruction*)
(* ------------------------------------------------------------------------- *)
fun not_ast_p_wph fm = case fm of
	Const("Not",_) $ R => if (is_arith_rel R) then (Not_ast_p_atomic (fm)) else CpLogError
	|Const("op &",_) $ ls $ rs => Not_ast_p_conjI((not_ast_p_wph ls),(not_ast_p_wph rs))
	|Const("op |",_) $ ls $ rs => Not_ast_p_disjI((not_ast_p_wph ls),(not_ast_p_wph rs))
	|_ => Not_ast_p_atomic (fm);
(* ------------------------------------------------------------------------- *)	
(* Main protocoling function for the backward direction gives the Bset and the divlcm and the Formula herself. Needed as inherited attributes for the proof reconstruction*)
(* ------------------------------------------------------------------------- *)
fun not_ast_p_wp x fm = let val prt = not_ast_p_wph fm
			    val D = mk_numeral (divlcm x fm)
			    val B = map norm_zero_one (aset x fm)
			in (Not_ast_p (x,fm,D,(list_to_set HOLogic.intT B) , prt))
			end;

(*======================================================*)
(* Protokolgeneration for the formula evaluation process*)
(*======================================================*)

fun evalc_wp fm = 
  let fun evalc_atom_wp at =case at of  
    (Const (p,_) $ s $ t) =>(  
    case assoc (operations,p) of 
        Some f => ((if (f ((dest_numeral s),(dest_numeral t))) then EvalAt(HOLogic.mk_eq(at,HOLogic.true_const)) else EvalAt(HOLogic.mk_eq(at, HOLogic.false_const)))  
		   handle _ => Evalfm(at)) 
        | _ =>  Evalfm(at)) 
     |Const("Not",_)$(Const (p,_) $ s $ t) =>(  
       case assoc (operations,p) of 
         Some f => ((if (f ((dest_numeral s),(dest_numeral t))) then 
	  EvalAt(HOLogic.mk_eq(at, HOLogic.false_const))  else EvalAt(HOLogic.mk_eq(at,HOLogic.true_const)))  
		      handle _ => Evalfm(at)) 
         | _ => Evalfm(at)) 
     | _ => Evalfm(at)  
 
  in
   case fm of
    (Const("op &",_)$A$B) => EvalConst("CJ",evalc_wp A,evalc_wp B)
   |(Const("op |",_)$A$B) => EvalConst("DJ",evalc_wp A,evalc_wp B) 
   |(Const("op -->",_)$A$B) => EvalConst("IM",evalc_wp A,evalc_wp B) 
   |(Const("op =", Type ("fun",[Type ("bool", []),_]))$A$B) => EvalConst("EQ",evalc_wp A,evalc_wp B) 
   |_ => evalc_atom_wp fm
  end;



(*======================================================*)
(* Protokolgeneration for the NNF Transformation        *)
(*======================================================*)

fun cnnf_wp f = 
  let fun hcnnf_wp fm =
    case fm of
    (Const ("op &",_) $ p $ q) => NNFConst("CJ",hcnnf_wp p,hcnnf_wp q) 
    | (Const ("op |",_) $ p $ q) =>  NNFConst("DJ",hcnnf_wp p,hcnnf_wp q)
    | (Const ("op -->",_) $ p $q) => NNFConst("IM",hcnnf_wp (HOLogic.Not $ p),hcnnf_wp q)
    | (Const ("op =",Type ("fun",[Type ("bool", []),_])) $ p $ q) => NNFConst("EQ",hcnnf_wp (HOLogic.mk_conj(p,q)),hcnnf_wp (HOLogic.mk_conj((HOLogic.Not $ p), (HOLogic.Not $ q)))) 

    | (Const ("Not",_) $ (Const("Not",_) $ p)) => NNFNN(hcnnf_wp p) 
    | (Const ("Not",_) $ (Const ("op &",_) $ p $ q)) => NNFConst ("NCJ",(hcnnf_wp(HOLogic.Not $ p)),(hcnnf_wp(HOLogic.Not $ q))) 
    | (Const ("Not",_) $(Const ("op |",_) $ (A as (Const ("op &",_) $ p $ q)) $  
    			(B as (Const ("op &",_) $ p1 $ r)))) => if p1 = negate p then 
		         NNFConst("SDJ",  
			   NNFConst("CJ",hcnnf_wp p,hcnnf_wp(HOLogic.Not $ q)),
			   NNFConst("CJ",hcnnf_wp p1,hcnnf_wp(HOLogic.Not $ r)))
			 else  NNFConst ("NDJ",(hcnnf_wp(HOLogic.Not $ A)),(hcnnf_wp(HOLogic.Not $ B))) 

    | (Const ("Not",_) $ (Const ("op |",_) $ p $ q)) => NNFConst ("NDJ",(hcnnf_wp(HOLogic.Not $ p)),(hcnnf_wp(HOLogic.Not $ q))) 
    | (Const ("Not",_) $ (Const ("op -->",_) $ p $q)) =>  NNFConst ("NIM",(hcnnf_wp(p)),(hcnnf_wp(HOLogic.Not $ q))) 
    | (Const ("Not",_) $ (Const ("op =",Type ("fun",[Type ("bool", []),_]))  $ p $ q)) =>NNFConst ("NEQ",(NNFConst("CJ",hcnnf_wp p,hcnnf_wp(HOLogic.Not $ q))),(NNFConst("CJ",hcnnf_wp(HOLogic.Not $ p),hcnnf_wp q))) 
    | _ => NNFAt(fm)  
  in NNFSimp(hcnnf_wp f)
end; 
   





(* ------------------------------------------------------------------------- *)
(*Cooper decision Procedure with proof protocoling*)
(* ------------------------------------------------------------------------- *)

fun coopermi_wp vars fm =
  case fm of
   Const ("Ex",_) $ Abs(xo,T,po) => let 
    val (xn,np) = variant_abs(xo,T,po) 
    val x = (Free(xn , T))
    val p = np     (* Is this a legal proof for the P=NP Problem??*)
    val (p_inf,miprt) = simpl_wp (minusinf_wp x p)
    val (bset,bsprt) = bset_wp x p
    val nbst_p_prt = not_bst_p_wp x p
    val dlcm = divlcm x p 
    val js = 1 upto dlcm 
    fun p_element j b = linrep vars x (linear_add vars b (mk_numeral j)) p 
    fun stage j = list_disj (linrep vars x (mk_numeral j) p_inf :: map (p_element j) bset) 
   in (list_disj (map stage js),Cooper(mk_numeral dlcm,miprt,bsprt,nbst_p_prt))
   end
   
  | _ => (error "cooper: not an existential formula",No);
				
fun cooperpi_wp vars fm =
  case fm of
   Const ("Ex",_) $ Abs(xo,T,po) => let 
    val (xn,np) = variant_abs(xo,T,po) 
    val x = (Free(xn , T))
    val p = np     (* Is this a legal proof for the P=NP Problem??*)
    val (p_inf,piprt) = simpl_wp (plusinf_wp x p)
    val (aset,asprt) = aset_wp x p
    val nast_p_prt = not_ast_p_wp x p
    val dlcm = divlcm x p 
    val js = 1 upto dlcm 
    fun p_element j a = linrep vars x (linear_sub vars a (mk_numeral j)) p 
    fun stage j = list_disj (linrep vars x (mk_numeral j) p_inf :: map (p_element j) aset) 
   in (list_disj (map stage js),Cooper(mk_numeral dlcm,piprt,asprt,nast_p_prt))
   end
  | _ => (error "cooper: not an existential formula",No);
				




(*-----------------------------------------------------------------*)
(*-----------------------------------------------------------------*)
(*-----------------------------------------------------------------*)
(*---                                                           ---*)
(*---                                                           ---*)
(*---      Interpretation and Proofgeneration Part              ---*)
(*---                                                           ---*)
(*---      Protocole interpretation functions                   ---*)
(*---                                                           ---*)
(*---      and proofgeneration functions                        ---*)
(*---                                                           ---*)
(*---                                                           ---*)
(*---                                                           ---*)
(*---                                                           ---*)
(*-----------------------------------------------------------------*)
(*-----------------------------------------------------------------*)
(*-----------------------------------------------------------------*)

(* ------------------------------------------------------------------------- *)
(* Returns both sides of an equvalence in the theorem*)
(* ------------------------------------------------------------------------- *)
fun qe_get_terms th = let val (_$(Const("op =",Type ("fun",[Type ("bool", []),_])) $ A $ B )) = prop_of th in (A,B) end;


(*-------------------------------------------------------------*)
(*-------------------------------------------------------------*)
(*-------------------------------------------------------------*)
(*-------------------------------------------------------------*)

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
(*-------------------------------------------------------------*)
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



(* ------------------------------------------------------------------------- *)
(* This function return an Isabelle proof, of the adjustcoffeq result.*)
(* The proofs are in Presburger.thy and are generally based on the arithmetic *)
(* ------------------------------------------------------------------------- *)
fun proof_of_adjustcoeffeq sg (prt,rs) = case prt of
   ACfm fm => instantiate' [Some cboolT]
    [Some (cterm_of sg fm)] refl
 | ACAt (k,at as (Const(p,_) $a $( Const ("op +", _)$(Const ("op *",_) $ 
      c $ x ) $t ))) => 
   let
     val ck = cterm_of sg (mk_numeral k)
     val cc = cterm_of sg c
     val ct = cterm_of sg t
     val cx = cterm_of sg x
     val ca = cterm_of sg a
   in case p of
     "op <" => let val pre = prove_elementar sg "lf" 
	                  (HOLogic.mk_binrel "op <" (Const("0",HOLogic.intT),(mk_numeral k)))
	           val th1 = (pre RS (instantiate' [] [Some ck,Some ca,Some cc, Some cx, Some ct] (ac_lt_eq)))
		      in [th1,(prove_elementar sg "lf" (HOLogic.mk_eq (snd (qe_get_terms th1) ,rs)))] MRS trans
                   end
    |"op =" =>let val pre = prove_elementar sg "lf" 
	    (HOLogic.Not $ (HOLogic.mk_binrel "op =" (Const("0",HOLogic.intT),(mk_numeral k))))
	          in let val th1 = (pre RS(instantiate' [] [Some ck,Some ca,Some cc, Some cx, Some ct] (ac_eq_eq)))
	             in [th1,(prove_elementar sg "lf" (HOLogic.mk_eq (snd (qe_get_terms th1) ,rs)))] MRS trans
                      end
                  end
    |"Divides.op dvd" =>let val pre = prove_elementar sg "lf" 
	   (HOLogic.Not $ (HOLogic.mk_binrel "op =" (Const("0",HOLogic.intT),(mk_numeral k))))
	                 val th1 = (pre RS (instantiate' [] [Some ck,Some ca,Some cc, Some cx, Some ct]) (ac_dvd_eq))
                         in [th1,(prove_elementar sg "lf" (HOLogic.mk_eq (snd (qe_get_terms th1) ,rs)))] MRS trans
                        
                          end
  end
 |ACPI(k,at as (Const("Not",_)$(Const("op <",_) $a $( Const ("op +", _)$(Const ("op *",_) $ c $ x ) $t )))) => 
   let
     val ck = cterm_of sg (mk_numeral k)
     val cc = cterm_of sg c
     val ct = cterm_of sg t
     val cx = cterm_of sg x
     val pre = prove_elementar sg "lf" 
       (HOLogic.mk_binrel "op <" (Const("0",HOLogic.intT),(mk_numeral k)))
       val th1 = (pre RS (instantiate' [] [Some ck,Some cc, Some cx, Some ct] (ac_pi_eq)))

         in [th1,(prove_elementar sg "sa" (HOLogic.mk_eq (snd (qe_get_terms th1) ,rs)))] MRS trans
   end
 |ACNeg(pr) => let val (Const("Not",_)$nrs) = rs
               in (proof_of_adjustcoeffeq sg (pr,nrs)) RS (qe_Not) 
               end
 |ACConst(s,pr1,pr2) =>
   let val (Const(_,_)$rs1$rs2) = rs
       val th1 = proof_of_adjustcoeffeq sg (pr1,rs1)
       val th2 = proof_of_adjustcoeffeq sg (pr2,rs2)
       in case s of 
	 "CJ" => [th1,th2] MRS (qe_conjI)
         |"DJ" => [th1,th2] MRS (qe_disjI)
         |"IM" => [th1,th2] MRS (qe_impI)
         |"EQ" => [th1,th2] MRS (qe_eqI)
   end;






(* ------------------------------------------------------------------------- *)
(* This function return an Isabelle proof, of some properties on the atoms*)
(* The proofs are in Presburger.thy and are generally based on the arithmetic *)
(* This function doese only instantiate the the theorems in the theory *)
(* ------------------------------------------------------------------------- *)
fun atomar_minf_proof_of sg dlcm (Modd_minf (x,fm1)) =
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
   end	

 |atomar_minf_proof_of sg dlcm (Eq_minf (x,fm1)) =  let
       (*Some certified types*)
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


(* ------------------------------------------------------------------------- *)
(* This function combines proofs of some special form already synthetised from the subtrees to make*)
(* a new proof of the same form. The combination occures whith isabelle theorems which have been already prooved *)
(*these Theorems are in Presburger.thy and mostly do not relay on the arithmetic.*)
(* These are Theorems for the Property of P_{-infty}*)
(* ------------------------------------------------------------------------- *)
fun combine_minf_proof s pr1 pr2 = case s of
    "ECJ" => [pr1 , pr2] MRS (eq_minf_conjI)

   |"EDJ" => [pr1 , pr2] MRS (eq_minf_disjI)
   
   |"MCJ" => [pr1 , pr2] MRS (modd_minf_conjI)

   |"MDJ" => [pr1 , pr2] MRS (modd_minf_disjI);

(* ------------------------------------------------------------------------- *)
(*This function return an isabelle Proof for the minusinfinity theorem*)
(* It interpretates the protool and gives the protokoles property of P_{...} as a theorem*)
(* ------------------------------------------------------------------------- *)
fun minf_proof_ofh sg dlcm prl = case prl of 

    Eq_minf (_) => atomar_minf_proof_of sg dlcm prl
    
   |Modd_minf (_) => atomar_minf_proof_of sg dlcm prl
   
   |Eq_minf_conjI (prl1,prl2) => let val pr1 = minf_proof_ofh sg dlcm prl1
   				    val pr2 = minf_proof_ofh sg dlcm prl2
				 in (combine_minf_proof "ECJ" pr1 pr2)
				 end
				 
   |Eq_minf_disjI (prl1,prl2) => let val pr1 = minf_proof_ofh sg dlcm prl1
   				    val pr2 = minf_proof_ofh sg dlcm prl2
				 in (combine_minf_proof "EDJ" pr1 pr2)
				 end
				 
   |Modd_minf_conjI (prl1,prl2) => let val pr1 = minf_proof_ofh sg dlcm prl1
   				    val pr2 = minf_proof_ofh sg dlcm prl2
				 in (combine_minf_proof "MCJ" pr1 pr2)
				 end
				 
   |Modd_minf_disjI (prl1,prl2) => let val pr1 = minf_proof_ofh sg dlcm prl1
   				    val pr2 = minf_proof_ofh sg dlcm prl2
				 in (combine_minf_proof "MDJ" pr1 pr2)
				 end;
(* ------------------------------------------------------------------------- *)
(* Main function For the rest both properies of P_{..} are needed and here both theorems are returned.*)				 
(* ------------------------------------------------------------------------- *)
fun  minf_proof_of sg dlcm (Minusinf (prl1,prl2))  = 
  let val pr1 = minf_proof_ofh sg dlcm prl1
      val pr2 = minf_proof_ofh sg dlcm prl2
  in (pr1, pr2)
end;
				 



(* ------------------------------------------------------------------------- *)
(* This function return an Isabelle proof, of some properties on the atoms*)
(* The proofs are in Presburger.thy and are generally based on the arithmetic *)
(* This function doese only instantiate the the theorems in the theory *)
(* ------------------------------------------------------------------------- *)
fun atomar_pinf_proof_of sg dlcm (Modd_minf (x,fm1)) =
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
   end	

 |atomar_pinf_proof_of sg dlcm (Eq_minf (x,fm1)) =  let
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


(* ------------------------------------------------------------------------- *)
(* This function combines proofs of some special form already synthetised from the subtrees to make*)
(* a new proof of the same form. The combination occures whith isabelle theorems which have been already prooved *)
(*these Theorems are in Presburger.thy and mostly do not relay on the arithmetic.*)
(* These are Theorems for the Property of P_{+infty}*)
(* ------------------------------------------------------------------------- *)
fun combine_pinf_proof s pr1 pr2 = case s of
    "ECJ" => [pr1 , pr2] MRS (eq_pinf_conjI)

   |"EDJ" => [pr1 , pr2] MRS (eq_pinf_disjI)
   
   |"MCJ" => [pr1 , pr2] MRS (modd_pinf_conjI)

   |"MDJ" => [pr1 , pr2] MRS (modd_pinf_disjI);

(* ------------------------------------------------------------------------- *)
(*This function return an isabelle Proof for the minusinfinity theorem*)
(* It interpretates the protool and gives the protokoles property of P_{...} as a theorem*)
(* ------------------------------------------------------------------------- *)
fun pinf_proof_ofh sg dlcm prl = case prl of 

    Eq_minf (_) => atomar_pinf_proof_of sg dlcm prl
    
   |Modd_minf (_) => atomar_pinf_proof_of sg dlcm prl
   
   |Eq_minf_conjI (prl1,prl2) => let val pr1 = pinf_proof_ofh sg dlcm prl1
   				    val pr2 = pinf_proof_ofh sg dlcm prl2
				 in (combine_pinf_proof "ECJ" pr1 pr2)
				 end
				 
   |Eq_minf_disjI (prl1,prl2) => let val pr1 = pinf_proof_ofh sg dlcm prl1
   				    val pr2 = pinf_proof_ofh sg dlcm prl2
				 in (combine_pinf_proof "EDJ" pr1 pr2)
				 end
				 
   |Modd_minf_conjI (prl1,prl2) => let val pr1 = pinf_proof_ofh sg dlcm prl1
   				    val pr2 = pinf_proof_ofh sg dlcm prl2
				 in (combine_pinf_proof "MCJ" pr1 pr2)
				 end
				 
   |Modd_minf_disjI (prl1,prl2) => let val pr1 = pinf_proof_ofh sg dlcm prl1
   				    val pr2 = pinf_proof_ofh sg dlcm prl2
				 in (combine_pinf_proof "MDJ" pr1 pr2)
				 end;
(* ------------------------------------------------------------------------- *)
(* Main function For the rest both properies of P_{..} are needed and here both theorems are returned.*)				 
(* ------------------------------------------------------------------------- *)
fun pinf_proof_of sg dlcm (Minusinf (prl1,prl2))  = 
  let val pr1 = pinf_proof_ofh sg dlcm prl1
      val pr2 = pinf_proof_ofh sg dlcm prl2
  in (pr1, pr2)
end;
				 



(* ------------------------------------------------------------------------- *)
(* Here we generate the theorem for the Bset Property in the simple direction*)
(* It is just an instantiation*)
(* ------------------------------------------------------------------------- *)
fun bsetproof_of sg (Bset(x as Free(xn,xT),fm,bs,dlcm))   = 
  let
    val cp = cterm_of sg (absfree (xn,xT,(norm_zero_one fm)))
    val cdlcm = cterm_of sg dlcm
    val cB = cterm_of sg (list_to_set HOLogic.intT (map norm_zero_one bs))
  in instantiate' [] [Some cdlcm,Some cB, Some cp] (bst_thm)
    end;




(* ------------------------------------------------------------------------- *)
(* Here we generate the theorem for the Bset Property in the simple direction*)
(* It is just an instantiation*)
(* ------------------------------------------------------------------------- *)
fun asetproof_of sg (Aset(x as Free(xn,xT),fm,ast,dlcm))   = 
  let
    val cp = cterm_of sg (absfree (xn,xT,(norm_zero_one fm)))
    val cdlcm = cterm_of sg dlcm
    val cA = cterm_of sg (list_to_set HOLogic.intT (map norm_zero_one ast))
  in instantiate' [] [Some cdlcm,Some cA, Some cp] (ast_thm)
end;




(* ------------------------------------------------------------------------- *)    
(* Protokol interpretation function for the backwards direction for cooper's Theorem*)

(* For the generation of atomic Theorems*)
(* Prove the premisses on runtime and then make RS*)
(* ------------------------------------------------------------------------- *)
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
fun not_bst_p_proof_of_h sg x fm dlcm B prt = case prt of 
	(Not_bst_p_atomic(fm2)) => (generate_atomic_not_bst_p sg x fm dlcm B fm2)
	
	|(Not_bst_p_conjI(pr1,pr2)) => 
			let val th1 = (not_bst_p_proof_of_h sg x fm dlcm B pr1)
			    val th2 = (not_bst_p_proof_of_h sg x fm dlcm B pr2)
			    in ([th1,th2] MRS (not_bst_p_conjI))
			    end

	|(Not_bst_p_disjI(pr1,pr2)) => 
			let val th1 = (not_bst_p_proof_of_h sg x fm dlcm B pr1)
			    val th2 = (not_bst_p_proof_of_h sg x fm dlcm B pr2)
			    in ([th1,th2] MRS not_bst_p_disjI)
			    end;
(* Main function*)
fun not_bst_p_proof_of sg (Not_bst_p(x as Free(xn,xT),fm,dlcm,B,prl)) =
  let val th =  not_bst_p_proof_of_h sg x fm dlcm B prl
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
    
(* ------------------------------------------------------------------------- *)    
(* Main interpretation function for this backwards dirction*)
(* if atomic do generate atomis formulae else Construct theorems and then make RS with the construction theorems*)
(*Help Function*)
(* ------------------------------------------------------------------------- *)
fun not_ast_p_proof_of_h sg x fm dlcm A prt = case prt of 
	(Not_ast_p_atomic(fm2)) => (generate_atomic_not_ast_p sg x fm dlcm A fm2)
	
	|(Not_ast_p_conjI(pr1,pr2)) => 
			let val th1 = (not_ast_p_proof_of_h sg x fm dlcm A pr1)
			    val th2 = (not_ast_p_proof_of_h sg x fm dlcm A pr2)
			    in ([th1,th2] MRS (not_ast_p_conjI))
			    end

	|(Not_ast_p_disjI(pr1,pr2)) => 
			let val th1 = (not_ast_p_proof_of_h sg x fm dlcm A pr1)
			    val th2 = (not_ast_p_proof_of_h sg x fm dlcm A pr2)
			    in ([th1,th2] MRS (not_ast_p_disjI))
			    end;
(* Main function*)
fun not_ast_p_proof_of sg (Not_ast_p(x as Free(xn,xT),fm,dlcm,A,prl)) =
  let val th =  not_ast_p_proof_of_h sg x fm dlcm A prl
      val fma = absfree (xn,xT, norm_zero_one fm)
      val th1 =  prove_elementar sg "ss"  (HOLogic.mk_eq (fma,fma))
  in [th,th1] MRS (not_ast_p_Q_elim)
end;




(* ------------------------------------------------------------------------- *)
(* Interpretaion of Protocols of the cooper procedure : minusinfinity version*)
(* ------------------------------------------------------------------------- *)


fun coopermi_proof_of sg x (Cooper (dlcm,Simp(fm,miprt),bsprt,nbst_p_prt)) =
  (* Get the Bset thm*)
  let val bst = bsetproof_of sg bsprt
      val (mit1,mit2) = minf_proof_of sg dlcm miprt
      val fm1 = norm_zero_one (simpl fm) 
      val dpos = prove_elementar sg "ss" (HOLogic.mk_binrel "op <" (zero,dlcm));
      val nbstpthm = not_bst_p_proof_of sg nbst_p_prt
    (* Return the four theorems needed to proove the whole Cooper Theorem*)
  in (dpos,mit2,bst,nbstpthm,mit1)
end;


(* ------------------------------------------------------------------------- *)
(* Interpretaion of Protocols of the cooper procedure : plusinfinity version *)
(* ------------------------------------------------------------------------- *)


fun cooperpi_proof_of sg x (Cooper (dlcm,Simp(fm,miprt),bsprt,nast_p_prt)) =
  let val ast = asetproof_of sg bsprt
      val (mit1,mit2) = pinf_proof_of sg dlcm miprt
      val fm1 = norm_zero_one (simpl fm) 
      val dpos = prove_elementar sg "ss" (HOLogic.mk_binrel "op <" (zero,dlcm));
      val nastpthm = not_ast_p_proof_of sg nast_p_prt
  in (dpos,mit2,ast,nastpthm,mit1)
end;


(* ------------------------------------------------------------------------- *)
(* Interpretaion of Protocols of the cooper procedure : full version*)
(* ------------------------------------------------------------------------- *)



fun cooper_thm sg s (x as Free(xn,xT)) vars cfm = case s of
  "pi" => let val (rs,prt) = cooperpi_wp (xn::vars) (HOLogic.mk_exists(xn,xT,cfm))
	      val (dpsthm,th1,th2,nbpth,th3) = cooperpi_proof_of sg x prt
		   in [dpsthm,th1,th2,nbpth,th3] MRS (cppi_eq)
           end
  |"mi" => let val (rs,prt) = coopermi_wp (xn::vars) (HOLogic.mk_exists(xn,xT,cfm))
	       val (dpsthm,th1,th2,nbpth,th3) = coopermi_proof_of sg x prt
		   in [dpsthm,th1,th2,nbpth,th3] MRS (cpmi_eq)
                end
 |_ => error "parameter error";

(* ------------------------------------------------------------------------- *)
(* This function should evoluate to the end prove Procedure for one quantifier elimination for Presburger arithmetic*)
(* It shoud be plugged in the qfnp argument of the quantifier elimination proof function*)
(* ------------------------------------------------------------------------- *)

fun cooper_prv sg (x as Free(xn,xT)) efm vars = let 
   val l = formlcm x efm
   val ac_thm = proof_of_adjustcoeffeq sg (adjustcoeffeq_wp  x l efm)
   val fm = snd (qe_get_terms ac_thm)
   val  cfm = unitycoeff x fm
   val afm = adjustcoeff x l fm
   val P = absfree(xn,xT,afm)
   val ss = presburger_ss addsimps
     [simp_from_to] delsimps [P_eqtrue, P_eqfalse, bex_triv, insert_iff]
   val uth = instantiate' [] [Some (cterm_of sg P) , Some (cterm_of sg (mk_numeral l))] (unity_coeff_ex)
   val e_ac_thm = (forall_intr (cterm_of sg x) ac_thm) COMP (qe_exI)
   val cms = if ((length (aset x cfm)) < (length (bset x cfm))) then "pi" else "mi"
   val cp_thm = cooper_thm sg cms x vars cfm
   val exp_cp_thm = refl RS (simplify ss (cp_thm RSN (2,trans)))
   val (lsuth,rsuth) = qe_get_terms (uth)
   val (lseacth,rseacth) = qe_get_terms(e_ac_thm)
   val (lscth,rscth) = qe_get_terms (exp_cp_thm)
   val  u_c_thm = [([uth,prove_elementar sg "ss" (HOLogic.mk_eq (rsuth,lscth))] MRS trans),exp_cp_thm] MRS trans
 in  ([e_ac_thm,[(prove_elementar sg "ss" (HOLogic.mk_eq (rseacth,lsuth))),u_c_thm] MRS trans] MRS trans)
   end
|cooper_prv _ _ _ _ = error "Parameters format";


(*====================================================*)
(*Interpretation function for the evaluation protokol *)
(*====================================================*)

fun proof_of_evalc sg fm =
let
fun proof_of_evalch prt = case prt of
  EvalAt(at) => prove_elementar sg "ss" at
 |Evalfm(fm) => instantiate' [Some cboolT] [Some (cterm_of sg fm)] refl
 |EvalConst(s,pr1,pr2) => 
   let val th1 = proof_of_evalch pr1
       val th2 = proof_of_evalch pr2
   in case s of
     "CJ" =>[th1,th2] MRS (qe_conjI)
    |"DJ" =>[th1,th2] MRS (qe_disjI)
    |"IM" =>[th1,th2] MRS (qe_impI)
    |"EQ" =>[th1,th2] MRS (qe_eqI)
    end
in proof_of_evalch (evalc_wp fm)
end;

(*============================================================*)
(*Interpretation function for the NNF-Transformation protokol *)
(*============================================================*)

fun proof_of_cnnf sg fm pf = 
let fun proof_of_cnnfh prt pat = case prt of
  NNFAt(at) => pat at
 |NNFSimp (pr) => let val th1 = proof_of_cnnfh pr pat
                  in let val fm2 = snd (qe_get_terms th1) 
		     in [th1,prove_elementar sg "ss" (HOLogic.mk_eq(fm2 ,simpl fm2))] MRS trans
                     end
                  end
 |NNFNN (pr) => (proof_of_cnnfh pr pat) RS (nnf_nn)
 |NNFConst (s,pr1,pr2) =>
   let val th1 = proof_of_cnnfh pr1 pat
       val th2 = proof_of_cnnfh pr2 pat
   in case s of
     "CJ" => [th1,th2] MRS (qe_conjI)
    |"DJ" => [th1,th2] MRS (qe_disjI)
    |"IM" => [th1,th2] MRS (nnf_im)
    |"EQ" => [th1,th2] MRS (nnf_eq)
    |"SDJ" => let val (Const("op &",_)$A$_) = fst (qe_get_terms th1)
	          val (Const("op &",_)$C$_) = fst (qe_get_terms th2)
	      in [th1,th2,prove_elementar sg "ss" (HOLogic.mk_eq (A,HOLogic.Not $ C))] MRS (nnf_sdj)
	      end
    |"NCJ" => [th1,th2] MRS (nnf_ncj)
    |"NIM" => [th1,th2] MRS (nnf_nim)
    |"NEQ" => [th1,th2] MRS (nnf_neq)
    |"NDJ" => [th1,th2] MRS (nnf_ndj)
   end
in proof_of_cnnfh (cnnf_wp fm) pf
end;




(*====================================================*)
(* Interpretation function for the linform protokol   *)
(*====================================================*)


fun proof_of_linform sg vars f = 
  let fun proof_of_linformh prt = 
  case prt of
    (LfAt (at)) =>  prove_elementar sg "lf" (HOLogic.mk_eq (at, linform vars at))
   |(LfAtdvd (Const("Divides.op dvd",_)$d$t)) => (prove_elementar sg "lf" (HOLogic.mk_eq (t, lint vars t))) RS (instantiate' [] [None , None, Some (cterm_of sg d)](linearize_dvd))
   |(Lffm (fm)) => (instantiate' [Some cboolT] [Some (cterm_of sg fm)] refl)
   |(LfConst (s,pr1,pr2)) =>
     let val th1 = proof_of_linformh pr1
	 val th2 = proof_of_linformh pr2
     in case s of
       "CJ" => [th1,th2] MRS (qe_conjI)
      |"DJ" =>[th1,th2] MRS (qe_disjI)
      |"IM" =>[th1,th2] MRS (qe_impI)
      |"EQ" =>[th1,th2] MRS (qe_eqI)
     end
   |(LfNot(pr)) => 
     let val th = proof_of_linformh pr
     in (th RS (qe_Not))
     end
   |(LfQ(s,xn,xT,pr)) => 
     let val th = forall_intr (cterm_of sg (Free(xn,xT)))(proof_of_linformh pr)
     in if s = "Ex" 
        then (th COMP(qe_exI) )
        else (th COMP(qe_ALLI) )
     end
in
 proof_of_linformh (linform_wp f)
end;

end;
