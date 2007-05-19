(*  Title:      HOL/Integ/qelim.ML
    ID:         $Id$
    Author:     Amine Chaieb and Tobias Nipkow, TU Muenchen

File containing the implementation of the proof protocoling
and proof generation for multiple quantified formulae.
*)

signature QELIM =
 sig
 val tproof_of_mlift_qelim: theory -> (term -> bool) ->
   (string list -> term -> thm) -> (term -> thm) ->
   (term -> thm) -> term -> thm
 val standard_qelim_conv: (cterm list -> cterm -> thm) ->
   (cterm list -> Conv.conv) -> (cterm list -> cterm -> thm) -> cterm -> thm
 val gen_qelim_conv: Conv.conv -> Conv.conv -> Conv.conv ->
   (cterm -> 'a -> 'a) -> 'a -> ('a -> cterm -> thm) ->
   ('a -> Conv.conv) -> ('a -> cterm -> thm) -> Conv.conv

end;

structure Qelim : QELIM =
struct
open CooperDec;
open CooperProof;
open Conv;

val cboolT = ctyp_of HOL.thy HOLogic.boolT;

(* List of the theorems to be used in the following*)

val qe_ex_conj = thm "qe_ex_conj";
val qe_ex_nconj = thm "qe_ex_nconj";
val qe_ALL = thm "qe_ALL";


(*============= Compact version =====*)


fun decomp_qe is_at afnp nfnp qfnp sg P = 
   if is_at P then ([], fn [] => afnp [] P) else 
   case P of
   (Const("op &",_)$A$B) => ([A,B], fn [th1,th2] => [th1,th2] MRS qe_conjI)
   |(Const("op |",_)$A$B) => ([A,B], fn [th1,th2] => [th1,th2] MRS qe_disjI)
   |(Const("op -->",_)$A$B) => ([A,B], fn [th1,th2] => [th1,th2] MRS qe_impI)
   |(Const("op =", Type ("fun",[Type ("bool", []),_]))$A$B) => ([A,B], fn [th1,th2] => [th1,th2] MRS qe_eqI)
   |(Const("Not",_)$p) => ([p],fn [th] => th RS qe_Not)
   |(Const("Ex",_)$Abs(xn,xT,p)) => 
      let val (xn1,p1) = Syntax.variant_abs(xn,xT,p) 
      in ([p1],
        fn [th1_1] => 
          let val th2 = [th1_1,nfnp (snd (qe_get_terms th1_1))] MRS trans
              val eth1 = (forall_intr (cterm_of sg (Free(xn1,xT))) th2) COMP  qe_exI
              val th3 = qfnp (snd(qe_get_terms eth1))
          in [eth1,th3] MRS trans
          end )
      end

   |(Const("All",_)$Abs(xn,xT,p)) => ([(HOLogic.exists_const xT)$Abs(xn,xT,HOLogic.Not $ p)], fn [th] => th RS qe_ALL)
   | _ => ([],fn [] => instantiate' [SOME (ctyp_of sg (type_of P))] [SOME (cterm_of sg P)] refl);
 

fun tproof_of_mlift_qelim sg isat afnp nfnp qfnp p = 
   let val th1 = thm_of sg (decomp_qe isat afnp nfnp qfnp sg) p
       val th2 = nfnp (snd (qe_get_terms th1))
    in [th1,th2] MRS trans
    end;

val is_refl = op aconv o Logic.dest_equals o Thm.prop_of;

fun gen_qelim_conv precv postcv simpex_conv ins env atcv ncv qcv  = 
 let fun conv p =
  case (term_of p) of 
   Const(s,T)$_$_ => if domain_type T = HOLogic.boolT 
                        andalso s mem ["op &","op |","op -->","op ="]
                    then binop_conv conv p else atcv env p
 | Const("Not",_)$_ => arg_conv conv p
 | Const("Ex",_)$Abs(s,_,_) => 
   let 
    val (e,p0) = Thm.dest_comb p
    val (x,p') = Thm.dest_abs (SOME s) p0
    val th = Thm.abstract_rule s x 
                  (((gen_qelim_conv precv postcv simpex_conv ins (ins x env) atcv ncv qcv) 
                      then_conv (ncv (ins x env))) p')
                  |> Drule.arg_cong_rule e
    val th' = simpex_conv (Thm.rhs_of th)
    val (l,r) = Thm.dest_equals (cprop_of th')
   in if is_refl th' then Thm.transitive th (qcv env (Thm.rhs_of th))
      else Thm.transitive (Thm.transitive th th') (conv r) end
 | _ => atcv env p
 in precv then_conv conv then_conv postcv end;

fun cterm_frees ct = 
 let fun h acc t = 
   case (term_of t) of 
    _$_ => h (h acc (Thm.dest_arg t)) (Thm.dest_fun t)
  | Abs(_,_,_) => Thm.dest_abs NONE t ||> h acc |> uncurry (remove (op aconvc))
  | Free _ => insert (op aconvc) t acc
  | _ => acc
 in h [] ct end;

val standard_qelim_conv = 
 let val pcv = Simplifier.rewrite 
                 (HOL_basic_ss addsimps (simp_thms @ (List.take(ex_simps,4)) 
                     @ [not_all,ex_disj_distrib]))
 in fn atcv => fn ncv => fn qcv => fn p => 
       gen_qelim_conv pcv pcv pcv (curry (op ::)) (cterm_frees p) atcv ncv qcv p 
 end;

end;
