(*  Title:      HOL/Integ/qelim.ML
    ID:         $Id$
    Author:     Amine Chaieb and Tobias Nipkow, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

File containing the implementation of the proof protocoling
and proof generation for multiple quantified formulae.
*)

signature QELIM =
 sig
 val tproof_of_mlift_qelim: Sign.sg -> (term -> bool) ->
   (string list -> term -> thm) -> (term -> thm) ->
   (term -> thm) -> term -> thm

end;

structure Qelim : QELIM =
struct
open CooperDec;
open CooperProof;

val cboolT = ctyp_of (sign_of HOL.thy) HOLogic.boolT;

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
      let val (xn1,p1) = variant_abs(xn,xT,p) 
      in ([p1],
        fn [th1_1] => 
          let val th2 = [th1_1,nfnp (snd (qe_get_terms th1_1))] MRS trans
              val eth1 = (forall_intr (cterm_of sg (Free(xn1,xT))) th2) COMP  qe_exI
              val th3 = qfnp (snd(qe_get_terms eth1))
          in [eth1,th3] MRS trans
          end )
      end

   |(Const("All",_)$Abs(xn,xT,p)) => ([(HOLogic.exists_const xT)$Abs(xn,xT,HOLogic.Not $ p)], fn [th] => th RS qe_ALL)
   | _ => ([],fn [] => instantiate' [Some (ctyp_of sg (type_of P))] [Some (cterm_of sg P)] refl);
 

fun tproof_of_mlift_qelim sg isat afnp nfnp qfnp p = 
   let val th1 = thm_of sg (decomp_qe isat afnp nfnp qfnp sg) p
       val th2 = nfnp (snd (qe_get_terms th1))
    in [th1,th2] MRS trans
    end;
end;
