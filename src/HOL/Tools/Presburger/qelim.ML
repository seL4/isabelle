(*  Title:      HOL/Tools/Presburger/qelim.ML
    ID:         $Id$
    Author:     Amine Chaieb and Tobias Nipkow, TU Muenchen

File containing the implementation of the proof protocoling
and proof generation for multiple quantified formulae.
*)

signature QELIM =
 sig
 val standard_qelim_conv: (cterm list -> cterm -> thm) ->
   (cterm list -> Conv.conv) -> (cterm list -> cterm -> thm) -> cterm -> thm
 val gen_qelim_conv: Conv.conv -> Conv.conv -> Conv.conv ->
   (cterm -> 'a -> 'a) -> 'a -> ('a -> cterm -> thm) ->
   ('a -> Conv.conv) -> ('a -> cterm -> thm) -> Conv.conv

end;

structure Qelim : QELIM =
struct
open Conv;

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
