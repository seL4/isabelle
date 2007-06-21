(*
    ID:         $Id$
    Author:     Amine Chaieb and Tobias Nipkow, TU Muenchen

File containing the implementation of the proof protocoling
and proof generation for multiple quantified formulae.
*)

signature QELIM =
sig
 val standard_qelim_conv: Proof.context -> (cterm list -> cterm -> thm) ->
   (cterm list -> Conv.conv) -> (cterm list -> cterm -> thm) -> cterm -> thm
 val gen_qelim_conv: Proof.context -> Conv.conv -> Conv.conv -> Conv.conv ->
   (cterm -> 'a -> 'a) -> 'a -> ('a -> cterm -> thm) ->
   ('a -> Conv.conv) -> ('a -> cterm -> thm) -> Conv.conv
end;

structure Qelim : QELIM =
struct

open Conv;

local
 val all_not_ex = mk_meta_eq @{thm "all_not_ex"}
in
fun gen_qelim_conv ctxt precv postcv simpex_conv ins env atcv ncv qcv  = 
 let 
  val thy = ProofContext.theory_of ctxt
  fun conv env p =
   case (term_of p) of 
    Const(s,T)$_$_ => if domain_type T = HOLogic.boolT 
                         andalso s mem ["op &","op |","op -->","op ="]
                     then binop_conv (conv env) p else atcv env p
  | Const("Not",_)$_ => arg_conv (conv env) p
  | Const("Ex",_)$Abs(s,_,_) => 
    let 
     val (e,p0) = Thm.dest_comb p
     val (x,p') = Thm.dest_abs (SOME s) p0
     val env' = ins x env
     val th = Thm.abstract_rule s x ((conv env' then_conv ncv env') p')
                   |> Drule.arg_cong_rule e
     val th' = simpex_conv (Thm.rhs_of th)
     val (l,r) = Thm.dest_equals (cprop_of th')
    in if is_refl th' then Thm.transitive th (qcv env (Thm.rhs_of th))
       else Thm.transitive (Thm.transitive th th') (conv env r) end
  | Const("Ex",_)$ _ => (eta_conv thy then_conv conv env) p 
  | Const("All",_)$_ => 
    let 
     val p = Thm.dest_arg p
     val ([(_,T)],[]) = Thm.match (@{cpat "All"}, Thm.dest_fun p)
     val th = instantiate' [SOME T] [SOME p] all_not_ex 
    in transitive th (conv env (Thm.rhs_of th)) 
    end
  | _ => atcv env p
 in precv then_conv (conv env) then_conv postcv end
end;

fun cterm_frees ct = 
 let fun h acc t = 
   case (term_of t) of 
    _$_ => h (h acc (Thm.dest_arg t)) (Thm.dest_fun t)
  | Abs(_,_,_) => Thm.dest_abs NONE t ||> h acc |> uncurry (remove (op aconvc))
  | Free _ => insert (op aconvc) t acc
  | _ => acc
 in h [] ct end;

local
val pcv = Simplifier.rewrite 
                 (HOL_basic_ss addsimps (simp_thms @ ex_simps @ all_simps) 
                     @ [@{thm "all_not_ex"}, not_all,ex_disj_distrib])
in 
fun standard_qelim_conv ctxt atcv ncv qcv p = 
    gen_qelim_conv ctxt pcv pcv pcv cons (cterm_frees p) atcv ncv qcv p 
end;

end;
