(*  Title:      HOL/Tools/Qelim/qelim.ML
    ID:         $Id$
    Author:     Amine Chaieb and Tobias Nipkow, TU Muenchen

Proof protocoling and proof generation for multiple quantified
formulae.
*)

signature QELIM =
sig
 val gen_qelim_conv: conv -> conv -> conv ->
   (cterm -> 'a -> 'a) -> 'a -> ('a -> cterm -> thm) ->
   ('a -> conv) -> ('a -> cterm -> thm) -> conv
 val standard_qelim_conv: (cterm list -> cterm -> thm) ->
   (cterm list -> conv) -> (cterm list -> cterm -> thm) -> cterm -> thm
end;

structure Qelim: QELIM =
struct

open Conv;


(* gen_qelim_conv *)

val all_not_ex = mk_meta_eq @{thm "all_not_ex"};

fun gen_qelim_conv precv postcv simpex_conv ins env atcv ncv qcv =
 let
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
  | Const("Ex",_)$ _ => (Thm.eta_long_conversion then_conv conv env) p
  | Const("All",_)$_ =>
    let
     val p = Thm.dest_arg p
     val ([(_,T)],[]) = Thm.match (@{cpat "All"}, Thm.dest_fun p)
     val th = instantiate' [SOME T] [SOME p] all_not_ex
    in transitive th (conv env (Thm.rhs_of th))
    end
  | _ => atcv env p
 in precv then_conv (conv env) then_conv postcv end


(* standard_qelim_conv *)

val pcv = Simplifier.rewrite
                 (HOL_basic_ss addsimps (simp_thms @ ex_simps @ all_simps)
                     @ [@{thm "all_not_ex"}, not_all, ex_disj_distrib]);

fun standard_qelim_conv atcv ncv qcv p =
  gen_qelim_conv pcv pcv pcv cons (Thm.add_cterm_frees p []) atcv ncv qcv p;

end;
