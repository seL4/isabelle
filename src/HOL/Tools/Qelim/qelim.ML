(*  Title:      HOL/Tools/Qelim/qelim.ML
    Author:     Amine Chaieb, TU Muenchen

Generic quantifier elimination conversions for HOL formulae.
*)

signature QELIM =
sig
 val gen_qelim_conv: conv -> conv -> conv -> (cterm -> 'a -> 'a) -> 'a ->
  ('a -> conv) -> ('a -> conv) -> ('a -> conv) -> conv
 val standard_qelim_conv: (cterm list -> conv) -> (cterm list -> conv) ->
  (cterm list -> conv) -> conv
end;

structure Qelim: QELIM =
struct

val all_not_ex = mk_meta_eq @{thm "all_not_ex"};

fun gen_qelim_conv precv postcv simpex_conv ins env atcv ncv qcv =
 let
  fun conv env p =
   case (term_of p) of
    Const(s,T)$_$_ =>
       if domain_type T = HOLogic.boolT
          andalso member (op =) [@{const_name HOL.conj}, @{const_name HOL.disj},
            @{const_name HOL.implies}, @{const_name HOL.eq}] s
       then Conv.binop_conv (conv env) p
       else atcv env p
  | Const(@{const_name Not},_)$_ => Conv.arg_conv (conv env) p
  | Const(@{const_name Ex},_)$Abs(s,_,_) =>
    let
     val (e,p0) = Thm.dest_comb p
     val (x,p') = Thm.dest_abs (SOME s) p0
     val env' = ins x env
     val th = Thm.abstract_rule s x ((conv env' then_conv ncv env') p')
                   |> Drule.arg_cong_rule e
     val th' = simpex_conv (Thm.rhs_of th)
     val (l,r) = Thm.dest_equals (cprop_of th')
    in if Thm.is_reflexive th' then Thm.transitive th (qcv env (Thm.rhs_of th))
       else Thm.transitive (Thm.transitive th th') (conv env r) end
  | Const(@{const_name Ex},_)$ _ => (Thm.eta_long_conversion then_conv conv env) p
  | Const(@{const_name All},_)$_ =>
    let
     val p = Thm.dest_arg p
     val ([(_,T)],[]) = Thm.match (@{cpat "All"}, Thm.dest_fun p)
     val th = instantiate' [SOME T] [SOME p] all_not_ex
    in Thm.transitive th (conv env (Thm.rhs_of th))
    end
  | _ => atcv env p
 in precv then_conv (conv env) then_conv postcv end

(* Instantiation of some parameter for most common cases *)

local
val pcv =
  Simplifier.rewrite
    (HOL_basic_ss addsimps @{thms simp_thms ex_simps all_simps all_not_ex not_all ex_disj_distrib});

in fun standard_qelim_conv atcv ncv qcv p =
      gen_qelim_conv pcv pcv pcv cons (Thm.add_cterm_frees p []) atcv ncv qcv p
end;

end;
