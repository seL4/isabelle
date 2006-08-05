(*  Title:      HOL/Tools/function_package/fundef_package.ML
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen

A package for general recursive function definitions.

Automatic splitting of overlapping constructor patterns. This is a preprocessing step which
turns a specification with overlaps into an overlap-free specification.

*)

signature FUNDEF_SPLIT =
sig
  val split_some_equations :
    Proof.context -> (('a * ('b * bool)) * term) list -> (('a * 'b) * term list) list

end

structure FundefSplit : FUNDEF_SPLIT =
struct


(* We use proof context for the variable management *)
(* FIXME: no __ *)

fun new_var ctx vs T =
    let
      val [v] = Variable.variant_frees ctx vs [("v", T)]
    in
      (Free v :: vs, Free v)
    end

fun saturate ctx vs t =
    fold (fn T => fn (vs, t) => new_var ctx vs T |> apsnd (curry op $ t))
         (binder_types (fastype_of t)) (vs, t)


(* This is copied from "fundef_datatype.ML" *)
fun inst_constrs_of thy (T as Type (name, _)) =
        map (fn (Cn,CT) => Envir.subst_TVars (Sign.typ_match thy (body_type CT, T) Vartab.empty) (Const (Cn, CT)))
            (the (DatatypePackage.get_datatype_constrs thy name))
  | inst_constrs_of thy t = (print t; sys_error "inst_constrs_of")



fun pattern_subtract_subst ctx vs _ (Free v2) = []
  | pattern_subtract_subst ctx vs (v as (Free (_, T))) t' =
    let
      fun foo constr =
          let
            val (vs', t) = saturate ctx vs constr
            val substs = pattern_subtract_subst ctx vs' t t'
          in
            map (cons (v, t)) substs
          end
    in
      flat (map foo (inst_constrs_of (ProofContext.theory_of ctx) T))
    end
  | pattern_subtract_subst ctx vs t t' =
    let
      val (C, ps) = strip_comb t
      val (C', qs) = strip_comb t'
    in
      if C = C'
      then flat (map2 (pattern_subtract_subst ctx vs) ps qs)
      else [[]]
    end

fun pattern_subtract_parallel ctx vs ps qs =
    flat (map2 (pattern_subtract_subst ctx vs) ps qs)



(* ps - qs *)
fun pattern_subtract ctx eq2 eq1 =
    let
      val _ $ (_ $ lhs1 $ _) = eq1
      val _ $ (_ $ lhs2 $ _) = eq2

      val thy = ProofContext.theory_of ctx
      val vs = term_frees eq1
    in
      map (fn sigma => Pattern.rewrite_term thy sigma [] eq1) (pattern_subtract_subst ctx vs lhs1 lhs2)
    end


(* ps - p' *)
fun pattern_subtract_from_many ctx p'=
    flat o map (pattern_subtract ctx p')

(* in reverse order *)
fun pattern_subtract_many ctx ps' =
    fold_rev (pattern_subtract_from_many ctx) ps'



fun split_all_equations ctx eqns =
    let
      fun split_aux prev [] = []
        | split_aux prev (e::es) = pattern_subtract_many ctx prev [e] @ split_aux (e::prev) es
    in
      split_aux [] eqns
end


fun split_some_equations ctx eqns =
    let
      fun split_aux prev [] = []
        | split_aux prev (((n, (att, true)), eq) :: es) = ((n, att), pattern_subtract_many ctx prev [eq])
                                                          :: split_aux (eq :: prev) es
        | split_aux prev (((n, (att, false)), eq) :: es) = ((n, att), [eq])
                                                                :: split_aux (eq :: prev) es
    in
      split_aux [] eqns
    end

end
