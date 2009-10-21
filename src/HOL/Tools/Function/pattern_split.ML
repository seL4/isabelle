(*  Title:      HOL/Tools/Function/pattern_split.ML
    Author:     Alexander Krauss, TU Muenchen

A package for general recursive function definitions.

Automatic splitting of overlapping constructor patterns. This is a preprocessing step which
turns a specification with overlaps into an overlap-free specification.

*)

signature FUNDEF_SPLIT =
sig
  val split_some_equations :
      Proof.context -> (bool * term) list -> term list list

  val split_all_equations :
      Proof.context -> term list -> term list list
end

structure FundefSplit : FUNDEF_SPLIT =
struct

open FundefLib

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
    map (fn (Cn,CT) =>
          Envir.subst_term_types (Sign.typ_match thy (body_type CT, T) Vartab.empty) (Const (Cn, CT)))
        (the (Datatype.get_constrs thy name))
  | inst_constrs_of thy T = raise TYPE ("inst_constrs_of", [T], [])
                            
                            
                            

fun join ((vs1,sub1), (vs2,sub2)) = (merge (op aconv) (vs1,vs2), sub1 @ sub2)
fun join_product (xs, ys) = map_product (curry join) xs ys

fun join_list [] = []
  | join_list xs = foldr1 (join_product) xs


exception DISJ

fun pattern_subtract_subst ctx vs t t' =
    let
      exception DISJ
      fun pattern_subtract_subst_aux vs _ (Free v2) = []
        | pattern_subtract_subst_aux vs (v as (Free (_, T))) t' =
          let
            fun foo constr =
                let
                  val (vs', t) = saturate ctx vs constr
                  val substs = pattern_subtract_subst ctx vs' t t'
                in
                  map (fn (vs, subst) => (vs, (v,t)::subst)) substs
                end
          in
            maps foo (inst_constrs_of (ProofContext.theory_of ctx) T)
          end
        | pattern_subtract_subst_aux vs t t' =
          let
            val (C, ps) = strip_comb t
            val (C', qs) = strip_comb t'
          in
            if C = C'
            then flat (map2 (pattern_subtract_subst_aux vs) ps qs)
            else raise DISJ
          end
    in
      pattern_subtract_subst_aux vs t t'
      handle DISJ => [(vs, [])]
    end


(* p - q *)
fun pattern_subtract ctx eq2 eq1 =
    let
      val thy = ProofContext.theory_of ctx
                
      val (vs, feq1 as (_ $ (_ $ lhs1 $ _))) = dest_all_all eq1
      val (_,  _ $ (_ $ lhs2 $ _)) = dest_all_all eq2
                                     
      val substs = pattern_subtract_subst ctx vs lhs1 lhs2
                   
      fun instantiate (vs', sigma) =
          let
            val t = Pattern.rewrite_term thy sigma [] feq1
          in
            fold_rev Logic.all (inter (op =) (map Free (frees_in_term ctx t), vs')) t
          end
    in
      map instantiate substs
    end
      

(* ps - p' *)
fun pattern_subtract_from_many ctx p'=
    maps (pattern_subtract ctx p')

(* in reverse order *)
fun pattern_subtract_many ctx ps' =
    fold_rev (pattern_subtract_from_many ctx) ps'



fun split_some_equations ctx eqns =
    let
      fun split_aux prev [] = []
        | split_aux prev ((true, eq) :: es) = pattern_subtract_many ctx prev [eq]
                                              :: split_aux (eq :: prev) es
        | split_aux prev ((false, eq) :: es) = [eq]
                                               :: split_aux (eq :: prev) es
    in
      split_aux [] eqns
    end
    
fun split_all_equations ctx =
    split_some_equations ctx o map (pair true)




end
