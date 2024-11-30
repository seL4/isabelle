(*  Title:      HOL/Tools/Function/pattern_split.ML
    Author:     Alexander Krauss, TU Muenchen

Fairly ad-hoc pattern splitting.
*)

signature FUNCTION_SPLIT =
sig
  val split_some_equations :
      Proof.context -> (bool * term) list -> term list list

  val split_all_equations :
      Proof.context -> term list -> term list list
end

structure Function_Split : FUNCTION_SPLIT =
struct

open Function_Lib

fun new_var ctxt vs T =
  let
    val v = singleton (Variable.variant_names (fold Variable.declare_names vs ctxt)) ("v", T)
  in
    (Free v :: vs, Free v)
  end

fun saturate ctxt vs t =
  fold (fn T => fn (vs, t) => new_var ctxt vs T |> apsnd (curry op $ t))
    (binder_types (fastype_of t)) (vs, t)


fun join ((vs1,sub1), (vs2,sub2)) = (merge (op aconv) (vs1,vs2), sub1 @ sub2)
fun join_product (xs, ys) = map_product (curry join) xs ys

exception DISJ

fun pattern_subtract_subst ctxt vs t t' =
  let
    exception DISJ
    fun pattern_subtract_subst_aux vs _ (Free v2) = []
      | pattern_subtract_subst_aux vs (v as (Free (_, T))) t' =
          let
            fun aux constr =
              let
                val (vs', t) = saturate ctxt vs constr
                val substs = pattern_subtract_subst ctxt vs' t t'
              in
                map (fn (vs, subst) => (vs, (v,t)::subst)) substs
              end
          in
            maps aux (inst_constrs_of ctxt T)
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
fun pattern_subtract ctxt eq2 eq1 =
  let
    val thy = Proof_Context.theory_of ctxt

    val (vs, feq1 as (_ $ (_ $ lhs1 $ _))) = dest_all_all eq1
    val (_,  _ $ (_ $ lhs2 $ _)) = dest_all_all eq2

    val substs = pattern_subtract_subst ctxt vs lhs1 lhs2

    fun instantiate (vs', sigma) =
      let
        val t = Pattern.rewrite_term thy sigma [] feq1
        val xs = fold_aterms
          (fn x as Free (a, _) =>
              if not (Variable.is_fixed ctxt a) andalso member (op =) vs' x
              then insert (op =) x else I
            | _ => I) t [];
      in fold Logic.all xs t end
  in
    map instantiate substs
  end

(* ps - p' *)
fun pattern_subtract_from_many ctxt p'=
  maps (pattern_subtract ctxt p')

(* in reverse order *)
fun pattern_subtract_many ctxt ps' =
  fold_rev (pattern_subtract_from_many ctxt) ps'

fun split_some_equations ctxt eqns =
  let
    fun split_aux prev [] = []
      | split_aux prev ((true, eq) :: es) =
          pattern_subtract_many ctxt prev [eq] :: split_aux (eq :: prev) es
      | split_aux prev ((false, eq) :: es) =
          [eq] :: split_aux (eq :: prev) es
  in
    split_aux [] eqns
  end

fun split_all_equations ctxt =
  split_some_equations ctxt o map (pair true)


end
