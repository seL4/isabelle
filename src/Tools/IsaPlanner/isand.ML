(*  Title:      Tools/IsaPlanner/isand.ML
    Author:     Lucas Dixon, University of Edinburgh

Natural Deduction tools.

For working with Isabelle theorems in a natural detuction style.
ie, not having to deal with meta level quantified varaibles,
instead, we work with newly introduced frees, and hide the
"all"'s, exporting results from theorems proved with the frees, to
solve the all cases of the previous goal. This allows resolution
to do proof search normally.

Note: A nice idea: allow exporting to solve any subgoal, thus
allowing the interleaving of proof, or provide a structure for the
ordering of proof, thus allowing proof attempts in parrell, but
recording the order to apply things in.

THINK: are we really ok with our varify name w.r.t the prop - do
we also need to avoid names in the hidden hyps? What about
unification contraints in flex-flex pairs - might they also have
extra free vars?
*)

signature ISA_ND =
sig
  (* inserting meta level params for frees in the conditions *)
  val allify_conditions : (term -> cterm) -> (string * typ) list -> thm -> thm * cterm list

  val variant_names : Proof.context -> term list -> string list -> string list

  (* meta level fixed params (i.e. !! vars) *)
  val fix_alls_term : Proof.context -> int -> term -> term * term list

  val unfix_frees : cterm list -> thm -> thm

  (* assumptions/subgoals *)
  val fixed_subgoal_thms : Proof.context -> thm -> thm list * (thm list -> thm)
end

structure IsaND : ISA_ND =
struct

(* Given ctertmify function, (string,type) pairs capturing the free
vars that need to be allified in the assumption, and a theorem with
assumptions possibly containing the free vars, then we give back the
assumptions allified as hidden hyps.

Given: x
th: A vs ==> B vs
Results in: "B vs" [!!x. A x]
*)
fun allify_conditions ctermify Ts th =
    let
      val premts = Thm.prems_of th;

      fun allify_prem_var (vt as (n,ty),t)  =
          (Logic.all_const ty) $ (Abs(n,ty,Term.abstract_over (Free vt, t)))

      fun allify_prem Ts p = List.foldr allify_prem_var p Ts

      val cTs = map (ctermify o Free) Ts
      val cterm_asms = map (ctermify o allify_prem Ts) premts
      val allifyied_asm_thms = map (Drule.forall_elim_list cTs o Thm.assume) cterm_asms
    in
      (Library.foldl (fn (x,y) => y COMP x) (th, allifyied_asm_thms), cterm_asms)
    end;

(* make free vars into schematic vars with index zero *)
fun unfix_frees frees =
     fold (K (Thm.forall_elim_var 0)) frees
     o Drule.forall_intr_list frees;

(* datatype to capture an exported result, ie a fix or assume. *)
datatype export =
         export of {fixes : Thm.cterm list, (* fixed vars *)
                    assumes : Thm.cterm list, (* hidden hyps/assumed prems *)
                    sgid : int,
                    gth :  Thm.thm}; (* subgoal/goalthm *)

(* exporting function that takes a solution to the fixed/assumed goal,
and uses this to solve the subgoal in the main theorem *)
fun export_solution (export {fixes = cfvs, assumes = hcprems,
                             sgid = i, gth = gth}) solth =
    let
      val solth' =
          solth |> Drule.implies_intr_list hcprems
                |> Drule.forall_intr_list cfvs
    in Drule.compose_single (solth', i, gth) end;

fun variant_names ctxt ts xs =
  let
    val names =
      Variable.names_of ctxt
      |> (fold o fold_aterms)
          (fn Var ((a, _), _) => Name.declare a
            | Free (a, _) => Name.declare a
            | _ => I) ts;
  in fst (fold_map Name.variant xs names) end;

(* fix parameters of a subgoal "i", as free variables, and create an
exporting function that will use the result of this proved goal to
show the goal in the original theorem.

Note, an advantage of this over Isar is that it supports instantiation
of unkowns in the earlier theorem, ie we can do instantiation of meta
vars!

avoids constant, free and vars names.

loosely corresponds to:
Given "[| SG0; ... !! x. As ==> SGi x; ... SGm |] ==> G" : thm
Result:
  ("(As ==> SGi x') ==> (As ==> SGi x')" : thm,
   expf :
     ("As ==> SGi x'" : thm) ->
     ("[| SG0; ... SGi-1; SGi+1; ... SGm |] ==> G") : thm)
*)
fun fix_alls_term ctxt i t =
    let
      val gt = Logic.get_goal t i;
      val body = Term.strip_all_body gt;
      val alls = rev (Term.strip_all_vars gt);
      val xs = variant_names ctxt [t] (map fst alls);
      val fvs = map Free (xs ~~ map snd alls);
    in ((subst_bounds (fvs,body)), fvs) end;

fun fix_alls_cterm ctxt i th =
    let
      val ctermify = Thm.cterm_of (Thm.theory_of_thm th);
      val (fixedbody, fvs) = fix_alls_term ctxt i (Thm.prop_of th);
      val cfvs = rev (map ctermify fvs);
      val ct_body = ctermify fixedbody
    in
      (ct_body, cfvs)
    end;

fun fix_alls' ctxt i = apfst Thm.trivial o fix_alls_cterm ctxt i;


(* hide other goals *)
(* note the export goal is rotated by (i - 1) and will have to be
unrotated to get backto the originial position(s) *)
fun hide_other_goals th =
    let
      (* tl beacuse fst sg is the goal we are interested in *)
      val cprems = tl (Drule.cprems_of th)
      val aprems = map Thm.assume cprems
    in
      (Drule.implies_elim_list (Drule.rotate_prems 1 th) aprems,
       cprems)
    end;

(* a nicer version of the above that leaves only a single subgoal (the
other subgoals are hidden hyps, that the exporter suffles about)
namely the subgoal that we were trying to solve. *)
(* loosely corresponds to:
Given "[| SG0; ... !! x. As ==> SGi x; ... SGm |] ==> G" : thm
Result:
  ("(As ==> SGi x') ==> SGi x'" : thm,
   expf :
     ("SGi x'" : thm) ->
     ("[| SG0; ... SGi-1; SGi+1; ... SGm |] ==> G") : thm)
*)
fun fix_alls ctxt i th =
    let
      val (fixed_gth, fixedvars) = fix_alls' ctxt i th
      val (sml_gth, othergoals) = hide_other_goals fixed_gth
    in
      (sml_gth, export {fixes = fixedvars,
                        assumes = othergoals,
                        sgid = i, gth = th})
    end;


(* Fixme: allow different order of subgoals given to expf *)
(* make each subgoal into a separate thm that needs to be proved *)
(* loosely corresponds to:
Given
  "[| SG0; ... SGm |] ==> G" : thm
Result:
(["SG0 ==> SG0", ... ,"SGm ==> SGm"] : thm list, -- goals
 ["SG0", ..., "SGm"] : thm list ->   -- export function
   "G" : thm)
*)
fun subgoal_thms th =
    let
      val t = (prop_of th);

      val prems = Logic.strip_imp_prems t;

      val sgn = Thm.theory_of_thm th;
      val ctermify = Thm.cterm_of sgn;

      val aprems = map (Thm.trivial o ctermify) prems;

      fun explortf premths =
          Drule.implies_elim_list th premths
    in
      (aprems, explortf)
    end;


(* Fixme: allow different order of subgoals in exportf *)
(* as above, but also fix all parameters in all subgoals, and uses
fix_alls, not fix_alls', ie doesn't leave extra asumptions as apparent
subgoals. *)
(* loosely corresponds to:
Given
  "[| !! x0s. A0s x0s ==> SG0 x0s;
      ...; !! xms. Ams xms ==> SGm xms|] ==> G" : thm
Result:
(["(A0s x0s' ==> SG0 x0s') ==> SG0 x0s'",
  ... ,"(Ams xms' ==> SGm xms') ==> SGm xms'"] : thm list, -- goals
 ["SG0 x0s'", ..., "SGm xms'"] : thm list ->   -- export function
   "G" : thm)
*)
(* requires being given solutions! *)
fun fixed_subgoal_thms ctxt th =
    let
      val (subgoals, expf) = subgoal_thms th;
(*       fun export_sg (th, exp) = exp th; *)
      fun export_sgs expfs solthms =
          expf (map2 (curry (op |>)) solthms expfs);
(*           expf (map export_sg (ths ~~ expfs)); *)
    in
      apsnd export_sgs (Library.split_list (map (apsnd export_solution o
                                                 fix_alls ctxt 1) subgoals))
    end;

end;
