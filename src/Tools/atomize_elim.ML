(*  Title:      Tools/atomize_elim.ML
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen

Turn elimination rules into atomic expressions in the object logic.
*)

signature ATOMIZE_ELIM =
sig
  val declare_atomize_elim : attribute  

  val atomize_elim : Proof.context -> conv
  val full_atomize_elim : Proof.context -> conv

  val atomize_elim_tac : Proof.context -> int -> tactic

  val setup : theory -> theory
end

structure AtomizeElim : ATOMIZE_ELIM =
struct

(* theory data *)
structure AtomizeElimData = TheoryDataFun
(
  type T = thm list;
  val empty = [];
  val copy = I;
  val extend = I;
  fun merge _ = Thm.merge_thms
);

val add_elim = AtomizeElimData.map o Thm.add_thm
val declare_atomize_elim = Thm.declaration_attribute (fn th => Context.mapping (add_elim th) I);


(* More conversions: *)
local open Conv in

(* Compute inverse permutation *)
fun invert_perm pi =
      (pi @ ((0 upto (fold (curry Int.max) pi 0)) \\ pi))
           |> map_index I
           |> sort (int_ord o pairself snd)
           |> map fst

(* rearrange_prems as a conversion *)
fun rearrange_prems_conv pi ct =
    let
      val pi' = 0 :: map (curry op + 1) pi
      val fwd  = trivial ct
                  |> Drule.rearrange_prems pi'
      val back = trivial (snd (Thm.dest_implies (cprop_of fwd)))
                  |> Drule.rearrange_prems (invert_perm pi')
    in equal_intr fwd back end


(* convert !!thesis. (!!x y z. ... => thesis) ==> ... 
                     ==> (!!a b c. ... => thesis)
                     ==> thesis

   to

   (EX x y z. ...) | ... | (EX a b c. ...)
*)
fun atomize_elim ctxt ct =
    (forall_conv (K (prems_conv ~1 ObjectLogic.atomize_prems)) ctxt
    then_conv MetaSimplifier.rewrite true (AtomizeElimData.get (ProofContext.theory_of ctxt))
    then_conv (fn ct' => if can ObjectLogic.dest_judgment ct'
                         then all_conv ct'
                         else raise CTERM ("atomize_elim", [ct', ct])))
    ct


(* Move the thesis-quantifier inside over other quantifiers and unrelated prems *)
fun thesis_miniscope_conv inner_cv ctxt =
    let
      (* check if the outermost quantifier binds the conclusion *)
      fun is_forall_thesis (Const ("all", _) $ Abs (_, T, b)) =
          exists_subterm (fn Free (n, _) => n = "" | _ => false) 
                         (Logic.strip_assums_concl (subst_bound (Free ("", dummyT), b)))
        | is_forall_thesis _ = false

      (* move unrelated assumptions out of the quantification *)
      fun movea_conv ctxt ct =
          let
            val _ $ Abs (_, _, b) = term_of ct
            val idxs = fold_index (fn (i, t) => not (loose_bvar1 (t, 0)) ? cons i)
                       (Logic.strip_imp_prems b) []
                       |> rev

            fun skip_over_assm cv = rewr_conv (Thm.symmetric Drule.norm_hhf_eq)
                                    then_conv (implies_concl_conv cv)
          in
            (forall_conv (K (rearrange_prems_conv idxs)) ctxt
             then_conv (funpow (length idxs) skip_over_assm (inner_cv ctxt)))
            ct
          end

      (* move current quantifier to the right *)
      fun moveq_conv ctxt = 
          (rewr_conv @{thm swap_params} then_conv (forall_conv (uncurry (K moveq_conv)) ctxt))
          else_conv (movea_conv ctxt)

      fun ms_conv ctxt ct = 
          if is_forall_thesis (term_of ct)
          then moveq_conv ctxt ct
          else (implies_concl_conv (ms_conv ctxt)
            else_conv
            (forall_conv (uncurry (K ms_conv)) ctxt))
            ct
    in
      ms_conv ctxt 
    end

val full_atomize_elim = thesis_miniscope_conv atomize_elim

end


fun atomize_elim_tac ctxt = CSUBGOAL (fn (csubg, i) =>
    let
      val _ $ thesis = Logic.strip_assums_concl (term_of csubg)
                       
      (* Introduce a quantifier first if the thesis is not bound *)
      val quantify_thesis = 
          if is_Bound thesis then all_tac
          else let
              val cthesis = cterm_of (theory_of_cterm csubg) thesis
              val rule = instantiate' [SOME (ctyp_of_term cthesis)] [NONE, SOME cthesis] 
                         @{thm meta_spec}
            in
              Thm.compose_no_flatten false (rule, 1) i
            end
    in
      quantify_thesis
      THEN (CONVERSION (full_atomize_elim ctxt) i)
    end)

val setup = Method.add_methods
  [("atomize_elim", Method.ctxt_args (Method.SIMPLE_METHOD' o atomize_elim_tac),
    "convert obtains statement to atomic object logic goal")]
  #> Attrib.add_attributes 
      [("atomize_elim", Attrib.no_args declare_atomize_elim, "declaration of atomize_elim rewrite rule")]

end
