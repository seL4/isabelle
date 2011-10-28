(*  Title:      Tools/atomize_elim.ML
    Author:     Alexander Krauss, TU Muenchen

Turn elimination rules into atomic expressions in the object logic.
*)

signature ATOMIZE_ELIM =
sig
  val declare_atomize_elim : attribute  

  val atomize_elim_conv : Proof.context -> conv
  val full_atomize_elim_conv : Proof.context -> conv

  val atomize_elim_tac : Proof.context -> int -> tactic

  val setup : theory -> theory
end

structure AtomizeElim : ATOMIZE_ELIM =
struct

(* theory data *)

structure AtomizeElimData = Named_Thms
(
  val name = @{binding atomize_elim};
  val description = "atomize_elim rewrite rule";
);

val declare_atomize_elim = AtomizeElimData.add

(* More conversions: *)
local open Conv in

(* Compute inverse permutation *)
fun invert_perm pi =
      (pi @ subtract (op =) pi (0 upto (fold Integer.max pi 0)))
           |> map_index I
           |> sort (int_ord o pairself snd)
           |> map fst

(* rearrange_prems as a conversion *)
fun rearrange_prems_conv pi ct =
    let
      val pi' = 0 :: map (Integer.add 1) pi
      val fwd  = Thm.trivial ct
                  |> Drule.rearrange_prems pi'
      val back = Thm.trivial (snd (Thm.dest_implies (cprop_of fwd)))
                  |> Drule.rearrange_prems (invert_perm pi')
    in Thm.equal_intr fwd back end


(* convert !!thesis. (!!x y z. ... => thesis) ==> ... 
                     ==> (!!a b c. ... => thesis)
                     ==> thesis

   to

   (EX x y z. ...) | ... | (EX a b c. ...)
*)
fun atomize_elim_conv ctxt ct =
    (forall_conv (K (prems_conv ~1 Object_Logic.atomize_prems)) ctxt
    then_conv Raw_Simplifier.rewrite true (AtomizeElimData.get ctxt)
    then_conv (fn ct' => if can Object_Logic.dest_judgment ct'
                         then all_conv ct'
                         else raise CTERM ("atomize_elim", [ct', ct])))
    ct


(* Move the thesis-quantifier inside over other quantifiers and unrelated prems *)
fun thesis_miniscope_conv inner_cv ctxt =
    let
      (* check if the outermost quantifier binds the conclusion *)
      fun is_forall_thesis t = 
          case Logic.strip_assums_concl t of
            (_ $ Bound i) => i = length (Logic.strip_params t) - 1
          | _ => false

      (* move unrelated assumptions out of the quantification *)
      fun movea_conv ctxt ct =
          let
            val _ $ Abs (_, _, b) = term_of ct
            val idxs = fold_index (fn (i, t) => not (Term.is_dependent t) ? cons i)
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
          (rewr_conv @{thm swap_params} then_conv (forall_conv (moveq_conv o snd) ctxt))
          else_conv (movea_conv ctxt)

      fun ms_conv ctxt ct = 
          if is_forall_thesis (term_of ct)
          then moveq_conv ctxt ct
          else (implies_concl_conv (ms_conv ctxt)
            else_conv
            (forall_conv (ms_conv o snd) ctxt))
            ct
    in
      ms_conv ctxt 
    end

val full_atomize_elim_conv = thesis_miniscope_conv atomize_elim_conv

end


fun atomize_elim_tac ctxt = SUBGOAL (fn (subg, i) =>
    let
      val thy = Proof_Context.theory_of ctxt
      val _ $ thesis = Logic.strip_assums_concl subg
                       
      (* Introduce a quantifier first if the thesis is not bound *)
      val quantify_thesis = 
          if is_Bound thesis then all_tac
          else let
              val cthesis = cterm_of thy thesis
              val rule = instantiate' [SOME (ctyp_of_term cthesis)] [NONE, SOME cthesis] 
                         @{thm meta_spec}
            in
              compose_tac (false, rule, 1) i
            end
    in
      quantify_thesis
      THEN (CONVERSION (full_atomize_elim_conv ctxt) i)
    end)

val setup =
  Method.setup @{binding atomize_elim} (Scan.succeed (SIMPLE_METHOD' o atomize_elim_tac))
    "convert obtains statement to atomic object logic goal"
  #> AtomizeElimData.setup

end
