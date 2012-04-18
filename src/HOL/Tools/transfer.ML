(*  Title:      HOL/Tools/transfer.ML
    Author:     Brian Huffman, TU Muenchen

Generic theorem transfer method.
*)

signature TRANSFER =
sig
  val fo_conv: Proof.context -> conv
  val prep_conv: conv
  val get_relator_eq: Proof.context -> thm list
  val transfer_add: attribute
  val transfer_del: attribute
  val transfer_tac: Proof.context -> int -> tactic
  val correspondence_tac: Proof.context -> int -> tactic
  val setup: theory -> theory
end

structure Transfer : TRANSFER =
struct

structure Data = Named_Thms
(
  val name = @{binding transfer_raw}
  val description = "raw correspondence rule for transfer method"
)

structure Relator_Eq = Named_Thms
(
  val name = @{binding relator_eq}
  val description = "relator equality rule (used by transfer method)"
)

fun get_relator_eq ctxt =
  map (Thm.symmetric o mk_meta_eq) (Relator_Eq.get ctxt)

(** Conversions **)

val App_rule = Thm.symmetric @{thm App_def}
val Abs_rule = Thm.symmetric @{thm Abs_def}
val Rel_rule = Thm.symmetric @{thm Rel_def}

fun dest_funcT cT =
  (case Thm.dest_ctyp cT of [T, U] => (T, U)
    | _ => raise TYPE ("dest_funcT", [Thm.typ_of cT], []))

fun App_conv ct =
  let val (cT, cU) = dest_funcT (Thm.ctyp_of_term ct)
  in Drule.instantiate' [SOME cT, SOME cU] [SOME ct] App_rule end

fun Abs_conv ct =
  let val (cT, cU) = dest_funcT (Thm.ctyp_of_term ct)
  in Drule.instantiate' [SOME cT, SOME cU] [SOME ct] Abs_rule end

fun Rel_conv ct =
  let val (cT, cT') = dest_funcT (Thm.ctyp_of_term ct)
      val (cU, _) = dest_funcT cT'
  in Drule.instantiate' [SOME cT, SOME cU] [SOME ct] Rel_rule end

fun Trueprop_conv cv ct =
  (case Thm.term_of ct of
    Const (@{const_name Trueprop}, _) $ _ => Conv.arg_conv cv ct
  | _ => raise CTERM ("Trueprop_conv", [ct]))

(* Conversion to insert tags on every application and abstraction. *)
fun fo_conv ctxt ct = (
      Conv.combination_conv (fo_conv ctxt then_conv App_conv) (fo_conv ctxt)
      else_conv
      Conv.abs_conv (fo_conv o snd) ctxt then_conv Abs_conv
      else_conv
      Conv.all_conv) ct

(* Conversion to preprocess a correspondence rule *)
fun prep_conv ct = (
      Conv.implies_conv Conv.all_conv prep_conv
      else_conv
      Trueprop_conv (Conv.fun_conv (Conv.fun_conv Rel_conv))
      else_conv
      Conv.all_conv) ct

(* Conversion to prep a proof goal containing a correspondence rule *)
fun correspond_conv ctxt ct = (
      Conv.forall_conv (correspond_conv o snd) ctxt
      else_conv
      Conv.implies_conv Conv.all_conv (correspond_conv ctxt)
      else_conv
      Trueprop_conv
      (Conv.combination_conv
         (Conv.combination_conv Rel_conv (fo_conv ctxt)) (fo_conv ctxt))
      else_conv
      Conv.all_conv) ct


(** Transfer proof method **)

fun bnames (t $ u) = bnames t @ bnames u
  | bnames (Abs (x,_,t)) = x :: bnames t
  | bnames _ = []

fun rename [] t = (t, [])
  | rename (x::xs) ((c as Const (@{const_name Abs}, _)) $ Abs (_, T, t)) =
    let val (t', xs') = rename xs t
    in (c $ Abs (x, T, t'), xs') end
  | rename xs0 (t $ u) =
    let val (t', xs1) = rename xs0 t
        val (u', xs2) = rename xs1 u
    in (t' $ u', xs2) end
  | rename xs t = (t, xs)

fun cert ctxt t = cterm_of (Proof_Context.theory_of ctxt) t

fun RelT (Const (@{const_name Rel}, _) $ _ $ _ $ y) = fastype_of y

(* Tactic to correspond a value to itself *)
fun eq_tac ctxt = SUBGOAL (fn (t, i) =>
  let
    val T = RelT (HOLogic.dest_Trueprop (Logic.strip_assums_concl t))
    val cT = ctyp_of (Proof_Context.theory_of ctxt) T
    val rews = get_relator_eq ctxt
    val thm1 = Drule.instantiate' [SOME cT] [] @{thm Rel_eq_refl}
    val thm2 = Raw_Simplifier.rewrite_rule rews thm1
  in
    rtac thm2 i
  end handle Match => no_tac | TERM _ => no_tac)

val post_simps =
  @{thms App_def Abs_def transfer_forall_eq [symmetric]
    transfer_implies_eq [symmetric] transfer_bforall_unfold}

fun gen_frees_tac keepers ctxt = SUBGOAL (fn (t, i) =>
  let
    val vs = rev (Term.add_frees t [])
    val vs' = filter_out (member (op =) keepers) vs
  in
    Induct.arbitrary_tac ctxt 0 vs' i
  end)

fun transfer_tac ctxt = SUBGOAL (fn (t, i) =>
  let
    val bs = bnames t
    val rules0 = @{thms Rel_App Rel_Abs}
    val rules = Data.get ctxt
  in
    EVERY
      [rewrite_goal_tac @{thms transfer_forall_eq transfer_implies_eq} i,
       CONVERSION (Trueprop_conv (fo_conv ctxt)) i,
       rtac @{thm transfer_start [rotated]} i,
       REPEAT_ALL_NEW (resolve_tac rules0 ORELSE' atac
         ORELSE' SOLVED' (REPEAT_ALL_NEW (resolve_tac rules))
         ORELSE' eq_tac ctxt) (i + 1),
       (* Alpha-rename bound variables in goal *)
       SUBGOAL (fn (u, i) =>
         rtac @{thm equal_elim_rule1} i THEN
         rtac (Thm.reflexive (cert ctxt (fst (rename bs u)))) i) i,
       (* FIXME: rewrite_goal_tac does unwanted eta-contraction *)
       rewrite_goal_tac post_simps i,
       rtac @{thm _} i]
  end)

fun correspondence_tac ctxt i =
  let
    val rules = @{thms Rel_App Rel_Abs} @ Data.get ctxt
  in
    EVERY
      [CONVERSION (correspond_conv ctxt) i,
       REPEAT_ALL_NEW
         (resolve_tac rules ORELSE' atac ORELSE' eq_tac ctxt) i]
  end

val free = Args.context -- Args.term >> (fn (_, Free v) => v | (ctxt, t) =>
  error ("Bad free variable: " ^ Syntax.string_of_term ctxt t))

val fixing = Scan.optional (Scan.lift (Args.$$$ "fixing" -- Args.colon)
  |-- Scan.repeat free) []

val transfer_method : (Proof.context -> Method.method) context_parser =
  fixing >> (fn vs => fn ctxt =>
    SIMPLE_METHOD' (gen_frees_tac vs ctxt THEN' transfer_tac ctxt))

val correspondence_method : (Proof.context -> Method.method) context_parser =
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (correspondence_tac ctxt))

(* Attribute for correspondence rules *)

val prep_rule = Conv.fconv_rule prep_conv

val transfer_add =
  Thm.declaration_attribute (Data.add_thm o prep_rule)

val transfer_del =
  Thm.declaration_attribute (Data.del_thm o prep_rule)

val transfer_attribute =
  Attrib.add_del transfer_add transfer_del

(* Theory setup *)

val setup =
  Data.setup
  #> Relator_Eq.setup
  #> Attrib.setup @{binding transfer_rule} transfer_attribute
     "correspondence rule for transfer method"
  #> Method.setup @{binding transfer} transfer_method
     "generic theorem transfer method"
  #> Method.setup @{binding correspondence} correspondence_method
     "for proving correspondence rules"

end
