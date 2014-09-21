(*  Title:      HOL/TPTP/TPTP_Proof_Reconstruction.thy
    Author:     Nik Sultana, Cambridge University Computer Laboratory

Various tests for the proof reconstruction module.

NOTE
  - Makes use of the PolyML structure.
  - looks for THF proofs in the path indicated by $THF_PROOFS
  - these proofs are generated using LEO-II with the following
    configuration choices: -po 1 -nux -nuc --expand_extuni
    You can simply filter LEO-II's output using the filter_proof
    script which is distributed with LEO-II.
*)

theory TPTP_Proof_Reconstruction_Test
imports TPTP_Test TPTP_Proof_Reconstruction
begin

section "Main function"
text "This function wraps all the reconstruction-related functions. Simply
 point it at a THF proof produced by LEO-II (using the configuration described
 above), and it will try to reconstruct it into an Isabelle/HOL theorem.
 It also returns the theory (into which the axioms and definitions used in the
 proof have been imported), but note that you can get the theory value from
 the theorem value."

ML {*
  reconstruct_leo2 (Path.explode "$THF_PROOFS/NUM667^1.p.out") @{theory}
*}

section "Prep for testing the component functions"

declare [[
  tptp_trace_reconstruction = false,
  tptp_test_all = false,
  (* tptp_test_all = true, *)
  tptp_test_timeout = 30,
  (* tptp_max_term_size = 200 *)
  tptp_max_term_size = 0
]]

ML {*
  if test_all @{context} then ()
  else
    (Options.default_put_bool @{system_option ML_exception_trace} true;
     default_print_depth 200;  (* FIXME proper ML_print_depth within context!? *)
     PolyML.Compiler.maxInlineSize := 0)
*}


section "Importing proofs"

ML {*
val probs =
  (* "$THF_PROOFS/SYN991^1.p.out" *) (*lacks conjecture*)
  (* "$THF_PROOFS/SYO040^2.p.out" *)
  (* "$THF_PROOFS/NUM640^1.p.out" *)
  (* "$THF_PROOFS/SEU553^2.p.out" *)
  (* "$THF_PROOFS/NUM665^1.p.out" *)
  (* "$THF_PROOFS/SEV161^5.p.out" *)
  (* "$THF_PROOFS/SET014^4.p.out" *)
  "$THF_PROOFS/NUM667^1.p.out"
  |> Path.explode
  |> single

val prob_names =
  probs
  |> map (Path.base #> Path.implode #> TPTP_Problem_Name.Nonstandard)
*}

setup {*
  if test_all @{context} then I
  else
    fold
     (fn path =>
       TPTP_Reconstruct.import_thm true [Path.dir path, Path.explode "$THF_PROOFS"] path leo2_on_load)
     probs
*}

text "Display nicely."
ML {*
fun display_nicely ctxt (fms : TPTP_Reconstruct.formula_meaning list) =
  List.app (fn ((n, data) : TPTP_Reconstruct.formula_meaning) =>
    Pretty.writeln
      (Pretty.block
        [Pretty.str (n ^ " "),
         Syntax.pretty_term ctxt (#fmla data),
         Pretty.str (
          if is_none (#source_inf_opt data) then ""
          else ("\n\tannotation: " ^
           PolyML.makestring (the (#source_inf_opt data : TPTP_Proof.source_info option))))])
    ) (rev fms);

(*FIXME hack for testing*)
fun test_fmla thy =
  TPTP_Reconstruct.get_fmlas_of_prob thy (hd prob_names);

fun test_pannot thy =
  TPTP_Reconstruct.get_pannot_of_prob thy (hd prob_names);

if test_all @{context} orelse prob_names = [] then ()
else
  display_nicely @{context}
  (#meta (test_pannot @{theory}))
(* To look at the original proof (i.e., before the proof transformations applied
   when the proof is loaded) replace previous line with:
   (test_fmla @{theory}
    |> map TPTP_Reconstruct.structure_fmla_meaning)
*)
*}

ML {*
fun step_range_tester f_x f_exn ctxt prob_name from until =
  let
    val max =
      case until of
          SOME x => x
        | NONE =>
            if is_some Int.maxInt then the Int.maxInt else 999999
    fun test_step x =
      if x > max then ()
      else
        (f_x x;
         (interpret_leo2_inference ctxt prob_name (Int.toString x); ())
         handle e => f_exn e; (*FIXME naive. should let Interrupt through*)
         (*assumes that inferences are numbered consecutively*)
         test_step (x + 1))
  in
    test_step from
  end

val step_range_tester_tracing =
  step_range_tester
   (fn x => tracing ("@step " ^ Int.toString x))
   (fn e => tracing ("!!" ^ PolyML.makestring e))
*}

ML {*
(*try to reconstruct each inference step*)
if test_all @{context} orelse prob_names = []
orelse true (*NOTE currently disabled*)
then ()
else
  let
    (*FIXME not guaranteed to be the right nodes*)
    val heur_start = 3
    val heur_end =
      hd (#meta (test_pannot @{theory}))
      |> #1
      |> Int.fromString
  in
    step_range_tester_tracing @{context} (hd prob_names) heur_start heur_end
  end
*}


section "Building metadata and tactics"

subsection "Building the skeleton"
ML {*
if test_all @{context} orelse prob_names = [] then []
else TPTP_Reconstruct.make_skeleton @{context} (test_pannot @{theory});

length it
*}


subsection "The 'one shot' tactic approach"
ML {*
val the_tactic =
  if test_all @{context} then []
  else
    map (fn prob_name =>
      (TPTP_Reconstruct.naive_reconstruct_tac @{context} interpret_leo2_inference (* auto_based_reconstruction_tac *) (* oracle_based_reconstruction_tac *) prob_name))
     prob_names;
*}


subsection "The 'piecemeal' approach"
ML {*
val the_tactics =
  if test_all @{context} then []
  else
    map (fn prob_name =>
      TPTP_Reconstruct.naive_reconstruct_tacs interpret_leo2_inference (* auto_based_reconstruction_tac *) (* oracle_based_reconstruction_tac *) prob_name @{context})
     prob_names;
*}

declare [[ML_print_depth = 2000]]

ML {*
the_tactics
|> map (filter (fn (_, _, x) => is_none x)
        #> map (fn (x, SOME y, _) => (x, cterm_of @{theory} y)))
*}


section "Using metadata and tactics"
text "There are various ways of testing the two ways (whole tactics or lists of tactics) of representing 'reconstructors'."


subsection "The 'one shot' tactic approach"
text "First we test whole tactics."
ML {*
(*produce thm*)
if test_all @{context} then []
else
  map (
    (* try *) (TPTP_Reconstruct.reconstruct @{context}
     (fn prob_name =>
       TPTP_Reconstruct.naive_reconstruct_tac @{context} interpret_leo2_inference prob_name
     (* oracle_based_reconstruction_tac *))))
   prob_names
*}


subsection "The 'piecemeal' approach"
ML {*
fun attac n = List.nth (List.nth (the_tactics, 0), n) |> #3 |> the |> snd
fun attac_to n 0 = attac n
  | attac_to n m = attac n THEN attac_to (n + 1) (m - 1)
fun shotac n = List.nth (List.nth (the_tactics, 0), n) |> #3 |> the |> fst
*}

ML {*
(*Given a list of reconstructed inferences (as in "the_tactics" above,
  count the number of failures and successes, and list the failed inference
  reconstructions.*)
fun evaluate_the_tactics [] acc = acc
  | evaluate_the_tactics ((node_no, (inf_name, inf_fmla, NONE)) :: xs) ((fai, suc), inf_list) =
      let
        val score = (fai + 1, suc)
        val index_info = get_index (fn (x, _) => if x = node_no then SOME true else NONE) inf_list
        val inf_list' =
          case index_info of
              NONE => (node_no, (inf_name, inf_fmla, 1)) :: inf_list
            | SOME (idx, _) =>
                nth_map idx (fn (node_no, (inf_name, inf_fmla, count)) => (node_no, (inf_name, inf_fmla, count + 1))) inf_list
      in
        evaluate_the_tactics xs (score, inf_list')
      end
  | evaluate_the_tactics ((_, (_, _, SOME _)) :: xs) ((fai, suc), inf_list) =
      evaluate_the_tactics xs ((fai, suc + 1), inf_list)
*}


text "Now we build a tactic by combining lists of tactics"
ML {*
(*given a list of tactics to be applied in sequence (i.e., they
  follow a skeleton), we build a single tactic, interleaving
  some tracing info to help with debugging.*)
fun step_by_step_tacs ctxt verbose (thm_tacs : (thm * tactic) list) : tactic =
    let
      fun interleave_tacs [] [] = all_tac
        | interleave_tacs (tac1 :: tacs1) (tac2 :: tacs2) =
            EVERY [tac1, tac2]
            THEN interleave_tacs tacs1 tacs2
      val thms_to_traceprint =
        map (fn thm => fn st =>
              (*FIXME uses makestring*)
              print_tac ctxt (PolyML.makestring thm) st)

    in
      if verbose then
        ListPair.unzip thm_tacs
        |> apfst (fn thms => enumerate 1 thms)
        |> apfst thms_to_traceprint
        |> uncurry interleave_tacs
      else EVERY (map #2 thm_tacs)
    end
*}

ML {*
(*apply step_by_step_tacs to all problems under test*)
fun narrated_tactics ctxt =
 map (map (#3 #> the)
      #> step_by_step_tacs ctxt false)
   the_tactics;

(*produce thm*)
(*use narrated_tactics to reconstruct all problems under test*)
if test_all @{context} then []
else
  map (fn (prob_name, tac) =>
         TPTP_Reconstruct.reconstruct @{context}
           (fn _ => tac) prob_name)
    (ListPair.zip (prob_names, narrated_tactics @{context}))
*}


subsection "Manually using 'piecemeal' approach"
text "Another testing possibility involves manually creating a lemma
and running through the list of tactics generating to prove that lemma. The following code shows the goal of each problem under test, and then for each problem returns the list of tactics which can be invoked individually as shown below."
ML {*
fun show_goal ctxt prob_name =
  let
    val thy = Proof_Context.theory_of ctxt
    val pannot = TPTP_Reconstruct.get_pannot_of_prob thy prob_name
  in
    #meta pannot
    |> List.filter (fn (_, info) =>
        #role info = TPTP_Syntax.Role_Conjecture)
    |> hd
    |> snd |> #fmla
    |> cterm_of thy
  end;

if test_all @{context} then []
else
  map (show_goal @{context}) prob_names;
*}

ML {*
(*project out the list of tactics from "the_tactics"*)
val just_the_tacs  =
 map (map (#3 #> the #> #2))
   the_tactics;

map length just_the_tacs
*}

ML {*
(*like just_the_tacs, but extract the thms, to inspect their thys*)
val just_the_thms  =
 map (map (#3 #> the #> #1))
   the_tactics;

map length just_the_thms;
*}

ML {*
(*given a thm, show us the axioms in its thy*)
val axms_of_thy_of_thm =
  Thm.theory_of_thm
  #> ` Theory.axioms_of
  #> apsnd cterm_of
  #> swap
  #> apsnd (map snd)
  #> uncurry map
*}

ML {*
(*Show the skeleton-level inference which is done by each element of just_the_tacs. This is useful when debugging using the technique shown next*)
if test_all @{context} orelse prob_names = [] then ()
else
  the_tactics
  |> hd
  |> map #1
  |> TPTP_Reconstruct_Library.enumerate 0
  |> List.app (PolyML.makestring #> writeln)
  *}

ML {*
fun leo2_tac_wrap prob_name step i = fn st =>
  let
    val ctxt =
      Thm.theory_of_thm st
      |> Proof_Context.init_global
  in
    rtac (interpret_leo2_inference ctxt prob_name step) i st
  end
*}

(*FIXME move these examples elsewhere*)
(*
lemma "\<forall>(Xj\<Colon>TPTP_Interpret.ind) Xk\<Colon>TPTP_Interpret.ind.
        bnd_cCKB6_BLACK Xj Xk \<longrightarrow>
        bnd_cCKB6_BLACK (bnd_s (bnd_s (bnd_s Xj))) (bnd_s Xk)"
apply (tactic {*nth (nth just_the_tacs 0) 0*})
apply (tactic {*nth (nth just_the_tacs 0) 1*})
apply (tactic {*nth (nth just_the_tacs 0) 2*})
apply (tactic {*nth (nth just_the_tacs 0) 3*})
apply (tactic {*nth (nth just_the_tacs 0) 4*})
apply (tactic {*nth (nth just_the_tacs 0) 5*})
ML_prf "nth (hd the_tactics) 6"
apply (tactic {*nth (nth just_the_tacs 0) 6*})
apply (tactic {*nth (nth just_the_tacs 0) 7*})
apply (tactic {*nth (nth just_the_tacs 0) 8*})
apply (tactic {*nth (nth just_the_tacs 0) 9*})
apply (tactic {*nth (nth just_the_tacs 0) 10*})
apply (tactic {*nth (nth just_the_tacs 0) 11*})
apply (tactic {*nth (nth just_the_tacs 0) 12*})
apply (tactic {*nth (nth just_the_tacs 0) 13*})
apply (tactic {*nth (nth just_the_tacs 0) 14*})
apply (tactic {*nth (nth just_the_tacs 0) 15*})

apply (tactic {*nth (nth just_the_tacs 0) 16*})

(*
apply (tactic {*
rtac (interpret_leo2_inference @{context} (hd prob_names) "8") 1
*})
apply (tactic {*
rtac (interpret_leo2_inference @{context} (hd prob_names) "7") 1
*})
apply (tactic {*
rtac (interpret_leo2_inference @{context} (hd prob_names) "6") 1
*})
(*
apply (tactic {*
rtac (interpret_leo2_inference @{context} (hd prob_names) "4") 1
*})
*)
*)

apply (tactic {*nth (nth just_the_tacs 0) 17*})
apply (tactic {*nth (nth just_the_tacs 0) 18*})
apply (tactic {*nth (nth just_the_tacs 0) 19*})
apply (tactic {*nth (nth just_the_tacs 0) 20*})
apply (tactic {*nth (nth just_the_tacs 0) 21*})

ML_prf "nth (hd the_tactics) 21"
ML_prf "nth (hd the_tactics) 22"

apply (tactic {*nth (nth just_the_tacs 0) 22*})
apply (tactic {*nth (nth just_the_tacs 0) 23*})
apply (tactic {*nth (nth just_the_tacs 0) 24*})
apply (tactic {*nth (nth just_the_tacs 0) 25*})


ML_prf "nth (hd the_tactics) 19"

apply (tactic {*
interpret_leo2_inference_wrap (hd prob_names) "8" 1
*})
apply (tactic {*
interpret_leo2_inference_wrap (hd prob_names) "7" 1
*})
apply (tactic {*
interpret_leo2_inference_wrap (hd prob_names) "6" 1
*})
apply (tactic {*
interpret_leo2_inference_wrap (hd prob_names) "4" 1
*})

ML_prf "nth (hd the_tactics) 20"
ML_prf "nth (hd the_tactics) 21"
ML_prf "nth (hd the_tactics) 22"
*)

(*
lemma "bnd_powersetE1 \<longrightarrow>
     bnd_sepInPowerset \<longrightarrow>
     (\<forall>A Xphi. bnd_subset (bnd_dsetconstr A Xphi) A)"
apply (tactic {*nth (nth just_the_tacs 0) 0*})
apply (tactic {*nth (nth just_the_tacs 0) 1*})
apply (tactic {*nth (nth just_the_tacs 0) 2*})
apply (tactic {*nth (nth just_the_tacs 0) 3*})
apply (tactic {*nth (nth just_the_tacs 0) 4*})
apply (tactic {*nth (nth just_the_tacs 0) 5*})
ML_prf "nth (hd the_tactics) 6"
apply (tactic {*nth (nth just_the_tacs 0) 6*})
apply (tactic {*nth (nth just_the_tacs 0) 7*})
apply (tactic {*nth (nth just_the_tacs 0) 8*})
apply (tactic {*nth (nth just_the_tacs 0) 9*})
apply (tactic {*nth (nth just_the_tacs 0) 10*})
apply (tactic {*nth (nth just_the_tacs 0) 11*})
apply (tactic {*nth (nth just_the_tacs 0) 12*})
apply (tactic {*nth (nth just_the_tacs 0) 13*})
apply (tactic {*nth (nth just_the_tacs 0) 14*})
apply (tactic {*nth (nth just_the_tacs 0) 15*})
apply (tactic {*nth (nth just_the_tacs 0) 16*})
apply (tactic {*nth (nth just_the_tacs 0) 17*})
apply (tactic {*nth (nth just_the_tacs 0) 18*})
apply (tactic {*nth (nth just_the_tacs 0) 19*})
apply (tactic {*nth (nth just_the_tacs 0) 20*})
apply (tactic {*nth (nth just_the_tacs 0) 21*})
apply (tactic {*nth (nth just_the_tacs 0) 22*})
apply (tactic {*nth (nth just_the_tacs 0) 23*})
apply (tactic {*nth (nth just_the_tacs 0) 24*})
apply (tactic {*nth (nth just_the_tacs 0) 25*})
(* apply (tactic {*nth (nth just_the_tacs 0) 26*}) *)
ML_prf "nth (hd the_tactics) 26"
apply (subgoal_tac "(\<not> (\<forall>A Xphi. bnd_subset (bnd_dsetconstr A Xphi) A)) =
       True \<Longrightarrow>
       (\<not> bnd_subset (bnd_dsetconstr bnd_sK1 bnd_sK2) bnd_sK1) =
       True")
prefer 2
apply (thin_tac "(bnd_powersetE1 \<longrightarrow>
      bnd_sepInPowerset \<longrightarrow>
      (\<forall>A Xphi. bnd_subset (bnd_dsetconstr A Xphi) A)) =
     False")
apply (tactic {*extcnf_combined_simulator_tac (hd prob_names) 1*})
apply (tactic {*extcnf_combined_simulator_tac (hd prob_names) 1*})
apply (tactic {*extcnf_combined_simulator_tac (hd prob_names) 1*})
apply (tactic {*extcnf_combined_simulator_tac (hd prob_names) 1*})

apply simp

(* apply (tactic {*nth (nth just_the_tacs 0) 26*}) *)
apply (tactic {*nth (nth just_the_tacs 0) 27*})
apply (tactic {*nth (nth just_the_tacs 0) 28*})
apply (tactic {*nth (nth just_the_tacs 0) 29*})
apply (tactic {*nth (nth just_the_tacs 0) 30*})
apply (tactic {*nth (nth just_the_tacs 0) 31*})
apply (tactic {*nth (nth just_the_tacs 0) 32*})
apply (tactic {*nth (nth just_the_tacs 0) 33*})
apply (tactic {*nth (nth just_the_tacs 0) 34*})
apply (tactic {*nth (nth just_the_tacs 0) 35*})
apply (tactic {*nth (nth just_the_tacs 0) 36*})
apply (tactic {*nth (nth just_the_tacs 0) 37*})
apply (tactic {*nth (nth just_the_tacs 0) 38*})
apply (tactic {*nth (nth just_the_tacs 0) 39*})
apply (tactic {*nth (nth just_the_tacs 0) 40*})
apply (tactic {*nth (nth just_the_tacs 0) 41*})
apply (tactic {*nth (nth just_the_tacs 0) 42*})
apply (tactic {*nth (nth just_the_tacs 0) 43*})
apply (tactic {*nth (nth just_the_tacs 0) 44*})
apply (tactic {*nth (nth just_the_tacs 0) 45*})
apply (tactic {*nth (nth just_the_tacs 0) 46*})
apply (tactic {*nth (nth just_the_tacs 0) 47*})
apply (tactic {*nth (nth just_the_tacs 0) 48*})
apply (tactic {*nth (nth just_the_tacs 0) 49*})
apply (tactic {*nth (nth just_the_tacs 0) 50*})
apply (tactic {*nth (nth just_the_tacs 0) 51*})
done
*)

(*
We can use just_the_tacs as follows:

(this is from SEV012^5.p.out)
lemma "((\<forall>(Xx :: bool) (Xy :: bool). True \<longrightarrow> True) \<and>
      (\<forall>(Xx :: bool) (Xy :: bool) (Xz :: bool). True \<and> True \<longrightarrow> True)) \<and>
     (\<lambda>(Xx :: bool) (Xy :: bool). True) = (\<lambda>Xx Xy. True)"
apply (tactic {*nth (nth just_the_tacs 0) 0*})
apply (tactic {*nth (nth just_the_tacs 0) 1*})
apply (tactic {*nth (nth just_the_tacs 0) 2*})
apply (tactic {*nth (nth just_the_tacs 0) 3*})
apply (tactic {*nth (nth just_the_tacs 0) 4*})
apply (tactic {*nth (nth just_the_tacs 0) 5*})
ML_prf "nth (hd the_tactics) 6"
apply (tactic {*nth (nth just_the_tacs 0) 6*})
apply (tactic {*nth (nth just_the_tacs 0) 7*})
apply (tactic {*nth (nth just_the_tacs 0) 8*})
apply (tactic {*nth (nth just_the_tacs 0) 9*})
apply (tactic {*nth (nth just_the_tacs 0) 10*})
apply (tactic {*nth (nth just_the_tacs 0) 11*})
apply (tactic {*nth (nth just_the_tacs 0) 12*})
apply (tactic {*nth (nth just_the_tacs 0) 13*})
apply (tactic {*nth (nth just_the_tacs 0) 14*})
apply (tactic {*nth (nth just_the_tacs 0) 15*})
apply (tactic {*nth (nth just_the_tacs 0) 16*})
apply (tactic {*nth (nth just_the_tacs 0) 17*})
apply (tactic {*nth (nth just_the_tacs 0) 18*})
apply (tactic {*nth (nth just_the_tacs 0) 19*})
apply (tactic {*nth (nth just_the_tacs 0) 20*})
apply (tactic {*nth (nth just_the_tacs 0) 21*})
apply (tactic {*nth (nth just_the_tacs 0) 22*})
done

(*
We could also use previous definitions directly,
e.g. the following should prove the goal at a go:
- apply (tactic {*narrated_tactics |> hd |> hd*})
- apply (tactic {*
    TPTP_Reconstruct.naive_reconstruct_tac
     interpret_leo2_inference
     (hd prob_names)
     @{context}*})
(Note that the previous two methods don't work in this
 "lemma" testing mode, not sure why. The previous methods
 (producing the thm values directly) should work though.)
*)
*)


section "Testing against benchmark"

ML {*
(*if reconstruction_info value is NONE then a big error must have occurred*)
type reconstruction_info =
  ((int(*no of failures*) * int(*no of successes*)) *
  (TPTP_Reconstruct.rolling_stock * term option(*inference formula*) * int (*number of times the inference occurs in the skeleton*)) list) option

datatype proof_contents =
    No_info
  | Empty
  | Nonempty of reconstruction_info

(*To make output less cluttered in whole-run tests*)
fun erase_inference_fmlas (Nonempty (SOME (outline, inf_info))) =
      Nonempty (SOME (outline, map (fn (inf_name, _, count) => (inf_name, NONE, count)) inf_info))
  | erase_inference_fmlas x = x
*}

ML {*
(*Report on how many inferences in a proof are reconstructed, and give some
  info about the inferences for which reconstruction failed.*)
fun test_partial_reconstruction thy prob_file =
  let
    val prob_name =
      (Path.base #> Path.implode #> TPTP_Problem_Name.Nonstandard) prob_file

    val thy' =
      try
       (TPTP_Reconstruct.import_thm
        true
        [Path.dir prob_file, Path.explode "$TPTP"]
        prob_file leo2_on_load)
       thy

    val ctxt' =
      if is_some thy' then SOME (Proof_Context.init_global (the thy')) else NONE

    (*to test if proof is empty*)
    val fms =
      if is_some thy'
      then SOME (TPTP_Reconstruct.get_fmlas_of_prob (the thy') prob_name)
      else NONE

    val the_tactics =
      if is_some thy' then
        SOME (TPTP_Reconstruct.naive_reconstruct_tacs (* metis_based_reconstruction_tac *)
interpret_leo2_inference (* auto_based_reconstruction_tac *) (* oracle_based_reconstruction_tac *) prob_name (the ctxt'))
      else NONE

(* val _ = tracing ("tt=" ^ PolyML.makestring the_tactics) *)

    val skeleton =
      if is_some thy' then
        SOME (TPTP_Reconstruct.make_skeleton (the ctxt')
              (TPTP_Reconstruct.get_pannot_of_prob (the thy') prob_name))
      else NONE

    val skeleton_and_tactics =
      if is_some thy' then
        SOME (ListPair.zip (the skeleton, the the_tactics))
      else NONE

    val result =
      if is_some thy' then
        SOME (evaluate_the_tactics (the skeleton_and_tactics)
              ((0, 0), []))
      else NONE

    (*strip node names*)
    val result' =
      if is_some result then SOME (apsnd (map #2) (the result)) else NONE
  in
    if is_some fms andalso List.null (the fms) then Empty
    else Nonempty result'
  end
*}

ML {*
  (*default timeout is 1 min*)
  fun reconstruct timeout light_output file thy =
    let
      val timer = Timer.startRealTimer ()
    in
      TimeLimit.timeLimit (Time.fromSeconds (if timeout = 0 then 60 else timeout))
       (test_partial_reconstruction thy
        #> light_output ? erase_inference_fmlas
        #> PolyML.makestring (* FIXME *)
        #> (fn s => report (Proof_Context.init_global thy) (PolyML.makestring file ^ " === " ^ s ^
             " t=" ^ (Timer.checkRealTimer timer |> Time.toMilliseconds |> PolyML.makestring))))
       file
    end
*}

ML {*
  (*this version of "reconstruct" builds theorems, instead of lists of reconstructed inferences*)
  (*default timeout is 1 min*)
  fun reconstruct timeout file thy =
    let
      val timer = Timer.startRealTimer ()
      val thy' =
        TPTP_Reconstruct.import_thm true
         [Path.dir file, Path.explode "$TPTP"]
         file leo2_on_load thy

      val ctxt = Proof_Context.init_global thy' (*FIXME pass ctxt instead of thy*)
      val prob_name =
        file
        |> Path.base
        |> Path.implode
        |> TPTP_Problem_Name.Nonstandard
    in
      TimeLimit.timeLimit (Time.fromSeconds (if timeout = 0 then 60 else timeout))
       (fn prob_name =>
        (can
          (TPTP_Reconstruct.reconstruct ctxt (fn prob_name =>
            TPTP_Reconstruct.naive_reconstruct_tac ctxt interpret_leo2_inference prob_name (* oracle_based_reconstruction_tac *))) prob_name )
       |> (fn s => report ctxt (Path.print file ^ " === " ^ Bool.toString s ^
             " t=" ^ (Timer.checkRealTimer timer |> Time.toMilliseconds |> PolyML.makestring))))
       prob_name
    end
*}

ML {*
  fun reconstruction_test timeout ctxt =
    test_fn ctxt
     (fn file => reconstruct timeout file (Proof_Context.theory_of ctxt))
     "reconstructor"
     ()
*}

ML {*
datatype examination_results =
    Whole_proof of string(*filename*) * proof_contents
  | Specific_rule of string(*filename*) * string(*inference rule*) * term option list

(*Look out for failures reconstructing a particular inference rule*)
fun filter_failures inference_name (Whole_proof (filename, results)) =
  let
    val filtered_results =
      case results of
          Nonempty (SOME results') =>
            #2 results'
            |> maps (fn (stock as TPTP_Reconstruct.Annotated_step (_, inf_name), inf_fmla, _) =>
                 if inf_name = inference_name then [inf_fmla] else [])
        | _ => []
  in Specific_rule (filename, inference_name, filtered_results) end

(*Returns detailed info about a proof-reconstruction attempt.
  If rule_name is specified then the related failed inferences
  are returned, otherwise all failed inferences are returned.*)
fun examine_failed_inferences ctxt filename rule_name =
  let
    val thy = Proof_Context.theory_of ctxt
    val prob_file = Path.explode filename
    val results =
      if test_all ctxt then No_info
      else test_partial_reconstruction thy prob_file
  in
    Whole_proof (filename, results)
    |> is_some rule_name ? (fn x =>
                             filter_failures (the rule_name) x)
  end
*}

ML {*
exception NONSENSE

fun annotation_or_id (TPTP_Reconstruct.Step n) = n
  | annotation_or_id (TPTP_Reconstruct.Annotated_step (n, anno)) = anno
  | annotation_or_id TPTP_Reconstruct.Assumed = "assumption"
  | annotation_or_id TPTP_Reconstruct.Unconjoin = "conjI"
  | annotation_or_id TPTP_Reconstruct.Caboose = "(end)"
  | annotation_or_id (TPTP_Reconstruct.Synth_step s) = s
  | annotation_or_id (TPTP_Reconstruct.Split (split_node, soln_node, _)) = "split_at " ^ split_node ^ " " ^ soln_node;

fun count_failures (Whole_proof (_, No_info)) = raise NONSENSE
  | count_failures (Whole_proof (_, Empty)) = raise NONSENSE
  | count_failures (Whole_proof (_, Nonempty NONE)) = raise NONSENSE
  | count_failures (Whole_proof (_, Nonempty (SOME (((n, _), _))))) = n
  | count_failures (Specific_rule (_, _, t)) = length t

fun pre_classify_failures [] alist = alist
  | pre_classify_failures ((stock, _, _) :: xs) alist =
      let
        val inf = annotation_or_id stock
        val count = AList.lookup (op =) alist inf
      in
        if is_none count
        then pre_classify_failures xs ((inf, 1) :: alist)
        else
          pre_classify_failures xs
           (AList.update (op =) (inf, the count + 1) alist)
      end

fun classify_failures (Whole_proof (_, Nonempty (SOME (((_, _), inferences))))) = pre_classify_failures inferences []
  | classify_failures (Specific_rule (_, rule, t)) = [(rule, length t)]
  | classify_failures _ = raise NONSENSE
*}

ML {*
val regressions = map (fn s => "$THF_PROOFS/" ^ s)
  ["SEV405^5.p.out",
   (*"SYO377^5.p.out", Always seems to raise Interrupt on my laptop -- probably because node 475 has lots of premises*)
   "PUZ031^5.p.out",
   "ALG001^5.p.out",
   "SYO238^5.p.out",
   (*"SEV158^5.p.out", This is big*)
   "SYO285^5.p.out",
   "../SYO285^5.p.out_reduced",
   (* "SYO225^5.p.out", This is big*)
   "SYO291^5.p.out",
   "SET669^3.p.out",
   "SEV233^5.p.out",
   (*"SEU511^1.p.out", This is big*)
   "SEV161^5.p.out",
   "SEV012^5.p.out",
   "SYO035^1.p.out",
   "SYO291^5.p.out",
   "SET741^4.p.out", (*involves both definitions and contorted splitting. has nice graph.*)
   "SEU548^2.p.out",
   "SEU513^2.p.out",
   "SYO006^1.p.out",
   "SYO371^5.p.out" (*has contorted splitting, like SYO006^1.p.out, but doesn't involve definitions*)
  ]
*}

ML {*
val experiment = examine_failed_inferences @{context}
  (List.last regressions) NONE;

(*
val experiment_focus =
  filter_failures "extcnf_combined" experiment;
*)

(*
count_failures experiment_focus
classify_failures experiment
*)
*}

text "Run reconstruction on all problems in a benchmark (provided via a script)
and report on partial success."

declare [[
  tptp_test_all = true,
  tptp_test_timeout = 10
]]

ML {*
  (*problem source*)
  val tptp_probs_dir =
    Path.explode "$THF_PROOFS"
    |> Path.expand;
*}

ML {*
  if test_all @{context} then
    (report @{context} "Reconstructing proofs";
    S timed_test (reconstruction_test (get_timeout @{context})) @{context} (TPTP_Syntax.get_file_list tptp_probs_dir))
  else ()
*}

(*
Debugging strategy:
  1) get list of all proofs
  2) order by size
  3) try to construct each in turn, given some timeout

Use this to find the smallest failure, then debug that.
*)
end