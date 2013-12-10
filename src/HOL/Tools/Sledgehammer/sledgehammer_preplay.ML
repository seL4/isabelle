(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_preplay.ML
    Author:     Steffen Juilf Smolka, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

Preplaying of isar proofs.
*)

signature SLEDGEHAMMER_PREPLAY =
sig
  type isar_proof = Sledgehammer_Proof.isar_proof
  type isar_step = Sledgehammer_Proof.isar_step
  type label = Sledgehammer_Proof.label

  eqtype preplay_time

  datatype preplay_result =
    PplFail of exn |
    PplSucc of preplay_time

  val trace : bool Config.T
  val zero_preplay_time : preplay_time
  val some_preplay_time : preplay_time
  val add_preplay_time : preplay_time -> preplay_time -> preplay_time
  val string_of_preplay_time : preplay_time -> string

  type preplay_interface =
  { get_preplay_result : label -> preplay_result,
    set_preplay_result : label -> preplay_result -> unit,
    get_preplay_time : label -> preplay_time,
    set_preplay_time : label -> preplay_time -> unit,
    preplay_quietly : Time.time -> isar_step -> preplay_time,
    (* the returned flag signals a preplay failure *)
    overall_preplay_stats : isar_proof -> preplay_time * bool }

  val proof_preplay_interface :
    bool -> Proof.context -> string -> string -> bool -> Time.time
    -> isar_proof -> preplay_interface
end;

structure Sledgehammer_Preplay : SLEDGEHAMMER_PREPLAY =
struct

open Sledgehammer_Util
open Sledgehammer_Proof

val trace =
  Attrib.setup_config_bool @{binding sledgehammer_preplay_trace} (K false)

(* The boolean flag encodes whether the time is exact (false) or an lower bound
   (true):
      (t, false) = "t ms"
      (t, true)  = "> t ms" *)
type preplay_time = bool * Time.time

datatype preplay_result =
  PplFail of exn |
  PplSucc of preplay_time

val zero_preplay_time = (false, Time.zeroTime) (* 0 ms *)
val some_preplay_time = (true, Time.zeroTime)  (* > 0 ms *)

fun add_preplay_time (b1, t1) (b2, t2) = (b1 orelse b2, Time.+(t1,t2))

val string_of_preplay_time = ATP_Util.string_of_ext_time

(* preplay tracing *)
fun preplay_trace ctxt assms concl time =
  let
    val ctxt = ctxt |> Config.put show_markup true
    val time = "[" ^ (string_of_preplay_time time) ^ "]" |> Pretty.str
    val nr_of_assms = length assms
    val assms = assms |> map (Display.pretty_thm ctxt)
                      |> (fn [] => Pretty.str ""
                           | [a] => a
                           | assms => Pretty.enum ";" "\<lbrakk>" "\<rbrakk>" assms)  (* Syntax.pretty_term!? *)
    val concl = concl |> Syntax.pretty_term ctxt
    val trace_list = [] |> cons concl
                        |> nr_of_assms>0 ? cons (Pretty.str "\<Longrightarrow>")
                        |> cons assms
                        |> cons time
    val pretty_trace = Pretty.blk (2, Pretty.breaks trace_list)
  in tracing (Pretty.string_of pretty_trace) end

(* timing *)
fun take_time timeout tac arg =
  let
    val timing = Timing.start ()
  in
    (TimeLimit.timeLimit timeout tac arg;
      Timing.result timing |> #cpu |> pair false)
    handle TimeLimit.TimeOut => (true, timeout)
  end

(* lookup facts in context *)
fun resolve_fact_names ctxt names =
  (names
    |>> map string_of_label
    |> op @
    |> maps (thms_of_name ctxt))
  handle ERROR msg => error ("preplay error: " ^ msg)

(* turn terms/proofs into theorems *)
fun thm_of_term ctxt = Skip_Proof.make_thm (Proof_Context.theory_of ctxt)

fun thm_of_proof ctxt (Proof (fixed_frees, assms, steps)) =
  let
    val concl = 
      (case try List.last steps of
        SOME (Prove (_, [], _, t, _, _)) => t
      | _ => raise Fail "preplay error: malformed subproof")
    val var_idx = maxidx_of_term concl + 1
    fun var_of_free (x, T) = Var((x, var_idx), T)
    val substitutions =
      map (`var_of_free #> swap #> apfst Free) fixed_frees
  in
    Logic.list_implies (assms |> map snd, concl)
      |> subst_free substitutions
      |> thm_of_term ctxt
  end

(* mapping from proof methods to tactics *)
fun tac_of_method method type_enc lam_trans ctxt facts =
  case method of
    MetisM => Metis_Tactic.metis_tac [type_enc] lam_trans ctxt facts
  | _ =>
      Method.insert_tac facts
      THEN' (case method of
              SimpM => Simplifier.asm_full_simp_tac
            | AutoM => Clasimp.auto_tac #> K
            | FastforceM => Clasimp.fast_force_tac
            | ForceM => Clasimp.force_tac
            | ArithM => Arith_Data.arith_tac
            | BlastM => blast_tac
            | _ => raise Fail "Sledgehammer_Preplay: tac_of_method") ctxt


(* main function for preplaying isar_steps; may throw exceptions *)
fun preplay_raw _ _ _ _ _ (Let _) = zero_preplay_time
  | preplay_raw debug type_enc lam_trans ctxt timeout
      (Prove (_, xs, _, t, subproofs, (fact_names, proof_method))) =
  let
    val (prop, obtain) =
      (case xs of
        [] => (t, false)
      | _ =>
      (* proof obligation: !!thesis. (!!x. A x ==> thesis) ==> thesis
           (see ~~/src/Pure/Isar/obtain.ML) *)
        let
          val thesis = Term.Free ("thesis", HOLogic.boolT)
          val thesis_prop = thesis |> HOLogic.mk_Trueprop
          val frees = map Term.Free xs

          (* !!x1..xn. t ==> thesis (xs = [x1, .., xn]) *)
          val inner_prop =
            fold_rev Logic.all frees (Logic.mk_implies (t, thesis_prop))

          (* !!thesis. (!!x1..xn. t ==> thesis) ==> thesis *)
          val prop =
            Logic.all thesis (Logic.mk_implies (inner_prop, thesis_prop))
        in
          (prop, true)
        end)
    val facts =
      map (thm_of_proof ctxt) subproofs @ resolve_fact_names ctxt fact_names
    val ctxt = ctxt |> Config.put Metis_Tactic.verbose debug
                    |> Config.put Lin_Arith.verbose debug
                    |> obtain ? Config.put Metis_Tactic.new_skolem true
    val goal =
      Goal.prove (Config.put Metis_Tactic.verbose debug ctxt) [] [] prop
    fun tac {context = ctxt, prems = _} =
      HEADGOAL (tac_of_method proof_method type_enc lam_trans ctxt facts)
    fun run_tac () = goal tac
      handle ERROR msg => error ("Preplay error: " ^ msg)
    val preplay_time = take_time timeout run_tac ()
  in
    (* tracing *)
    (if Config.get ctxt trace then preplay_trace ctxt facts prop preplay_time
     else ();
     preplay_time)
  end


(*** proof preplay interface ***)

type preplay_interface =
{ get_preplay_result : label -> preplay_result,
  set_preplay_result : label -> preplay_result -> unit,
  get_preplay_time : label -> preplay_time,
  set_preplay_time : label -> preplay_time -> unit,
  preplay_quietly : Time.time -> isar_step -> preplay_time,
  (* the returned flag signals a preplay failure *)
  overall_preplay_stats : isar_proof -> preplay_time * bool }


(* enriches context with local proof facts *)
fun enrich_context proof ctxt =
  let
    val thy = Proof_Context.theory_of ctxt

    fun enrich_with_fact l t =
      Proof_Context.put_thms false
        (string_of_label l, SOME [Skip_Proof.make_thm thy t])

    val enrich_with_assms = fold (uncurry enrich_with_fact)

    fun enrich_with_proof (Proof (_, assms, isar_steps)) =
      enrich_with_assms assms #> fold enrich_with_step isar_steps

    and enrich_with_step (Let _) = I
      | enrich_with_step (Prove (_, _, l, t, subproofs, _)) =
          enrich_with_fact l t #> fold enrich_with_proof subproofs
  in
    enrich_with_proof proof ctxt
  end


(* Given a proof, produces an imperative preplay interface with a shared table
   mapping from labels to preplay results.
   The preplay results are caluclated lazyly and cached to avoid repeated
   calculation.

   PRECONDITION: the proof must be labeled canocially, see
   Slegehammer_Proof.relabel_proof_canonically
*)

fun proof_preplay_interface debug ctxt type_enc lam_trans do_preplay
      preplay_timeout proof : preplay_interface =
  if not do_preplay then
    (* the dont_preplay option pretends that everything works just fine *)
    { get_preplay_result = K (PplSucc zero_preplay_time),
      set_preplay_result = K (K ()),
      get_preplay_time = K zero_preplay_time,
      set_preplay_time = K (K ()),
      preplay_quietly = K (K zero_preplay_time),
      overall_preplay_stats = K (zero_preplay_time, false)}
  else
    let
      (* add local proof facts to context *)
      val ctxt = enrich_context proof ctxt

      fun preplay quietly timeout step =
        preplay_raw debug type_enc lam_trans ctxt timeout step
        |> PplSucc
        handle exn =>
          if Exn.is_interrupt exn then
            reraise exn
          else if not quietly andalso debug then
            (warning ("Preplay failure:\n  " ^ @{make_string} step ^ "\n  "
                      ^ @{make_string} exn);
             PplFail exn)
          else
            PplFail exn

      (* preplay steps treating exceptions like timeouts *)
      fun preplay_quietly timeout step =
        (case preplay true timeout step of
          PplSucc preplay_time => preplay_time
        | PplFail _ => (true, timeout))

      val preplay_tab =
        let
          fun add_step_to_tab step tab =
            case label_of_step step of
              NONE => tab
            | SOME l =>
                Canonical_Lbl_Tab.update_new
                  (l, (fn () => preplay false preplay_timeout step) |> Lazy.lazy)
                  tab
            handle Canonical_Lbl_Tab.DUP _ =>
              raise Fail "Sledgehammer_Preplay: preplay time table"
        in
          Canonical_Lbl_Tab.empty
          |> fold_isar_steps add_step_to_tab (steps_of_proof proof)
          |> Unsynchronized.ref
        end

      fun get_preplay_result lbl =
        Canonical_Lbl_Tab.lookup (!preplay_tab) lbl |> the |> Lazy.force
        handle Option.Option =>
          raise Fail "Sledgehammer_Preplay: preplay time table"

      fun set_preplay_result lbl result =
        preplay_tab :=
          Canonical_Lbl_Tab.update (lbl, Lazy.value result) (!preplay_tab)

      fun get_preplay_time lbl =
        case get_preplay_result lbl of
          PplSucc preplay_time => preplay_time
        | PplFail _ => some_preplay_time (* best approximation possible *)

      fun set_preplay_time lbl time = set_preplay_result lbl (PplSucc time)

      fun overall_preplay_stats (Proof(_, _, steps)) =
        let
          fun result_of_step step =
            try (label_of_step #> the #> get_preplay_result) step
            |> the_default (PplSucc zero_preplay_time)
          fun do_step step =
            (case result_of_step step of
              PplSucc preplay_time => apfst (add_preplay_time preplay_time)
            | PplFail _ => apsnd (K true))
        in
          fold_isar_steps do_step steps (zero_preplay_time, false)
        end

    in
      {get_preplay_result = get_preplay_result,
       set_preplay_result = set_preplay_result,
       get_preplay_time = get_preplay_time,
       set_preplay_time = set_preplay_time,
       preplay_quietly = preplay_quietly,
       overall_preplay_stats = overall_preplay_stats}
    end

end;
