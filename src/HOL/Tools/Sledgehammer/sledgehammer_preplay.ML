(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_preplay.ML
    Author:     Steffen Juilf Smolka, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

Preplaying of Isar proofs.
*)

signature SLEDGEHAMMER_PREPLAY =
sig
  type isar_proof = Sledgehammer_Proof.isar_proof
  type isar_step = Sledgehammer_Proof.isar_step
  type label = Sledgehammer_Proof.label

  type preplay_result

  val trace: bool Config.T
  val zero_preplay_time: bool * Time.time
  val some_preplay_time: bool * Time.time
  val add_preplay_time: bool * Time.time -> bool * Time.time -> bool * Time.time

  type preplay_interface =
    {get_preplay_result: label -> preplay_result,
     set_preplay_result: label -> preplay_result -> unit,
     get_preplay_time: label -> bool * Time.time,
     set_preplay_time: label -> bool * Time.time -> unit,
     preplay_quietly: Time.time -> isar_step -> bool * Time.time,
     (* the returned flag signals a preplay failure *)
     overall_preplay_stats: isar_proof -> (bool * Time.time) * bool}

  val proof_preplay_interface: bool -> Proof.context -> string -> string -> bool -> Time.time ->
    isar_proof -> preplay_interface
end;

structure Sledgehammer_Preplay : SLEDGEHAMMER_PREPLAY =
struct

open ATP_Util
open Sledgehammer_Util
open Sledgehammer_Proof

val trace = Attrib.setup_config_bool @{binding sledgehammer_preplay_trace} (K false)

datatype preplay_result =
  Preplay_Success of bool * Time.time |
  Preplay_Failure of exn

val zero_preplay_time = (false, Time.zeroTime) (* 0 ms *)
val some_preplay_time = (true, Time.zeroTime)  (* > 0 ms *)

fun add_preplay_time (b1, t1) (b2, t2) = (b1 orelse b2, Time.+ (t1, t2))

fun preplay_trace ctxt assms concl time =
  let
    val ctxt = ctxt |> Config.put show_markup true
    val time = "[" ^ string_of_ext_time time ^ "]" |> Pretty.str
    val nr_of_assms = length assms
    val assms = assms
      |> map (Display.pretty_thm ctxt)
      |> (fn [] => Pretty.str ""
           | [a] => a
           | assms => Pretty.enum ";" "\<lbrakk>" "\<rbrakk>" assms)  (* Syntax.pretty_term!? *)
    val concl = concl |> Syntax.pretty_term ctxt
    val trace_list = []
      |> cons concl
      |> nr_of_assms > 0 ? cons (Pretty.str "\<Longrightarrow>")
      |> cons assms
      |> cons time
    val pretty_trace = Pretty.blk (2, Pretty.breaks trace_list)
  in
    tracing (Pretty.string_of pretty_trace)
  end

fun take_time timeout tac arg =
  let val timing = Timing.start () in
    (TimeLimit.timeLimit timeout tac arg;
     Timing.result timing |> #cpu |> pair false)
    handle TimeLimit.TimeOut => (true, timeout)
  end

fun resolve_fact_names ctxt names =
  (names
   |>> map string_of_label
   |> op @
   |> maps (thms_of_name ctxt))
  handle ERROR msg => error ("preplay error: " ^ msg)

fun thm_of_proof ctxt (Proof (fixed_frees, assms, steps)) =
  let
    val thy = Proof_Context.theory_of ctxt

    val concl = 
      (case try List.last steps of
        SOME (Prove (_, [], _, t, _, _)) => t
      | _ => raise Fail "preplay error: malformed subproof")

    val var_idx = maxidx_of_term concl + 1
    fun var_of_free (x, T) = Var ((x, var_idx), T)
    val subst = map (`var_of_free #> swap #> apfst Free) fixed_frees
  in
    Logic.list_implies (assms |> map snd, concl)
    |> subst_free subst
    |> Skip_Proof.make_thm thy
  end

fun tac_of_method method type_enc lam_trans ctxt facts =
  (case method of
    MetisM => Metis_Tactic.metis_tac [type_enc] lam_trans ctxt facts
  | _ =>
    Method.insert_tac facts THEN'
    (case method of
      SimpM => Simplifier.asm_full_simp_tac
    | AutoM => Clasimp.auto_tac #> K
    | FastforceM => Clasimp.fast_force_tac
    | ForceM => Clasimp.force_tac
    | ArithM => Arith_Data.arith_tac
    | BlastM => blast_tac
    | _ => raise Fail "Sledgehammer_Preplay: tac_of_method") ctxt)

(* main function for preplaying Isar steps; may throw exceptions *)
fun preplay_raw _ _ _ _ _ (Let _) = zero_preplay_time
  | preplay_raw debug type_enc lam_trans ctxt timeout
      (step as Prove (_, xs, _, t, subproofs, (fact_names, meth))) =
    let
      val goal =
        (case xs of
          [] => t
        | _ =>
          (* proof obligation: !!thesis. (!!x. A x ==> thesis) ==> thesis
             (cf. "~~/src/Pure/Isar/obtain.ML") *)
          let
            val thesis = Term.Free ("thesis", HOLogic.boolT)
            val thesis_prop = thesis |> HOLogic.mk_Trueprop
            val frees = map Term.Free xs

            (* !!x1..xn. t ==> thesis (xs = [x1, .., xn]) *)
            val inner_prop = fold_rev Logic.all frees (Logic.mk_implies (t, thesis_prop))
          in
            (* !!thesis. (!!x1..xn. t ==> thesis) ==> thesis *)
            Logic.all thesis (Logic.mk_implies (inner_prop, thesis_prop))
          end)

      val facts = map (thm_of_proof ctxt) subproofs @ resolve_fact_names ctxt fact_names

      val ctxt' = ctxt
        |> debug ? (Config.put Metis_Tactic.verbose true #> Config.put Lin_Arith.verbose true)
        |> use_metis_new_skolem step ? Config.put Metis_Tactic.new_skolem true

      val prove = Goal.prove ctxt' [] [] goal

      fun tac {context = ctxt, ...} = HEADGOAL (tac_of_method meth type_enc lam_trans ctxt facts)
      fun run_tac () = prove tac handle ERROR msg => error ("Preplay error: " ^ msg)

      val preplay_time = take_time timeout run_tac ()
    in
      (if Config.get ctxt trace then preplay_trace ctxt facts goal preplay_time else ();
       preplay_time)
    end


(*** proof preplay interface ***)

type preplay_interface =
  {get_preplay_result: label -> preplay_result,
   set_preplay_result: label -> preplay_result -> unit,
   get_preplay_time: label -> bool * Time.time,
   set_preplay_time: label -> bool * Time.time -> unit,
   preplay_quietly: Time.time -> isar_step -> bool * Time.time,
   (* the returned flag signals a preplay failure *)
   overall_preplay_stats: isar_proof -> (bool * Time.time) * bool}

fun enrich_context_with_local_facts proof ctxt =
  let
    val thy = Proof_Context.theory_of ctxt

    fun enrich_with_fact l t =
      Proof_Context.put_thms false (string_of_label l, SOME [Skip_Proof.make_thm thy t])

    val enrich_with_assms = fold (uncurry enrich_with_fact)

    fun enrich_with_proof (Proof (_, assms, isar_steps)) =
      enrich_with_assms assms #> fold enrich_with_step isar_steps
    and enrich_with_step (Let _) = I
      | enrich_with_step (Prove (_, _, l, t, subproofs, _)) =
        enrich_with_fact l t #> fold enrich_with_proof subproofs
  in
    enrich_with_proof proof ctxt
  end

(* Given a proof, produces an imperative preplay interface with a shared table mapping from labels
   to preplay results. The preplay results are caluclated lazyly and cached to avoid repeated
   calculation.

   Precondition: The proof must be labeled canonically; cf.
   "Slegehammer_Proof.relabel_proof_canonically". *)
fun proof_preplay_interface debug ctxt type_enc lam_trans do_preplay preplay_timeout proof =
  if not do_preplay then
    (* the dont_preplay option pretends that everything works just fine *)
    {get_preplay_result = K (Preplay_Success zero_preplay_time),
     set_preplay_result = K (K ()),
     get_preplay_time = K zero_preplay_time,
     set_preplay_time = K (K ()),
     preplay_quietly = K (K zero_preplay_time),
     overall_preplay_stats = K (zero_preplay_time, false)} : preplay_interface
  else
    let
      val ctxt = enrich_context_with_local_facts proof ctxt

      fun preplay quietly timeout step =
        Preplay_Success (preplay_raw debug type_enc lam_trans ctxt timeout step)
        handle exn =>
               if Exn.is_interrupt exn then
                 reraise exn
               else if not quietly andalso debug then
                 (warning ("Preplay failure:\n  " ^ @{make_string} step ^ "\n  " ^
                    @{make_string} exn);
                  Preplay_Failure exn)
               else
                 Preplay_Failure exn

      (* preplay steps treating exceptions like timeouts *)
      fun preplay_quietly timeout step =
        (case preplay true timeout step of
          Preplay_Success preplay_time => preplay_time
        | Preplay_Failure _ => (true, timeout))

      val preplay_tab =
        let
          fun add_step_to_tab step tab =
            (case label_of_step step of
               NONE => tab
             | SOME l =>
               Canonical_Lbl_Tab.update_new
                 (l, (fn () => preplay false preplay_timeout step) |> Lazy.lazy) tab)
            handle Canonical_Lbl_Tab.DUP _ => raise Fail "Sledgehammer_Preplay: preplay time table"
        in
          Canonical_Lbl_Tab.empty
          |> fold_isar_steps add_step_to_tab (steps_of_proof proof)
          |> Unsynchronized.ref
        end

      fun get_preplay_result l =
        Canonical_Lbl_Tab.lookup (!preplay_tab) l |> the |> Lazy.force
        handle Option.Option => raise Fail "Sledgehammer_Preplay: preplay time table"

      fun set_preplay_result l result =
        preplay_tab := Canonical_Lbl_Tab.update (l, Lazy.value result) (!preplay_tab)

      fun get_preplay_time l =
        (case get_preplay_result l of
          Preplay_Success preplay_time => preplay_time
        | Preplay_Failure _ => some_preplay_time)

      fun set_preplay_time l = set_preplay_result l o Preplay_Success

      val result_of_step =
        try (label_of_step #> the #> get_preplay_result)
        #> the_default (Preplay_Success zero_preplay_time)

      fun do_step step =
        (case result_of_step step of
          Preplay_Success preplay_time => apfst (add_preplay_time preplay_time)
        | Preplay_Failure _ => apsnd (K true))

      fun overall_preplay_stats (Proof (_, _, steps)) =
        fold_isar_steps do_step steps (zero_preplay_time, false)
    in
      {get_preplay_result = get_preplay_result,
       set_preplay_result = set_preplay_result,
       get_preplay_time = get_preplay_time,
       set_preplay_time = set_preplay_time,
       preplay_quietly = preplay_quietly,
       overall_preplay_stats = overall_preplay_stats}
    end

end;
