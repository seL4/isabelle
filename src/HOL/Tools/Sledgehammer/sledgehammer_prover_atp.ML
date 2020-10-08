(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_prover_atp.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Makarius
    Author:     Jasmin Blanchette, TU Muenchen

ATPs as Sledgehammer provers.
*)

signature SLEDGEHAMMER_PROVER_ATP =
sig
  type mode = Sledgehammer_Prover.mode
  type prover = Sledgehammer_Prover.prover

  val atp_dest_dir : string Config.T
  val atp_problem_prefix : string Config.T
  val atp_completish : int Config.T
  val atp_full_names : bool Config.T

  val is_ho_atp : Proof.context -> string -> bool

  val run_atp : mode -> string -> prover
end;

structure Sledgehammer_Prover_ATP : SLEDGEHAMMER_PROVER_ATP =
struct

open ATP_Util
open ATP_Problem
open ATP_Problem_Generate
open ATP_Proof
open ATP_Proof_Reconstruct
open Sledgehammer_Util
open Sledgehammer_Proof_Methods
open Sledgehammer_Isar
open Sledgehammer_ATP_Systems
open Sledgehammer_Prover

(* Empty string means create files in Isabelle's temporary files directory. *)
val atp_dest_dir = Attrib.setup_config_string \<^binding>\<open>sledgehammer_atp_dest_dir\<close> (K "")
val atp_problem_prefix =
  Attrib.setup_config_string \<^binding>\<open>sledgehammer_atp_problem_prefix\<close> (K "prob")
val atp_completish = Attrib.setup_config_int \<^binding>\<open>sledgehammer_atp_completish\<close> (K 0)
(* In addition to being easier to read, readable names are often much shorter, especially if types
   are mangled in names. This makes a difference for some provers (e.g., E). For these reason, short
   names are enabled by default. *)
val atp_full_names = Attrib.setup_config_bool \<^binding>\<open>sledgehammer_atp_full_names\<close> (K false)

fun is_atp_of_format is_format ctxt name =
  let val thy = Proof_Context.theory_of ctxt in
    (case try (get_atp thy) name of
      SOME config =>
      exists (fn (_, ((_, format, _, _, _), _)) => is_format format) (#best_slices (config ()) ctxt)
    | NONE => false)
  end

val is_ho_atp = is_atp_of_format is_format_higher_order

fun choose_type_enc strictness best_type_enc format =
  the_default best_type_enc
  #> type_enc_of_string strictness
  #> adjust_type_enc format

fun has_bound_or_var_of_type pred =
  exists_subterm (fn Var (_, T as Type _) => pred T
                   | Abs (_, T as Type _, _) => pred T
                   | _ => false)

(* Unwanted equalities are those between a (bound or schematic) variable that does not properly
   occur in the second operand. *)
val is_exhaustive_finite =
  let
    fun is_bad_equal (Var z) t =
        not (exists_subterm (fn Var z' => z = z' | _ => false) t)
      | is_bad_equal (Bound j) t = not (loose_bvar1 (t, j))
      | is_bad_equal _ _ = false
    fun do_equals t1 t2 = is_bad_equal t1 t2 orelse is_bad_equal t2 t1
    fun do_formula pos t =
      (case (pos, t) of
        (_, \<^const>\<open>Trueprop\<close> $ t1) => do_formula pos t1
      | (true, Const (\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, _, t')) => do_formula pos t'
      | (true, Const (\<^const_name>\<open>All\<close>, _) $ Abs (_, _, t')) => do_formula pos t'
      | (false, Const (\<^const_name>\<open>Ex\<close>, _) $ Abs (_, _, t')) => do_formula pos t'
      | (_, \<^const>\<open>Pure.imp\<close> $ t1 $ t2) =>
        do_formula (not pos) t1 andalso (t2 = \<^prop>\<open>False\<close> orelse do_formula pos t2)
      | (_, \<^const>\<open>HOL.implies\<close> $ t1 $ t2) =>
        do_formula (not pos) t1 andalso (t2 = \<^const>\<open>False\<close> orelse do_formula pos t2)
      | (_, \<^const>\<open>Not\<close> $ t1) => do_formula (not pos) t1
      | (true, \<^const>\<open>HOL.disj\<close> $ t1 $ t2) => forall (do_formula pos) [t1, t2]
      | (false, \<^const>\<open>HOL.conj\<close> $ t1 $ t2) => forall (do_formula pos) [t1, t2]
      | (true, Const (\<^const_name>\<open>HOL.eq\<close>, _) $ t1 $ t2) => do_equals t1 t2
      | (true, Const (\<^const_name>\<open>Pure.eq\<close>, _) $ t1 $ t2) => do_equals t1 t2
      | _ => false)
  in do_formula true end

(* Facts containing variables of finite types such as "unit" or "bool" or of the form
   "ALL x. x = A | x = B | x = C" are likely to lead to untypable proofs for unsound type
   encodings. *)
fun is_dangerous_prop ctxt =
  transform_elim_prop
  #> (has_bound_or_var_of_type (is_type_surely_finite ctxt) orf is_exhaustive_finite)

fun get_slices slice slices =
  (0 upto length slices - 1) ~~ slices |> not slice ? (List.last #> single)

fun get_facts_of_filter _ [(_, facts)] = facts
  | get_facts_of_filter fact_filter factss =
    (case AList.lookup (op =) factss fact_filter of
      SOME facts => facts
    | NONE => snd (hd factss))

(* For low values of "max_facts", this fudge value ensures that most slices are invoked with a
   nontrivial amount of facts. *)
val max_fact_factor_fudge = 5

val mono_max_privileged_facts = 10

fun suffix_of_mode Auto_Try = "_try"
  | suffix_of_mode Try = "_try"
  | suffix_of_mode Normal = ""
  | suffix_of_mode MaSh = ""
  | suffix_of_mode Minimize = "_min"

(* Give the ATPs some slack before interrupting them the hard way. "z3_tptp" on Linux appears to be
   the only ATP that does not honor its time limit. *)
val atp_timeout_slack = seconds 1.0

(* Important messages are important but not so important that users want to see them each time. *)
val atp_important_message_keep_quotient = 25

fun run_atp mode name
    ({debug, verbose, overlord, type_enc, strict, lam_trans, uncurried_aliases, fact_filter,
     max_facts, max_mono_iters, max_new_mono_instances, isar_proofs, compress, try0, smt_proofs,
     slice, minimize, timeout, preplay_timeout, ...} : params)
    ({comment, state, goal, subgoal, subgoal_count, factss, found_proof, ...} : prover_problem) =
  let
    val thy = Proof.theory_of state
    val ctxt = Proof.context_of state

    val {exec, arguments, proof_delims, known_failures, prem_role, best_slices, best_max_mono_iters,
      best_max_new_mono_instances, ...} = get_atp thy name ()

    val full_proofs = isar_proofs |> the_default (mode = Minimize)
    val local_name = perhaps (try (unprefix remote_prefix)) name

    val completish = Config.get ctxt atp_completish
    val atp_mode = if completish > 0 then Sledgehammer_Completish completish else Sledgehammer
    val (_, hyp_ts, concl_t) = strip_subgoal goal subgoal ctxt
    val (dest_dir, problem_prefix) =
      if overlord then overlord_file_location_of_prover name
      else (Config.get ctxt atp_dest_dir, Config.get ctxt atp_problem_prefix)
    val problem_file_name =
      Path.basic (problem_prefix ^ (if overlord then "" else serial_string ()) ^
        suffix_of_mode mode ^ "_" ^ string_of_int subgoal)
    val prob_path =
      if dest_dir = "" then
        File.tmp_path problem_file_name
      else if File.exists (Path.explode dest_dir) then
        Path.append (Path.explode dest_dir) problem_file_name
      else
        error ("No such directory: " ^ quote dest_dir)
    val exec = exec full_proofs
    val command0 =
      (case find_first (fn var => getenv var <> "") (fst exec) of
        SOME var =>
        let
          val pref = getenv var ^ "/"
          val paths =
            map (Path.explode o prefix pref)
              (if ML_System.platform_is_windows then
                map (suffix ".exe") (snd exec) @ snd exec
               else snd exec);
        in
          (case find_first File.exists paths of
            SOME path => path
          | NONE => error ("Bad executable: " ^ Path.print (hd paths)))
        end
      | NONE => error ("The environment variable " ^ quote (List.last (fst exec)) ^ " is not set"))

    fun split_time s =
      let
        val split = String.tokens (fn c => str c = "\n")
        val (output, t) = s |> split |> (try split_last #> the_default ([], "0")) |>> cat_lines
        val num = Scan.many1 Symbol.is_ascii_digit >> (fst o read_int)
        val digit = Scan.one Symbol.is_ascii_digit
        val num3 = digit ::: digit ::: (digit >> single) >> (fst o read_int)
        val time = num --| Scan.$$ "." -- num3 >> (fn (a, b) => a * 1000 + b)
        val as_time = raw_explode #> Scan.read Symbol.stopper time #> the_default 0
      in (output, as_time t |> Time.fromMilliseconds) end

    fun run () =
      let
        (* If slicing is disabled, we expand the last slice to fill the entire time available. *)
        val all_slices = best_slices ctxt
        val actual_slices = get_slices slice all_slices

        fun max_facts_of_slices (slices : (real * (slice_spec * string)) list) =
          fold (Integer.max o fst o #1 o fst o snd) slices 0

        val num_actual_slices = length actual_slices
        val max_fact_factor =
          Real.fromInt (case max_facts of NONE => max_facts_of_slices all_slices | SOME max => max)
          / Real.fromInt (max_facts_of_slices (map snd actual_slices))

        fun monomorphize_facts facts =
          let
            val ctxt =
              ctxt
              |> repair_monomorph_context max_mono_iters best_max_mono_iters max_new_mono_instances
                   best_max_new_mono_instances
            (* pseudo-theorem involving the same constants as the subgoal *)
            val subgoal_th =
              Logic.list_implies (hyp_ts, concl_t) |> Skip_Proof.make_thm thy
            val rths =
              facts |> chop mono_max_privileged_facts
                    |>> map (pair 1 o snd)
                    ||> map (pair 2 o snd)
                    |> op @
                    |> cons (0, subgoal_th)
          in
            Monomorph.monomorph atp_schematic_consts_of ctxt rths
            |> tl |> curry ListPair.zip (map fst facts)
            |> maps (fn (name, rths) => map (pair name o zero_var_indexes o snd) rths)
          end

        fun run_slice time_left (cache_key, cache_value) (slice, (time_frac,
            (key as ((best_max_facts, best_fact_filter), format, best_type_enc, best_lam_trans,
               best_uncurried_aliases),
             extra))) =
          let
            val effective_fact_filter = fact_filter |> the_default best_fact_filter
            val facts = get_facts_of_filter effective_fact_filter factss
            val num_facts =
              Real.ceil (max_fact_factor * Real.fromInt best_max_facts) + max_fact_factor_fudge
              |> Integer.min (length facts)
            val generate_info = (case format of DFG _ => true | _ => false)
            val strictness = if strict then Strict else Non_Strict
            val type_enc = type_enc |> choose_type_enc strictness best_type_enc format
            val sound = is_type_enc_sound type_enc
            val real_ms = Real.fromInt o Time.toMilliseconds
            val slice_timeout =
              (real_ms time_left
               |> (if slice < num_actual_slices - 1 then
                     curry Real.min (time_frac * real_ms timeout)
                   else
                     I))
              * 0.001
              |> seconds
            val generous_slice_timeout =
              if mode = MaSh then one_day else slice_timeout + atp_timeout_slack
            val _ =
              if debug then
                quote name ^ " slice #" ^ string_of_int (slice + 1) ^
                " with " ^ string_of_int num_facts ^ " fact" ^
                plural_s num_facts ^ " for " ^ string_of_time slice_timeout ^ "..."
                |> writeln
              else
                ()
            val readable_names = not (Config.get ctxt atp_full_names)
            val lam_trans = lam_trans |> the_default best_lam_trans
            val uncurried_aliases = uncurried_aliases |> the_default best_uncurried_aliases
            val value as (atp_problem, _, _, _) =
              if cache_key = SOME key then
                cache_value
              else
                facts
                |> not sound ? filter_out (is_dangerous_prop ctxt o Thm.prop_of o snd)
                |> take num_facts
                |> not (is_type_enc_polymorphic type_enc) ? monomorphize_facts
                |> map (apsnd Thm.prop_of)
                |> generate_atp_problem ctxt generate_info format prem_role type_enc atp_mode
                  lam_trans uncurried_aliases readable_names true hyp_ts concl_t

            fun sel_weights () = atp_problem_selection_weights atp_problem
            fun ord_info () = atp_problem_term_order_info atp_problem

            val ord = effective_term_order ctxt name
            val args =
              arguments ctxt full_proofs extra slice_timeout (File.bash_path prob_path)
                (ord, ord_info, sel_weights)
            val command =
              "(exec 2>&1; " ^ File.bash_path command0 ^ " " ^ args ^ " " ^ ")"
              |> enclose "TIMEFORMAT='%3R'; { time " " ; }"

            val _ =
              atp_problem
              |> lines_of_atp_problem format ord ord_info
              |> cons ("% " ^ command ^ "\n" ^ (if comment = "" then "" else "% " ^ comment ^ "\n"))
              |> File.write_list prob_path

            val ((output, run_time), (atp_proof, outcome)) =
              Timeout.apply generous_slice_timeout Isabelle_System.bash_output command
              |>> (if overlord then prefix ("% " ^ command ^ "\n% " ^ timestamp () ^ "\n") else I)
              |> fst |> split_time
              |> (fn accum as (output, _) =>
                (accum,
                 extract_tstplike_proof_and_outcome verbose proof_delims known_failures output
                 |>> atp_proof_of_tstplike_proof (perhaps (try (unprefix remote_prefix)) name)
                   atp_problem
                 handle UNRECOGNIZED_ATP_PROOF () => ([], SOME ProofUnparsable)))
              handle Timeout.TIMEOUT _ => (("", slice_timeout), ([], SOME TimedOut))

            val outcome =
              (case outcome of
                NONE =>
                (case used_facts_in_unsound_atp_proof ctxt (map fst facts) atp_proof of
                  SOME facts =>
                  let
                    val failure = UnsoundProof (is_type_enc_sound type_enc, sort string_ord facts)
                  in
                    if debug then (warning (string_of_atp_failure failure); NONE) else SOME failure
                  end
                | NONE => (found_proof (); NONE))
              | _ => outcome)
          in
            ((SOME key, value), (output, run_time, facts, atp_proof, outcome),
              SOME (format, type_enc))
          end

        val timer = Timer.startRealTimer ()

        fun maybe_run_slice slice (result as (cache, (_, run_time0, _, _, SOME _), _)) =
            let val time_left = timeout - Timer.checkRealTimer timer in
              if time_left <= Time.zeroTime then
                result
              else
                run_slice time_left cache slice
                |> (fn (cache, (output, run_time, used_from, atp_proof, outcome),
                        format_type_enc) =>
                  (cache, (output, run_time0 + run_time, used_from, atp_proof, outcome),
                   format_type_enc))
            end
          | maybe_run_slice _ result = result
      in
        ((NONE, ([], Symtab.empty, [], Symtab.empty)),
         ("", Time.zeroTime, [], [], SOME InternalError), NONE)
        |> fold maybe_run_slice actual_slices
      end

    (* If the problem file has not been exported, remove it; otherwise, export
       the proof file too. *)
    fun clean_up () = if dest_dir = "" then (try File.rm prob_path; ()) else ()
    fun export (_, (output, _, _, _, _), _) =
      if dest_dir = "" then ()
      else File.write (Path.explode (Path.implode prob_path ^ "_proof")) output

    val ((_, (_, pool, lifted, sym_tab)), (output, run_time, used_from, atp_proof, outcome),
         SOME (format, type_enc)) =
      with_cleanup clean_up run () |> tap export

    val important_message =
      if mode = Normal andalso Random.random_range 0 (atp_important_message_keep_quotient - 1) = 0
      then extract_important_message output
      else ""

    val (used_facts, preferred_methss, message) =
      (case outcome of
        NONE =>
        let
          val used_facts = sort_by fst (used_facts_in_atp_proof ctxt (map fst used_from) atp_proof)
          val needs_full_types = is_typed_helper_used_in_atp_proof atp_proof
          val preferred_methss =
            (Metis_Method (NONE, NONE),
             bunches_of_proof_methods try0 smt_proofs needs_full_types
              (if atp_proof_prefers_lifting atp_proof then liftingN else hide_lamsN))
        in
          (used_facts, preferred_methss,
           fn preplay =>
              let
                val _ = if verbose then writeln "Generating proof text..." else ()

                fun isar_params () =
                  let
                    val metis_type_enc =
                      if is_typed_helper_used_in_atp_proof atp_proof then SOME full_typesN else NONE
                    val metis_lam_trans =
                      if atp_proof_prefers_lifting atp_proof then SOME liftingN else NONE
                    val atp_proof =
                      atp_proof
                      |> termify_atp_proof ctxt name format type_enc pool lifted sym_tab
                      |> local_name = spassN ? introduce_spass_skolems
                      |> factify_atp_proof (map fst used_from) hyp_ts concl_t
                  in
                    (verbose, (metis_type_enc, metis_lam_trans), preplay_timeout, compress, try0,
                     minimize, atp_proof, goal)
                  end

                val one_line_params = (preplay (), proof_banner mode name, subgoal, subgoal_count)
                val num_chained = length (#facts (Proof.goal state))
              in
                proof_text ctxt debug isar_proofs smt_proofs isar_params num_chained
                  one_line_params ^
                (if important_message <> "" then
                   "\n\nImportant message from Dr. Geoff Sutcliffe:\n" ^ important_message
                 else
                   "")
              end)
        end
      | SOME failure =>
        ([], (Auto_Method (* dummy *), []), fn _ => string_of_atp_failure failure))
  in
    {outcome = outcome, used_facts = used_facts, used_from = used_from,
     preferred_methss = preferred_methss, run_time = run_time, message = message}
  end

end;
