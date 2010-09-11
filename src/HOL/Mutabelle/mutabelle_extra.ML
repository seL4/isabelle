(*  Title:      HOL/Mutabelle/mutabelle_extra.ML
    Author:     Stefan Berghofer, Jasmin Blanchette, Lukas Bulwahn, TU Muenchen

    Invokation of Counterexample generators
*)
signature MUTABELLE_EXTRA =
sig

val take_random : int -> 'a list -> 'a list

datatype outcome = GenuineCex | PotentialCex | NoCex | Donno | Timeout | Error
type timing = (string * int) list

type mtd = string * (theory -> term -> outcome * (timing * (int * Quickcheck.report list) list option))

type mutant_subentry = term * (string * (outcome * (timing * Quickcheck.report option))) list
type detailed_entry = string * bool * term * mutant_subentry list

type subentry = string * int * int * int * int * int * int
type entry = string * bool * subentry list
type report = entry list

val quickcheck_mtd : string -> mtd
(*
val refute_mtd : mtd
val nitpick_mtd : mtd
*)

val freezeT : term -> term
val thms_of : bool -> theory -> thm list

val string_for_report : report -> string
val write_report : string -> report -> unit
val mutate_theorems_and_write_report :
  theory -> mtd list -> thm list -> string -> unit

val random_seed : real Unsynchronized.ref
end;

structure MutabelleExtra : MUTABELLE_EXTRA =
struct

(* Own seed; can't rely on the Isabelle one to stay the same *)
val random_seed = Unsynchronized.ref 1.0;


(* mutation options *)
val max_mutants = 4
val num_mutations = 1
(* soundness check: *)
(*val max_mutants = 1
val num_mutations = 0*)

(* quickcheck options *)
(*val quickcheck_generator = "SML"*)
val iterations = 10
val size = 5

exception RANDOM;

fun rmod x y = x - y * Real.realFloor (x / y);

local
  val a = 16807.0;
  val m = 2147483647.0;
in

fun random () = CRITICAL (fn () =>
  let val r = rmod (a * ! random_seed) m
  in (random_seed := r; r) end);

end;

fun random_range l h =
  if h < l orelse l < 0 then raise RANDOM
  else l + Real.floor (rmod (random ()) (real (h - l + 1)));

datatype outcome = GenuineCex | PotentialCex | NoCex | Donno | Timeout | Error
type timing = (string * int) list

type mtd = string * (theory -> term -> outcome * (timing * (int * Quickcheck.report list) list option))

type mutant_subentry = term * (string * (outcome * (timing * Quickcheck.report option))) list
type detailed_entry = string * bool * term * mutant_subentry list

type subentry = string * int * int * int * int * int * int
type entry = string * bool * subentry list
type report = entry list

fun inst_type insts (Type (s, Ts)) = Type (s, map (inst_type insts) Ts)
  | inst_type insts T = the_default HOLogic.intT (AList.lookup op = insts T)

fun preprocess thy insts t = Object_Logic.atomize_term thy
 (map_types (inst_type insts) (Mutabelle.freeze t));

fun invoke_quickcheck quickcheck_generator thy t =
  TimeLimit.timeLimit (Time.fromSeconds (!Auto_Tools.time_limit))
      (fn _ =>
          case Quickcheck.gen_test_term (ProofContext.init_global thy) true (SOME quickcheck_generator)
                                    size iterations (preprocess thy [] t) of
            (NONE, (time_report, report)) => (NoCex, (time_report, report))
          | (SOME _, (time_report, report)) => (GenuineCex, (time_report, report))) ()
  handle TimeLimit.TimeOut => (Timeout, ([("timelimit", !Auto_Tools.time_limit)], NONE))

fun quickcheck_mtd quickcheck_generator =
  ("quickcheck_" ^ quickcheck_generator, invoke_quickcheck quickcheck_generator)

  (*
fun invoke_refute thy t =
  let
    val res = MyRefute.refute_term thy [] t
    val _ = priority ("Refute: " ^ res)
  in
    case res of
      "genuine" => GenuineCex
    | "likely_genuine" => GenuineCex
    | "potential" => PotentialCex
    | "none" => NoCex
    | "unknown" => Donno
    | _ => Error
  end
  handle MyRefute.REFUTE (loc, details) =>
         (error ("Unhandled Refute error (" ^ quote loc ^ "): " ^ details ^
                   "."))
val refute_mtd = ("refute", invoke_refute)
*)

(*
open Nitpick_Util
open Nitpick_Rep
open Nitpick_Nut

fun invoke_nitpick thy t =
  let
    val ctxt = ProofContext.init_global thy
    val state = Proof.init ctxt
  in
    let
      val (res, _) = Nitpick.pick_nits_in_term state (Nitpick_Isar.default_params thy []) false [] t
      val _ = priority ("Nitpick: " ^ res)
    in
      case res of
        "genuine" => GenuineCex
      | "likely_genuine" => GenuineCex
      | "potential" => PotentialCex
      | "none" => NoCex
      | "unknown" => Donno
      | _ => Error
    end
    handle ARG (loc, details) =>
           (error ("Bad argument(s) to " ^ quote loc ^ ": " ^ details ^ "."))
         | BAD (loc, details) =>
           (error ("Internal error (" ^ quote loc ^ "): " ^ details ^ "."))
         | LIMIT (_, details) =>
           (warning ("Limit reached: " ^ details ^ "."); Donno)
         | NOT_SUPPORTED details =>
           (warning ("Unsupported case: " ^ details ^ "."); Donno)
         | NUT (loc, us) =>
           (error ("Invalid nut" ^ plural_s_for_list us ^
                   " (" ^ quote loc ^ "): " ^
                  commas (map (string_for_nut ctxt) us) ^ "."))
         | REP (loc, Rs) =>
           (error ("Invalid representation" ^ plural_s_for_list Rs ^
                   " (" ^ quote loc ^ "): " ^
                   commas (map string_for_rep Rs) ^ "."))
         | TERM (loc, ts) =>
           (error ("Invalid term" ^ plural_s_for_list ts ^
                   " (" ^ quote loc ^ "): " ^
                   commas (map (Syntax.string_of_term ctxt) ts) ^ "."))
         | TYPE (loc, Ts, ts) =>
           (error ("Invalid type" ^ plural_s_for_list Ts ^
                   (if null ts then
                      ""
                    else
                      " for term" ^ plural_s_for_list ts ^ " " ^
                      commas (map (quote o Syntax.string_of_term ctxt) ts)) ^
                   " (" ^ quote loc ^ "): " ^
                   commas (map (Syntax.string_of_typ ctxt) Ts) ^ "."))
         | Kodkod.SYNTAX (_, details) =>
           (warning ("Ill-formed Kodkodi output: " ^ details ^ "."); Error)
         | Refute.REFUTE (loc, details) =>
           (error ("Unhandled Refute error (" ^ quote loc ^ "): " ^ details ^
                   "."))
         | Exn.Interrupt => raise Exn.Interrupt
         | _ => (priority ("Unknown error in Nitpick"); Error)
  end
val nitpick_mtd = ("nitpick", invoke_nitpick)
*)

val comms = [@{const_name HOL.eq}, @{const_name HOL.disj}, @{const_name HOL.conj}]

val forbidden =
 [(* (@{const_name "power"}, "'a"), *)
  (*(@{const_name induct_equal}, "'a"),
  (@{const_name induct_implies}, "'a"),
  (@{const_name induct_conj}, "'a"),*)
  (@{const_name "undefined"}, "'a"),
  (@{const_name "default"}, "'a"),
  (@{const_name "dummy_pattern"}, "'a::{}"),
  (@{const_name "HOL.simp_implies"}, "prop => prop => prop"),
  (@{const_name "bot_fun_inst.bot_fun"}, "'a"),
  (@{const_name "top_fun_inst.top_fun"}, "'a"),
  (@{const_name "Pure.term"}, "'a"),
  (@{const_name "top_class.top"}, "'a"),
  (@{const_name "HOL.equal"}, "'a"),
  (@{const_name "Quotient.Quot_True"}, "'a")(*,
  (@{const_name "uminus"}, "'a"),
  (@{const_name "Nat.size"}, "'a"),
  (@{const_name "Groups.abs"}, "'a") *)]

val forbidden_thms =
 ["finite_intvl_succ_class",
  "nibble"]

val forbidden_consts =
 [@{const_name nibble_pair_of_char}]

fun is_forbidden_theorem (s, th) =
  let val consts = Term.add_const_names (prop_of th) [] in
    exists (member (op =) (space_explode "." s)) forbidden_thms orelse
    exists (member (op =) forbidden_consts) consts orelse
    length (space_explode "." s) <> 2 orelse
    String.isPrefix "type_definition" (List.last (space_explode "." s)) orelse
    String.isSuffix "_def" s orelse
    String.isSuffix "_raw" s
  end

val forbidden_mutant_constnames =
 ["HOL.induct_equal",
  "HOL.induct_implies",
  "HOL.induct_conj",
 @{const_name undefined},
 @{const_name default},
 @{const_name dummy_pattern},
 @{const_name "HOL.simp_implies"},
 @{const_name "bot_fun_inst.bot_fun"},
 @{const_name "top_fun_inst.top_fun"},
 @{const_name "Pure.term"},
 @{const_name "top_class.top"},
 @{const_name "HOL.equal"},
 @{const_name "Quotient.Quot_True"}]

fun is_forbidden_mutant t =
  let
    val consts = Term.add_const_names t []
  in
    exists (String.isPrefix "Nitpick") consts orelse
    exists (String.isSubstring "_sumC") consts orelse
    exists (member (op =) forbidden_mutant_constnames) consts
  end

fun is_executable_term thy t = can (TimeLimit.timeLimit (Time.fromMilliseconds 2000) (Quickcheck.test_term
 (ProofContext.init_global thy) false (SOME "SML") 1 0)) (preprocess thy [] t)
fun is_executable_thm thy th = is_executable_term thy (prop_of th)

val freezeT =
  map_types (map_type_tvar (fn ((a, i), S) =>
    TFree (if i = 0 then a else a ^ "_" ^ string_of_int i, S)))

fun thms_of all thy =
  filter
    (fn th => (all orelse Context.theory_name (theory_of_thm th) = Context.theory_name thy)
      (* andalso is_executable_thm thy th *))
    (map snd (filter_out is_forbidden_theorem (Mutabelle.all_unconcealed_thms_of thy)))

val count = length oo filter o equal

fun take_random 0 _ = []
  | take_random _ [] = []
  | take_random n xs =
    let val j = random_range 0 (length xs - 1) in
      Library.nth xs j :: take_random (n - 1) (nth_drop j xs)
    end

fun cpu_time description f =
  let
    val start = start_timing ()
    val result = Exn.capture f ()
    val time = Time.toMilliseconds (#cpu (end_timing start))
  in (Exn.release result, (description, time)) end

fun safe_invoke_mtd thy (mtd_name, invoke_mtd) t =
  let
    val _ = priority ("Invoking " ^ mtd_name)
    val ((res, (timing, reports)), time) = cpu_time "total time"
      (fn () => case try (invoke_mtd thy) t of
          SOME (res, (timing, reports)) => (res, (timing, reports))
        | NONE => (priority ("**** PROBLEMS WITH " ^ Syntax.string_of_term_global thy t);
           (Error , ([], NONE))))
    val _ = priority (" Done")
  in (res, (time :: timing, reports)) end

(* theory -> term list -> mtd -> subentry *)
(*
fun test_mutants_using_one_method thy mutants (mtd_name, invoke_mtd) =
  let
     val res = map (safe_invoke_mtd thy (mtd_name, invoke_mtd)) mutants
  in
    (mtd_name, count GenuineCex res, count PotentialCex res, count NoCex res,
     count Donno res, count Timeout res, count Error res)
  end

fun create_entry thy thm exec mutants mtds =
  (Thm.get_name_hint thm, exec, map (test_mutants_using_one_method thy mutants) mtds)
*)
fun create_detailed_entry thy thm exec mutants mtds =
  let
    fun create_mutant_subentry mutant = (mutant,
      map (fn (mtd_name, invoke_mtd) =>
        (mtd_name, safe_invoke_mtd thy (mtd_name, invoke_mtd) mutant)) mtds)
  in
    (Thm.get_name_hint thm, exec, prop_of thm, map create_mutant_subentry mutants)
  end

(* (theory -> thm -> bool -> term list -> mtd list -> 'a) -> theory -> mtd list -> thm -> 'a *)
fun mutate_theorem create_entry thy mtds thm =
  let
    val exec = is_executable_thm thy thm
    val _ = priority (if exec then "EXEC" else "NOEXEC")
    val mutants =
          (if num_mutations = 0 then
             [Thm.prop_of thm]
           else
             Mutabelle.mutate_mix (Thm.prop_of thm) thy comms forbidden
                                  num_mutations)
             |> filter_out is_forbidden_mutant
    val mutants =
      if exec then
        let
          val _ = priority ("BEFORE PARTITION OF " ^
                            Int.toString (length mutants) ^ " MUTANTS")
          val (execs, noexecs) = List.partition (is_executable_term thy) (take_random (20 * max_mutants) mutants)
          val _ = tracing ("AFTER PARTITION (" ^ Int.toString (length execs) ^
                           " vs " ^ Int.toString (length noexecs) ^ ")")
        in
          execs @ take_random (Int.max (0, max_mutants - length execs)) noexecs
        end
      else
        mutants
    val mutants = mutants
          |> take_random max_mutants
          |> map Mutabelle.freeze |> map freezeT
(*          |> filter (not o is_forbidden_mutant) *)
          |> List.mapPartial (try (Sign.cert_term thy))
    val _ = map (fn t => priority ("MUTANT: " ^ Syntax.string_of_term_global thy t)) mutants
  in
    create_entry thy thm exec mutants mtds
  end

(* theory -> mtd list -> thm list -> report *)
val mutate_theorems = map ooo mutate_theorem

fun string_of_outcome GenuineCex = "GenuineCex"
  | string_of_outcome PotentialCex = "PotentialCex"
  | string_of_outcome NoCex = "NoCex"
  | string_of_outcome Donno = "Donno"
  | string_of_outcome Timeout = "Timeout"
  | string_of_outcome Error = "Error"

fun string_of_mutant_subentry thy thm_name (t, results) =
  "mutant: " ^ Syntax.string_of_term_global thy t ^ "\n" ^
  space_implode "; "
    (map (fn (mtd_name, (outcome, timing)) => mtd_name ^ ": " ^ string_of_outcome outcome) results) ^
  "\n"

(* XML.tree -> string *)
fun plain_string_from_xml_tree t =
  Buffer.empty |> XML.add_content t |> Buffer.content
(* string -> string *)
val unyxml = plain_string_from_xml_tree o YXML.parse

fun string_of_mutant_subentry' thy thm_name (t, results) =
  let
    fun string_of_report (Quickcheck.Report {iterations = i, raised_match_errors = e,
      satisfied_assms = s, positive_concl_tests = p}) =
      "errors: " ^ string_of_int e ^ "; conclusion tests: " ^ string_of_int p
    fun string_of_reports NONE = ""
      | string_of_reports (SOME reports) =
        cat_lines (map (fn (size, [report]) =>
          "size " ^ string_of_int size ^ ": " ^ string_of_report report) (rev reports))
    fun string_of_mtd_result (mtd_name, (outcome, (timing, reports))) =
      mtd_name ^ ": " ^ string_of_outcome outcome ^ "; " ^
      space_implode "; " (map (fn (s, t) => (s ^ ": " ^ string_of_int t)) timing)
      (*^ "\n" ^ string_of_reports reports*)
  in
    "mutant of " ^ thm_name ^ ":\n"
    ^ unyxml (Syntax.string_of_term_global thy t) ^ "\n" ^ cat_lines (map string_of_mtd_result results)
  end

fun string_of_detailed_entry thy (thm_name, exec, t, mutant_subentries) = 
   thm_name ^ " " ^ (if exec then "[exe]" else "[noexe]") ^ ": " ^
   Syntax.string_of_term_global thy t ^ "\n" ^                                    
   cat_lines (map (string_of_mutant_subentry' thy thm_name) mutant_subentries) ^ "\n"

fun theoryfile_string_of_mutant_subentry thy thm_name (i, (t, results)) =
  "lemma " ^ thm_name ^ "_" ^ string_of_int (i + 1) ^ ":\n" ^
  "\"" ^ unyxml (Syntax.string_of_term_global thy t) ^
  "\" \nquickcheck[generator = SML]\nquickcheck[generator = predicate_compile_wo_ff]\n" ^
  "quickcheck[generator = predicate_compile_ff_nofs]\noops\n"

fun theoryfile_string_of_detailed_entry thy (thm_name, exec, t, mutant_subentries) =
  "subsubsection {* mutants of " ^ thm_name ^ " *}\n\n" ^
  cat_lines (map_index
    (theoryfile_string_of_mutant_subentry thy thm_name) mutant_subentries) ^ "\n"

(* subentry -> string *)
fun string_for_subentry (mtd_name, genuine_cex, potential_cex, no_cex, donno,
                         timeout, error) =
  "    " ^ mtd_name ^ ": " ^ Int.toString genuine_cex ^ "+ " ^
  Int.toString potential_cex ^ "= " ^ Int.toString no_cex ^ "- " ^
  Int.toString donno ^ "? " ^ Int.toString timeout ^ "T " ^
  Int.toString error ^ "!"
(* entry -> string *)
fun string_for_entry (thm_name, exec, subentries) =
  thm_name ^ " " ^ (if exec then "[exe]" else "[noexe]") ^ ":\n" ^
  cat_lines (map string_for_subentry subentries) ^ "\n"
(* report -> string *)
fun string_for_report report = cat_lines (map string_for_entry report)

(* string -> report -> unit *)
fun write_report file_name =
  File.write (Path.explode file_name) o string_for_report

(* theory -> mtd list -> thm list -> string -> unit *)
fun mutate_theorems_and_write_report thy mtds thms file_name =
  let
    val _ = priority "Starting Mutabelle..."
    val path = Path.explode file_name
    (* for normal report: *)
    (*val (gen_create_entry, gen_string_for_entry) = (create_entry, string_for_entry)*)
    (*for detailled report: *)
    val (gen_create_entry, gen_string_for_entry) =
      (create_detailed_entry, string_of_detailed_entry thy)
    val (gen_create_entry, gen_string_for_entry) =
      (create_detailed_entry, theoryfile_string_of_detailed_entry thy)
  in
    File.write path (
    "Mutation options = "  ^
      "max_mutants: " ^ string_of_int max_mutants ^
      "; num_mutations: " ^ string_of_int num_mutations ^ "\n" ^
    "QC options = " ^
      (*"quickcheck_generator: " ^ quickcheck_generator ^ ";*)
      "size: " ^ string_of_int size ^
      "; iterations: " ^ string_of_int iterations ^ "\n");
    map (File.append path o gen_string_for_entry o mutate_theorem gen_create_entry thy mtds) thms;
    ()
  end

end;
