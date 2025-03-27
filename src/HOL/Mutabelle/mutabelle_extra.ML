(*  Title:      HOL/Mutabelle/mutabelle_extra.ML
    Author:     Stefan Berghofer, Jasmin Blanchette, Lukas Bulwahn, TU Muenchen

Invokation of Counterexample generators.
*)

signature MUTABELLE_EXTRA =
sig

val take_random : int -> 'a list -> 'a list

datatype outcome = GenuineCex | PotentialCex | NoCex | Donno | Timeout | Error | Solved | Unsolved
type timings = (string * int) list

type mtd = string * (theory -> term -> outcome * timings)

type mutant_subentry = term * (string * (outcome * timings)) list
type detailed_entry = string * bool * term * mutant_subentry list

type subentry = string * int * int * int * int * int * int
type entry = string * bool * subentry list
type report = entry list

val quickcheck_mtd : (Proof.context -> Proof.context) -> string -> mtd

val solve_direct_mtd : mtd
val try0_mtd : mtd
(*
val sledgehammer_mtd : mtd
*)
val nitpick_mtd : mtd

val refute_mtd : mtd

val freezeT : term -> term
val thms_of : bool -> theory -> thm list

val string_for_report : report -> string
val write_report : string -> report -> unit
val mutate_theorems_and_write_report :
  theory -> int * int -> mtd list -> thm list -> string -> unit

val init_random : real -> unit
end;

structure MutabelleExtra : MUTABELLE_EXTRA =
struct

(* Another Random engine *)

exception RANDOM;

fun rmod x y = x - y * Real.realFloor (x / y);

local
  (* Own seed; can't rely on the Isabelle one to stay the same *)
  val random_seed = Synchronized.var "random_seed" 1.0;

  val a = 16807.0;
  val m = 2147483647.0;
in

fun init_random r = Synchronized.change random_seed (K r);

fun random () =
  Synchronized.change_result random_seed
    (fn s =>
      let val r = rmod (a * s) m
      in (r, r) end);

end;

fun random_range l h =
  if h < l orelse l < 0 then raise RANDOM
  else l + Real.floor (rmod (random ()) (real (h - l + 1)));

fun take_random 0 _ = []
  | take_random _ [] = []
  | take_random n xs =
    let val j = random_range 0 (length xs - 1) in
      Library.nth xs j :: take_random (n - 1) (nth_drop j xs)
    end
  
(* possible outcomes *)

datatype outcome = GenuineCex | PotentialCex | NoCex | Donno | Timeout | Error | Solved | Unsolved

fun string_of_outcome GenuineCex = "GenuineCex"
  | string_of_outcome PotentialCex = "PotentialCex"
  | string_of_outcome NoCex = "NoCex"
  | string_of_outcome Donno = "Donno"
  | string_of_outcome Timeout = "Timeout"
  | string_of_outcome Error = "Error"
  | string_of_outcome Solved = "Solved"
  | string_of_outcome Unsolved = "Unsolved"

type timings = (string * int) list

type mtd = string * (theory -> term -> outcome * timings)

type mutant_subentry = term * (string * (outcome * timings)) list
type detailed_entry = string * bool * term * mutant_subentry list

type subentry = string * int * int * int * int * int * int
type entry = string * bool * subentry list
type report = entry list

(* possible invocations *)

(** quickcheck **)

fun invoke_quickcheck change_options thy t =
  Timeout.apply (seconds 30.0)
      (fn _ =>
          let
            val ctxt' = change_options (Proof_Context.init_global thy)
            val (result :: _) = case Quickcheck.active_testers ctxt' of
              [] => error "No active testers for quickcheck"
            | [tester] => tester ctxt' false [] [(t, [])]
            | _ => error "Multiple active testers for quickcheck"
          in
            case Quickcheck.counterexample_of result of 
              NONE => (NoCex, Quickcheck.timings_of result)
            | SOME _ => (GenuineCex, Quickcheck.timings_of result)
          end) ()
  handle Timeout.TIMEOUT _ =>
         (Timeout, [("timelimit", Real.floor (Options.default_real \<^system_option>\<open>auto_time_limit\<close>))])

fun quickcheck_mtd change_options quickcheck_generator =
  ("quickcheck_" ^ quickcheck_generator, invoke_quickcheck change_options)

(** solve direct **)
 
fun invoke_solve_direct thy t =
  let
    val state = Proof.theorem NONE (K I) (map (single o rpair []) [t]) (Proof_Context.init_global thy) 
  in
    case Solve_Direct.solve_direct state of
      (true, _) => (Solved, [])
    | (false, _) => (Unsolved, [])
  end

val solve_direct_mtd = ("solve_direct", invoke_solve_direct) 

(** try0 **)

fun invoke_try0 thy t =
  let
    val state = Proof.theorem NONE (K I) (map (single o rpair []) [t]) (Proof_Context.init_global thy)
  in
    case Try0.try0 (SOME (seconds 5.0)) Try0.empty_facts state of
      [] => (Unsolved, [])
    | _ => (Solved, [])
  end

val try0_mtd = ("try0", invoke_try0)

(** sledgehammer **)
(*
fun invoke_sledgehammer thy t =
  if can (Goal.prove_global thy (Term.add_free_names t [])  [] t)
      (fn {context, ...} => Sledgehammer_Tactics.sledgehammer_with_metis_tac context 1) then
    (Solved, ([], NONE))
  else
    (Unsolved, ([], NONE))

val sledgehammer_mtd = ("sledgehammer", invoke_sledgehammer)
*)

fun invoke_refute thy t =
  let
    val params = []
    val res = Refute.refute_term (Proof_Context.init_global thy) params [] t
    val _ = writeln ("Refute: " ^ res)
  in
    (rpair []) (case res of
      "genuine" => GenuineCex
    | "likely_genuine" => GenuineCex
    | "potential" => PotentialCex
    | "none" => NoCex
    | "unknown" => Donno
    | _ => Error)
  end
  handle Refute.REFUTE (loc, details) =>
         (error ("Unhandled Refute error (" ^ quote loc ^ "): " ^ details ^
                   "."))
val refute_mtd = ("refute", invoke_refute)

(** nitpick **)

fun invoke_nitpick thy t =
  let
    val ctxt = Proof_Context.init_global thy
    val state = Proof.init ctxt
    val (res, _) = Nitpick.pick_nits_in_term state
      (Nitpick_Commands.default_params thy []) Nitpick.Normal 1 1 1 [] [] [] t
    val _ = writeln ("Nitpick: " ^ res)
  in
    (rpair []) (case res of
      "genuine" => GenuineCex
    | "likely_genuine" => GenuineCex
    | "potential" => PotentialCex
    | "none" => NoCex
    | "unknown" => Donno
    | _ => Error)
  end

val nitpick_mtd = ("nitpick", invoke_nitpick)

(* filtering forbidden theorems and mutants *)

val comms = [\<^const_name>\<open>HOL.eq\<close>, \<^const_name>\<open>HOL.disj\<close>, \<^const_name>\<open>HOL.conj\<close>]

val forbidden =
 [(* (@{const_name "power"}, "'a"), *)
  (*(@{const_name induct_equal}, "'a"),
  (@{const_name induct_implies}, "'a"),
  (@{const_name induct_conj}, "'a"),*)
  (\<^const_name>\<open>undefined\<close>, "'a"),
  (\<^const_name>\<open>default\<close>, "'a"),
  (\<^const_name>\<open>Pure.dummy_pattern\<close>, "'a::{}"),
  (\<^const_name>\<open>HOL.simp_implies\<close>, "prop => prop => prop"),
  (\<^const_name>\<open>bot_fun_inst.bot_fun\<close>, "'a"),
  (\<^const_name>\<open>top_fun_inst.top_fun\<close>, "'a"),
  (\<^const_name>\<open>Pure.term\<close>, "'a"),
  (\<^const_name>\<open>top_class.top\<close>, "'a"),
  (\<^const_name>\<open>Quotient.Quot_True\<close>, "'a")(*,
  (@{const_name "uminus"}, "'a"),
  (@{const_name "Nat.size"}, "'a"),
  (@{const_name "Groups.abs"}, "'a") *)]

val forbidden_thms =
 ["finite_intvl_succ_class",
  "nibble"]

val forbidden_consts = [\<^const_name>\<open>Pure.type\<close>]

fun is_forbidden_theorem ((s, _): Thm_Name.T, th) =
  let val consts = Term.add_const_names (Thm.prop_of th) [] in
    exists (member (op =) (Long_Name.explode s)) forbidden_thms orelse
    exists (member (op =) forbidden_consts) consts orelse
    Long_Name.count s <> 2 orelse
    String.isPrefix "type_definition" (List.last (Long_Name.explode s)) orelse
    String.isSuffix "_def" s orelse
    String.isSuffix "_raw" s orelse
    String.isPrefix "term_of" (List.last (Long_Name.explode s))
  end

val forbidden_mutant_constnames =
[\<^const_name>\<open>HOL.induct_equal\<close>,
 \<^const_name>\<open>HOL.induct_implies\<close>,
 \<^const_name>\<open>HOL.induct_conj\<close>,
 \<^const_name>\<open>HOL.induct_forall\<close>,
 \<^const_name>\<open>undefined\<close>,
 \<^const_name>\<open>default\<close>,
 \<^const_name>\<open>Pure.dummy_pattern\<close>,
 \<^const_name>\<open>HOL.simp_implies\<close>,
 \<^const_name>\<open>bot_fun_inst.bot_fun\<close>,
 \<^const_name>\<open>top_fun_inst.top_fun\<close>,
 \<^const_name>\<open>Pure.term\<close>,
 \<^const_name>\<open>top_class.top\<close>,
 (*@{const_name "HOL.equal"},*)
 \<^const_name>\<open>Quotient.Quot_True\<close>,
 \<^const_name>\<open>equal_fun_inst.equal_fun\<close>,
 \<^const_name>\<open>equal_bool_inst.equal_bool\<close>,
 \<^const_name>\<open>ord_fun_inst.less_eq_fun\<close>,
 \<^const_name>\<open>ord_fun_inst.less_fun\<close>,
 \<^const_name>\<open>Meson.skolem\<close>,
 \<^const_name>\<open>ATP.fequal\<close>,
 \<^const_name>\<open>ATP.fEx\<close>,
 \<^const_name>\<open>enum_prod_inst.enum_all_prod\<close>,
 \<^const_name>\<open>enum_prod_inst.enum_ex_prod\<close>,
 \<^const_name>\<open>Quickcheck_Random.catch_match\<close>,
 \<^const_name>\<open>Quickcheck_Exhaustive.unknown\<close>,
 \<^const_name>\<open>Num.Bit0\<close>, \<^const_name>\<open>Num.Bit1\<close>
 (*@{const_name Pure.imp}, @{const_name Pure.eq}*)]

val forbidden_mutant_consts =
  [
   (\<^const_name>\<open>Groups.zero_class.zero\<close>, \<^typ>\<open>prop => prop => prop\<close>),
   (\<^const_name>\<open>Groups.one_class.one\<close>, \<^typ>\<open>prop => prop => prop\<close>),
   (\<^const_name>\<open>Groups.plus_class.plus\<close>, \<^typ>\<open>prop => prop => prop\<close>),
   (\<^const_name>\<open>Groups.minus_class.minus\<close>, \<^typ>\<open>prop => prop => prop\<close>),
   (\<^const_name>\<open>Groups.times_class.times\<close>, \<^typ>\<open>prop => prop => prop\<close>),
   (\<^const_name>\<open>Lattices.inf_class.inf\<close>, \<^typ>\<open>prop => prop => prop\<close>),
   (\<^const_name>\<open>Lattices.sup_class.sup\<close>, \<^typ>\<open>prop => prop => prop\<close>),
   (\<^const_name>\<open>Orderings.bot_class.bot\<close>, \<^typ>\<open>prop => prop => prop\<close>),
   (\<^const_name>\<open>Orderings.ord_class.min\<close>, \<^typ>\<open>prop => prop => prop\<close>),
   (\<^const_name>\<open>Orderings.ord_class.max\<close>, \<^typ>\<open>prop => prop => prop\<close>),
   (\<^const_name>\<open>Rings.modulo\<close>, \<^typ>\<open>prop => prop => prop\<close>),
   (\<^const_name>\<open>Rings.divide\<close>, \<^typ>\<open>prop => prop => prop\<close>),
   (\<^const_name>\<open>GCD.gcd_class.gcd\<close>, \<^typ>\<open>prop => prop => prop\<close>),
   (\<^const_name>\<open>GCD.gcd_class.lcm\<close>, \<^typ>\<open>prop => prop => prop\<close>),
   (\<^const_name>\<open>Orderings.bot_class.bot\<close>, \<^typ>\<open>bool => prop\<close>),
   (\<^const_name>\<open>Groups.one_class.one\<close>, \<^typ>\<open>bool => prop\<close>),
   (\<^const_name>\<open>Groups.zero_class.zero\<close>,\<^typ>\<open>bool => prop\<close>),
   (\<^const_name>\<open>equal_class.equal\<close>,\<^typ>\<open>bool => bool => bool\<close>)]

fun is_forbidden_mutant t =
  let
    val const_names = Term.add_const_names t []
    val consts = Term.add_consts t []
  in
    exists (String.isPrefix "Nitpick") const_names orelse
    exists (String.isSubstring "_sumC") const_names orelse
    exists (member (op =) forbidden_mutant_constnames) const_names orelse
    exists (member (op =) forbidden_mutant_consts) consts
  end

(* executable via quickcheck *)

fun is_executable_term thy t =
  let
    val ctxt = Proof_Context.init_global thy
  in
    can (Timeout.apply (seconds 30.0)
      (Quickcheck.test_terms
        ((Context.proof_map (Quickcheck.set_active_testers ["exhaustive"]) #>
          Config.put Quickcheck.finite_types true #>
          Config.put Quickcheck.finite_type_size 1 #>
          Config.put Quickcheck.size 1 #> Config.put Quickcheck.iterations 1) ctxt)
        (false, false) [])) (map (rpair [] o Object_Logic.atomize_term ctxt)
        (fst (Variable.import_terms true [t] ctxt)))
  end

fun is_executable_thm thy th = is_executable_term thy (Thm.prop_of th)

val freezeT =
  map_types (map_type_tvar (fn ((a, i), S) =>
    TFree (if i = 0 then a else a ^ "_" ^ string_of_int i, S)))

fun thms_of all thy =
  filter
    (fn th => (all orelse Thm.theory_long_name th = Context.theory_long_name thy)
      (* andalso is_executable_thm thy th *))
    (map snd (filter_out is_forbidden_theorem (Global_Theory.all_thms_of thy false)))

fun elapsed_time description e =
  let val ({elapsed, ...}, result) = Timing.timing e ()
  in (result, (description, Time.toMilliseconds elapsed)) end
(*
fun unsafe_invoke_mtd thy (mtd_name, invoke_mtd) t =
  let
    val _ = writeln ("Invoking " ^ mtd_name)
    val ((res, (timing, reports)), time) = cpu_time "total time" (fn () => invoke_mtd thy t
      handle ERROR s => (tracing s; (Error, ([], NONE))))
    val _ = writeln (" Done")
  in (res, (time :: timing, reports)) end
*)  
fun safe_invoke_mtd thy (mtd_name, invoke_mtd) t =
  let
    val _ = writeln ("Invoking " ^ mtd_name)
    val (res, timing) = elapsed_time "total time"
      (fn () => case try (invoke_mtd thy) t of
          SOME (res, _) => res
        | NONE => (writeln ("**** PROBLEMS WITH " ^ Syntax.string_of_term_global thy t);
            Error))
    val _ = writeln (" Done")
  in (res, [timing]) end

(* creating entries *)

fun create_detailed_entry thy thm exec mutants mtds =
  let
    fun create_mutant_subentry mutant = (mutant,
      map (fn (mtd_name, invoke_mtd) =>
        (mtd_name, safe_invoke_mtd thy (mtd_name, invoke_mtd) mutant)) mtds)
  in
    (Thm.get_name_hint thm, exec, Thm.prop_of thm, map create_mutant_subentry mutants)
  end

(* (theory -> thm -> bool -> term list -> mtd list -> 'a) -> theory -> mtd list -> thm -> 'a *)
fun mutate_theorem create_entry thy (num_mutations, max_mutants) mtds thm =
  let
    val exec = is_executable_thm thy thm
    val _ = tracing (if exec then "EXEC" else "NOEXEC")
    val mutants =
          (if num_mutations = 0 then
             [Thm.prop_of thm]
           else
             Mutabelle.mutate_mix (Thm.prop_of thm) thy comms forbidden
                                  num_mutations)
             |> tap (fn muts => tracing ("mutants: " ^ string_of_int (length muts)))
             |> filter_out is_forbidden_mutant
    val mutants =
      if exec then
        let
          val _ = writeln ("BEFORE PARTITION OF " ^
                            string_of_int (length mutants) ^ " MUTANTS")
          val (execs, noexecs) = List.partition (is_executable_term thy) (take_random (20 * max_mutants) mutants)
          val _ = tracing ("AFTER PARTITION (" ^ string_of_int (length execs) ^
                           " vs " ^ string_of_int (length noexecs) ^ ")")
        in
          execs @ take_random (Int.max (0, max_mutants - length execs)) noexecs
        end
      else
        mutants
    val mutants = mutants
          |> map Mutabelle.freeze |> map freezeT
(*          |> filter (not o is_forbidden_mutant) *)
          |> map_filter (try (Sign.cert_term thy))
          |> filter (is_some o try (Thm.global_cterm_of thy))
          |> filter (is_some o try (Syntax.check_term (Proof_Context.init_global thy)))
          |> take_random max_mutants
    val _ = map (fn t => writeln ("MUTANT: " ^ Syntax.string_of_term_global thy t)) mutants
  in
    create_entry thy thm exec mutants mtds
  end

fun string_of_mutant_subentry' thy thm_name (t, results) =
  let
   (* fun string_of_report (Quickcheck.Report {iterations = i, raised_match_errors = e,
      satisfied_assms = s, positive_concl_tests = p}) =
      "errors: " ^ string_of_int e ^ "; conclusion tests: " ^ string_of_int p
    fun string_of_reports NONE = ""
      | string_of_reports (SOME reports) =
        cat_lines (map (fn (size, [report]) =>
          "size " ^ string_of_int size ^ ": " ^ string_of_report report) (rev reports))*)
    fun string_of_mtd_result (mtd_name, (outcome, timing)) =
      mtd_name ^ ": " ^ string_of_outcome outcome
      ^ "(" ^ space_implode "; " (map (fn (s, t) => (s ^ ": " ^ string_of_int t)) timing) ^ ")"
      (*^ "\n" ^ string_of_reports reports*)
  in
    "mutant of " ^ Thm_Name.short thm_name ^ ":\n" ^
      Pretty.pure_string_of (Syntax.pretty_term_global thy t) ^ "\n" ^
      space_implode "; " (map string_of_mtd_result results)
  end

fun string_of_detailed_entry thy (thm_name, exec, t, mutant_subentries) = 
   Thm_Name.short thm_name ^ " " ^ (if exec then "[exe]" else "[noexe]") ^ ": " ^
   Syntax.string_of_term_global thy t ^ "\n" ^                                    
   cat_lines (map (string_of_mutant_subentry' thy thm_name) mutant_subentries) ^ "\n"

(* subentry -> string *)
fun string_for_subentry (mtd_name, genuine_cex, potential_cex, no_cex, donno,
                         timeout, error) =
  "    " ^ mtd_name ^ ": " ^ string_of_int genuine_cex ^ "+ " ^
  string_of_int potential_cex ^ "= " ^ string_of_int no_cex ^ "- " ^
  string_of_int donno ^ "? " ^ string_of_int timeout ^ "T " ^
  string_of_int error ^ "!"

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
fun mutate_theorems_and_write_report thy (num_mutations, max_mutants) mtds thms file_name =
  let
    val _ = writeln "Starting Mutabelle..."
    val ctxt = Proof_Context.init_global thy
    val path = Path.explode file_name
    (* for normal report: *)
    (*
    val (gen_create_entry, gen_string_for_entry) = (create_entry, string_for_entry)
    *)
    (* for detailled report: *)
    val (gen_create_entry, gen_string_for_entry) = (create_detailed_entry, string_of_detailed_entry thy)
    (* for theory creation: *)
    (*val (gen_create_entry, gen_string_for_entry) = (create_detailed_entry, theoryfile_string_of_detailed_entry thy)*)
  in
    File.write path (
    "Mutation options = "  ^
      "max_mutants: " ^ string_of_int max_mutants ^
      "; num_mutations: " ^ string_of_int num_mutations ^ "\n" ^
    "QC options = " ^
      (*"quickcheck_generator: " ^ quickcheck_generator ^ ";*)
      "size: " ^ string_of_int (Config.get ctxt Quickcheck.size) ^
      "; iterations: " ^ string_of_int (Config.get ctxt Quickcheck.iterations) ^ "\n" ^
    "Isabelle environment = ISABELLE_GHC: " ^ getenv "ISABELLE_GHC" ^ "\n");
    map (File.append path o gen_string_for_entry o mutate_theorem gen_create_entry thy (num_mutations, max_mutants) mtds) thms;
    ()
  end

end;
