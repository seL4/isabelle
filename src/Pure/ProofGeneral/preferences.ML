(*  Title:      Pure/ProofGeneral/preferences.ML
    ID:         $Id$
    Author:     David Aspinall and Markus Wenzel

User preferences for Isabelle which are maintained by the interface.
*)

signature PREFERENCES =
sig
  type pgiptype = PgipTypes.pgiptype

  type isa_preference = { name: string,
                          descr: string,
                          default: string,
                          pgiptype: pgiptype,
                          get: unit -> string,
                          set: string -> unit }

  (* table of categories and preferences; names must be unique *)
  type isa_preference_table = (string * isa_preference list) list

  val preferences : isa_preference_table

  val remove      : string -> isa_preference_table -> isa_preference_table
  val set_default : string * string -> isa_preference_table -> isa_preference_table
end

structure Preferences : PREFERENCES =
struct

val thm_depsN = "thm_deps";    (* also in proof_general_pgip.ML: move to pgip_isabelle? *)

type pgiptype = PgipTypes.pgiptype

type isa_preference = { name: string,
                        descr: string,
                        default: string,
                        pgiptype: pgiptype,
                        get: unit -> string,
                        set: string -> unit }


fun mkpref get set typ nm descr =
    { name=nm, descr=descr, pgiptype=typ, get=get, set=set, default=get() } : isa_preference

fun mkpref_from_ref read write typ r nm descr =
    mkpref (fn()=> read (!r)) (fn v=> r:= (write v)) typ nm descr

val int_pref =
    mkpref_from_ref PgipTypes.int_to_pgstring (PgipTypes.read_pgipint (NONE,NONE))
                    (PgipTypes.Pgipint (NONE, NONE))
val nat_pref =
    mkpref_from_ref PgipTypes.int_to_pgstring PgipTypes.read_pgipnat PgipTypes.Pgipnat

val bool_pref =
    mkpref_from_ref PgipTypes.bool_to_pgstring PgipTypes.read_pgipbool PgipTypes.Pgipbool

val proof_pref =
    let
        fun get () = PgipTypes.bool_to_pgstring (! Proofterm.proofs >= 2)
        fun set s = Proofterm.proofs := (if PgipTypes.read_pgipbool s then 2 else 1)
    in
        mkpref get set PgipTypes.Pgipbool "full-proofs"
               "Record full proof objects internally"
    end

val thm_deps_pref =
    let
        fun get () = PgipTypes.bool_to_pgstring (print_mode_active thm_depsN)
        fun set s =  NAMED_CRITICAL "print_mode" (fn () =>
          if PgipTypes.read_pgipbool s then
            change print_mode (insert (op =) thm_depsN)
          else
            change print_mode (remove (op =) thm_depsN))
    in
        mkpref get set PgipTypes.Pgipbool "theorem-dependencies"
               "Track theorem dependencies within Proof General"
    end

val print_depth_pref =
    let
        fun get () = PgipTypes.int_to_pgstring (get_print_depth ())
        val set = print_depth o PgipTypes.read_pgipnat
    in
        mkpref get set PgipTypes.Pgipnat
               "print-depth" "Setting for the ML print depth"
    end


val display_preferences =
    [bool_pref show_types
               "show-types"
               "Include types in display of Isabelle terms",
     bool_pref show_sorts
               "show-sorts"
               "Include sorts in display of Isabelle terms",
     bool_pref show_consts
               "show-consts"
               "Show types of consts in Isabelle goal display",
     bool_pref long_names
               "long-names"
               "Show fully qualified names in Isabelle terms",
     bool_pref show_brackets
               "show-brackets"
               "Show full bracketing in Isabelle terms",
     bool_pref Proof.show_main_goal
               "show-main-goal"
               "Show main goal in proof state display",
     bool_pref Syntax.eta_contract
               "eta-contract"
               "Print terms eta-contracted"]

val advanced_display_preferences =
    [nat_pref goals_limit
              "goals-limit"
              "Setting for maximum number of goals printed",
     int_pref ProofContext.prems_limit
              "prems-limit"
              "Setting for maximum number of premises printed",
     print_depth_pref,
     bool_pref show_question_marks
               "show-question-marks"
               "Show leading question mark of variable name"]

val tracing_preferences =
    [bool_pref trace_simp
               "trace-simplifier"
               "Trace simplification rules.",
     nat_pref trace_simp_depth_limit
              "trace-simplifier-depth"
              "Trace simplifier depth limit.",
     bool_pref trace_rules
               "trace-rules"
               "Trace application of the standard rules",
     bool_pref Pattern.trace_unify_fail
               "trace-unification"
               "Output error diagnostics during unification",
     bool_pref Output.timing
               "global-timing"
               "Whether to enable timing in Isabelle.",
     bool_pref Toplevel.debug
                "debugging"
                "Whether to enable debugging.",
     bool_pref Codegen.auto_quickcheck
                "auto-quickcheck"
                "Whether to enable quickcheck automatically.",
     nat_pref Codegen.auto_quickcheck_time_limit
                "auto-quickcheck-time-limit"
                "Time limit for automatic quickcheck (in milliseconds)."]

val proof_preferences =
    [bool_pref quick_and_dirty
               "quick-and-dirty"
               "Take a few short cuts",
     bool_pref Toplevel.skip_proofs
               "skip-proofs"
               "Skip over proofs (interactive-only)",
     proof_pref,
     nat_pref Multithreading.max_threads
               "max-threads"
               "Maximum number of threads"]

val preferences =
    [("Display", display_preferences),
     ("Advanced Display", advanced_display_preferences),
     ("Tracing", tracing_preferences),
     ("Proof", proof_preferences)]

type isa_preference_table = (string * isa_preference list) list

fun remove name (preftable : isa_preference_table)  =
    map (fn (cat,prefs) =>
            (cat, filter_out (curry op= name o #name) prefs))
        preftable;

fun set_default (setname,newdefault) (preftable : isa_preference_table)  =
    map (fn (cat,prefs) =>
            (cat, map (fn (pref as {name,descr,default,pgiptype,get,set})
                          => if (name = setname) then
                                 (set newdefault;
                                  {name=name,descr=descr,default=newdefault,
                                  pgiptype=pgiptype,get=get,set=set})
                             else pref)
                  prefs))
        preftable;

end
