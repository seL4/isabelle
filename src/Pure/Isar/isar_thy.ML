(*  Title:      Pure/Isar/isar_thy.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Pure/Isar derived theory operations.
*)

signature ISAR_THY =
sig
  val hide_names: string * xstring list -> theory -> theory
  val hide_names_i: string * string list -> theory -> theory
  val add_axioms: ((bstring * string) * Attrib.src list) list -> theory -> theory
  val add_axioms_i: ((bstring * term) * theory attribute list) list -> theory -> theory
  val add_defs: bool * ((bstring * string) * Attrib.src list) list -> theory -> theory
  val add_defs_i: bool * ((bstring * term) * theory attribute list) list -> theory -> theory
  val theorems: string ->
    ((bstring * Attrib.src list) * (thmref * Attrib.src list) list) list
    -> theory -> theory * (string * thm list) list
  val theorems_i: string ->
    ((bstring * theory attribute list) * (thm list * theory attribute list) list) list
    -> theory -> theory * (string * thm list) list
  val locale_theorems: string -> xstring ->
    ((bstring * Attrib.src list) * (thmref * Attrib.src list) list) list
    -> theory -> (theory * Proof.context) * (bstring * thm list) list
  val locale_theorems_i: string -> string ->
    ((bstring * Attrib.src list) * (thm list * Attrib.src list) list) list ->
    theory -> (theory * Proof.context) * (string * thm list) list
  val smart_theorems: string -> xstring option ->
    ((bstring * Attrib.src list) * (thmref * Attrib.src list) list) list
    -> theory -> (theory * Proof.context) * (string * thm list) list
  val declare_theorems: xstring option ->
    (thmref * Attrib.src list) list -> theory -> theory * Proof.context
  val apply_theorems: (thmref * Attrib.src list) list -> theory -> theory * thm list
  val apply_theorems_i: (thm list * theory attribute list) list -> theory -> theory * thm list
  val theorem: string -> (bstring * Attrib.src list) * (string * (string list * string list))
    -> bool -> theory -> ProofHistory.T
  val theorem_i: string -> (bstring * theory attribute list) *
    (term * (term list * term list)) -> bool -> theory -> ProofHistory.T
  val multi_theorem: string -> (thm list * thm list -> theory -> theory) ->
    (cterm list -> Proof.context -> Proof.context -> thm -> thm) ->
    bstring * Attrib.src list -> Locale.element Locale.elem_expr list ->
    ((bstring * Attrib.src list) * (string * (string list * string list)) list) list
    -> bool -> theory -> ProofHistory.T
  val multi_theorem_i: string -> (thm list * thm list -> theory -> theory) ->
    (cterm list -> Proof.context -> Proof.context -> thm -> thm) ->
    bstring * theory attribute list ->
    Locale.element_i Locale.elem_expr list ->
    ((bstring * theory attribute list) * (term * (term list * term list)) list) list ->
    bool -> theory -> ProofHistory.T
  val locale_multi_theorem:
    string -> (thm list * thm list -> theory -> theory) ->
    (cterm list -> Proof.context -> Proof.context -> thm -> thm) ->
    xstring ->
    bstring * Attrib.src list -> Locale.element Locale.elem_expr list ->
    ((bstring * Attrib.src list) * (string * (string list * string list)) list) list ->
    bool -> theory -> ProofHistory.T
  val locale_multi_theorem_i:
    string -> (thm list * thm list -> theory -> theory) ->
    (cterm list -> Proof.context -> Proof.context -> thm -> thm) ->
    string ->
    bstring * Attrib.src list -> Locale.element_i Locale.elem_expr list ->
    ((bstring * Attrib.src list) * (term * (term list * term list)) list) list ->
    bool -> theory -> ProofHistory.T
  val smart_multi_theorem: string -> xstring option
    -> bstring * Attrib.src list -> Locale.element Locale.elem_expr list
    -> ((bstring * Attrib.src list) * (string * (string list * string list)) list) list
    -> bool -> theory -> ProofHistory.T
  val have: ((string * Attrib.src list) *
    (string * (string list * string list)) list) list -> ProofHistory.T -> ProofHistory.T
  val have_i: ((string * Proof.context attribute list) *
    (term * (term list * term list)) list) list -> ProofHistory.T -> ProofHistory.T
  val hence: ((string * Attrib.src list) *
    (string * (string list * string list)) list) list -> ProofHistory.T -> ProofHistory.T
  val hence_i: ((string * Proof.context attribute list) *
    (term * (term list * term list)) list) list -> ProofHistory.T -> ProofHistory.T
  val show: ((string * Attrib.src list) *
    (string * (string list * string list)) list) list
    -> bool -> ProofHistory.T -> ProofHistory.T
  val show_i: ((string * Proof.context attribute list) *
    (term * (term list * term list)) list) list
    -> bool -> ProofHistory.T -> ProofHistory.T
  val thus: ((string * Attrib.src list) *
    (string * (string list * string list)) list) list
    -> bool -> ProofHistory.T -> ProofHistory.T
  val thus_i: ((string * Proof.context attribute list)
    * (term * (term list * term list)) list) list
    -> bool -> ProofHistory.T -> ProofHistory.T
  val obtain: (string list * string option) list
    * ((string * Attrib.src list) * (string * (string list * string list)) list) list
    -> Toplevel.transition -> Toplevel.transition
  val obtain_i: (string list * typ option) list
    * ((string * Proof.context attribute list) * (term * (term list * term list)) list) list
    -> Toplevel.transition -> Toplevel.transition
  val three_buffersN: string
  val cond_print: Toplevel.transition -> Toplevel.transition
  val qed: Method.text option -> Toplevel.transition -> Toplevel.transition
  val terminal_proof: Method.text * Method.text option
    -> Toplevel.transition -> Toplevel.transition
  val default_proof: Toplevel.transition -> Toplevel.transition
  val immediate_proof: Toplevel.transition -> Toplevel.transition
  val done_proof: Toplevel.transition -> Toplevel.transition
  val skip_proof: Toplevel.transition -> Toplevel.transition
  val forget_proof: Toplevel.transition -> Toplevel.transition
  val get_thmss: (thmref * Attrib.src list) list -> Proof.state -> thm list
  val also: (thmref * Attrib.src list) list option -> Toplevel.transition -> Toplevel.transition
  val also_i: thm list option -> Toplevel.transition -> Toplevel.transition
  val finally: (thmref * Attrib.src list) list option -> Toplevel.transition -> Toplevel.transition
  val finally_i: thm list option -> Toplevel.transition -> Toplevel.transition
  val moreover: Toplevel.transition -> Toplevel.transition
  val ultimately: Toplevel.transition -> Toplevel.transition
  val generic_setup: string -> theory -> theory
  val method_setup: bstring * string * string -> theory -> theory
  val add_oracle: bstring * string * string -> theory -> theory
  val register_globally:
    ((string * Attrib.src list) * Locale.expr) * string option list ->
    bool -> theory -> ProofHistory.T
  val register_in_locale:
    string * Locale.expr -> bool -> theory -> ProofHistory.T
  val register_locally:
    ((string * Attrib.src list) * Locale.expr) * string option list ->
    ProofHistory.T -> ProofHistory.T
  val begin_theory: string -> string list -> (string * bool) list -> theory
  val end_theory: theory -> theory
  val kill_theory: string -> unit
  val theory: string * string list * (string * bool) list
    -> Toplevel.transition -> Toplevel.transition
  val init_context: ('a -> unit) -> 'a -> Toplevel.transition -> Toplevel.transition
  val context: string -> Toplevel.transition -> Toplevel.transition
end;

structure IsarThy: ISAR_THY =
struct

(** derived theory and proof operations **)

(* name spaces *)

local

val kinds =
 [("class", (Sign.intern_class, can o Sign.certify_class, Theory.hide_classes_i)),
  ("type", (Sign.intern_type, Sign.declared_tyname, Theory.hide_types_i)),
  ("const", (Sign.intern_const, Sign.declared_const, Theory.hide_consts_i))];

fun gen_hide int (kind, xnames) thy =
  (case AList.lookup (op =) kinds kind of
    SOME (intern, check, hide) =>
      let
        val names = if int then map (intern thy) xnames else xnames;
        val bads = filter_out (check thy) names;
      in
        if null bads then hide true names thy
        else error ("Attempt to hide undeclared item(s): " ^ commas_quote bads)
      end
  | NONE => error ("Bad name space specification: " ^ quote kind));

in

val hide_names = gen_hide true;
val hide_names_i = gen_hide false;

end;


(* axioms and defs *)

fun add_axms f args thy =
  f (map (fn (x, srcs) => (x, map (Attrib.global_attribute thy) srcs)) args) thy;

val add_axioms = add_axms (#1 oo PureThy.add_axioms);
val add_axioms_i = #1 oo PureThy.add_axioms_i;
fun add_defs (x, args) = add_axms (#1 oo PureThy.add_defs x) args;
fun add_defs_i (x, args) = (#1 oo PureThy.add_defs_i x) args;


(* theorems *)

local

fun present_thmss kind (thy, named_thmss) =
  conditional (kind <> "" andalso kind <> Drule.internalK) (fn () =>
    Context.setmp (SOME thy) (Present.results (kind ^ "s")) named_thmss);

fun present_thmss' kind ((thy, _), named_thmss) = present_thmss kind (thy, named_thmss);

fun global_attribs thy = Attrib.map_facts (Attrib.global_attribute thy);

in

fun theorems_i k = tap (present_thmss k) oo PureThy.note_thmss_i (Drule.kind k);
fun locale_theorems_i k loc = tap (present_thmss' k) oo Locale.note_thmss_i k loc;

fun theorems k args thy = thy
  |> PureThy.note_thmss (Drule.kind k) (global_attribs thy args)
  |> tap (present_thmss k);

fun locale_theorems k loc args thy = thy
  |> Locale.note_thmss k loc args
  |> tap (present_thmss' k);

fun smart_theorems k NONE args thy =
      let val (thy', res) =
        thy |> PureThy.note_thmss (Drule.kind k) (global_attribs thy args)
      in
        present_thmss k (thy', res);
        ((thy', ProofContext.init thy'), res)
      end
  | smart_theorems k (SOME loc) args thy = thy
      |> Locale.note_thmss k loc args
      |> tap (present_thmss' k);

fun declare_theorems opt_loc args = #1 o smart_theorems "" opt_loc [(("", []), args)];

fun apply_theorems args = apsnd (List.concat o map snd) o theorems "" [(("", []), args)];
fun apply_theorems_i args = apsnd (List.concat o map snd) o theorems_i "" [(("", []), args)];

end;


(* local results *)

local

fun prt_facts ctxt =
  List.concat o (separate [Pretty.fbrk, Pretty.str "and "]) o
    map (single o ProofContext.pretty_fact ctxt);

fun pretty_results ctxt ((kind, ""), facts) =
      Pretty.block (Pretty.str kind :: Pretty.brk 1 :: prt_facts ctxt facts)
  | pretty_results ctxt ((kind, name), [fact]) = Pretty.blk (1,
      [Pretty.str (kind ^ " " ^ name ^ ":"), Pretty.fbrk, ProofContext.pretty_fact ctxt fact])
  | pretty_results ctxt ((kind, name), facts) = Pretty.blk (1,
      [Pretty.str (kind ^ " " ^ name ^ ":"), Pretty.fbrk,
        Pretty.blk (1, Pretty.str "(" :: prt_facts ctxt facts @ [Pretty.str ")"])]);

fun pretty_rule s ctxt thm =
  Pretty.block [Pretty.str (s ^ " to solve goal by exported rule:"),
    Pretty.fbrk, ProofContext.pretty_thm ctxt thm];

in

val print_result = Pretty.writeln oo pretty_results;
fun print_result' ctxt (k, res) = print_result ctxt ((k, ""), res);

fun cond_print_result_rule true =
      (print_result', priority oo (Pretty.string_of oo pretty_rule "Successful attempt"))
  | cond_print_result_rule false = (K (K ()), K (K ()));

fun proof'' f = Toplevel.proof' (f o cond_print_result_rule);

fun check_goal false state = state
  | check_goal true state =
      let
        val rule = ref (NONE: thm option);
        fun fail exn =
          (["Problem! Local statement will fail to solve any pending goal"] @
          (case exn of NONE => [] | SOME e => [Toplevel.exn_message e]) @
          (case ! rule of NONE => [] | SOME thm =>
            [Pretty.string_of (pretty_rule "Failed attempt" (Proof.context_of state) thm)]))
          |> cat_lines |> error;
        val check =
          (fn () => Seq.pull (SkipProof.local_skip_proof (K (K ()),
            fn _ => fn thm => rule := SOME thm) true state))
          |> setmp proofs 0
          |> transform_error;
        val result = (check (), NONE) handle Interrupt => raise Interrupt | e => (NONE, SOME e);
      in (case result of (SOME _, NONE) => () | (_, exn) => fail exn); state end;

end;


(* statements *)

local

fun global_statement f args int thy = ProofHistory.init (Toplevel.undo_limit int) (f args thy);
fun local_statement' f g args int = ProofHistory.apply (f args int o g);
fun local_statement f g args = local_statement' (K o f) g args ();

in

fun multi_theorem k after_qed export a elems concl int thy =
  global_statement (Proof.multi_theorem k after_qed export NONE a
    (map (Locale.intern_attrib_elem_expr thy) elems)) concl int thy;

fun multi_theorem_i k after_qed export a =
  global_statement o Proof.multi_theorem_i k after_qed export NONE a;

fun locale_multi_theorem k after_qed export locale (name, atts) elems concl int thy =
  global_statement (Proof.multi_theorem k after_qed export
      (SOME (locale,
        (map (Attrib.intern_src thy) atts,
         map (map (Attrib.intern_src thy) o snd o fst) concl)))
      (name, [])
      (map (Locale.intern_attrib_elem_expr thy) elems))
    (map (apfst (apsnd (K []))) concl) int thy;

fun locale_multi_theorem_i k after_qed export locale (name, atts) elems concl =
  global_statement (Proof.multi_theorem_i k after_qed export
      (SOME (locale, (atts, map (snd o fst) concl)))
      (name, []) elems) (map (apfst (apsnd (K []))) concl);

fun theorem k (a, t) =
  multi_theorem k (K I) ProofContext.export_standard a [] [(("", []), [t])];

fun theorem_i k (a, t) =
  multi_theorem_i k (K I) ProofContext.export_standard a [] [(("", []), [t])];

fun smart_multi_theorem k NONE a elems =
      multi_theorem k (K I) ProofContext.export_standard a elems
  | smart_multi_theorem k (SOME locale) a elems =
      locale_multi_theorem k (K I) ProofContext.export_standard locale a elems;

val have        = local_statement (Proof.have (K Seq.single) true) I;
val have_i      = local_statement (Proof.have_i (K Seq.single) true) I;
val hence       = local_statement (Proof.have (K Seq.single) true) Proof.chain;
val hence_i     = local_statement (Proof.have_i (K Seq.single) true) Proof.chain;
val show        = local_statement' (Proof.show check_goal (K Seq.single) true) I;
val show_i      = local_statement' (Proof.show_i check_goal (K Seq.single) true) I;
val thus        = local_statement' (Proof.show check_goal (K Seq.single) true) Proof.chain;
val thus_i      = local_statement' (Proof.show_i check_goal (K Seq.single) true) Proof.chain;

fun obtain (xs, asms) = proof'' (ProofHistory.applys o Obtain.obtain xs asms);
fun obtain_i (xs, asms) = proof'' (ProofHistory.applys o Obtain.obtain_i xs asms);

end;


(* local endings *)

val three_buffersN = "three_buffers";
val cond_print = Toplevel.print' three_buffersN;

val local_qed = proof'' o (ProofHistory.applys oo Proof.local_qed true);
val skip_local_qed =
  Toplevel.skip_proof (History.apply (fn i => if i > 1 then i - 1 else raise Toplevel.UNDEF));
val local_terminal_proof = proof'' o (ProofHistory.applys oo Proof.local_terminal_proof);
val local_default_proof = proof'' (ProofHistory.applys o Proof.local_default_proof);
val local_immediate_proof = proof'' (ProofHistory.applys o Proof.local_immediate_proof);
val local_done_proof = proof'' (ProofHistory.applys o Proof.local_done_proof);
val local_skip_proof = Toplevel.proof' (fn int =>
  ProofHistory.applys (SkipProof.local_skip_proof (cond_print_result_rule int) int));


(* global endings *)

fun name_results "" res = res
  | name_results name res =
      let
        val n = length (List.concat (map #2 res));
        fun name_res (i, (a, ths)) =
          let
            val m = length ths;
            val j = i + m;
          in
            if a <> "" then (j, (a, ths))
            else if m = n then (j, (name, ths))
            else if m = 1 then
              (j, (PureThy.string_of_thmref (NameSelection (name, [Single i])), ths))
            else (j, (PureThy.string_of_thmref (NameSelection (name, [FromTo (i, j - 1)])), ths))
          end;
      in #2 (foldl_map name_res (1, res)) end;

fun global_result finish = Toplevel.proof_to_theory_context (fn int => fn prf =>
  let
    val state = ProofHistory.current prf;
    val _ = if Proof.at_bottom state then () else raise Toplevel.UNDEF;
    val ((thy, ctxt), ((kind, name), res)) = finish int state;
  in
    if kind = "" orelse kind = Drule.internalK then ()
    else (print_result (Proof.context_of state) ((kind, name), res);
      Context.setmp (SOME thy) (Present.results kind) (name_results name res));
    (thy, ctxt)
  end);

fun global_qed m = global_result (K (Proof.global_qed true m));
val skip_global_qed = Toplevel.skip_proof_to_theory (equal 1 o History.current);
fun global_terminal_proof m = global_result (K (Proof.global_terminal_proof m));
val global_default_proof = global_result (K Proof.global_default_proof);
val global_immediate_proof = global_result (K Proof.global_immediate_proof);
val global_skip_proof = global_result SkipProof.global_skip_proof;
val global_done_proof = global_result (K Proof.global_done_proof);


(* common endings *)

fun qed meth = local_qed meth o global_qed meth o skip_local_qed o skip_global_qed;
fun terminal_proof meths = local_terminal_proof meths o global_terminal_proof meths;
val default_proof = local_default_proof o global_default_proof;
val immediate_proof = local_immediate_proof o global_immediate_proof;
val done_proof = local_done_proof o global_done_proof;
val skip_proof = local_skip_proof o global_skip_proof;
val forget_proof = Toplevel.proof_to_theory (Proof.theory_of o ProofHistory.current) o
  Toplevel.skip_proof_to_theory (K true);


(* calculational proof commands *)

local

fun cond_print_calc int ctxt thms =
  if int then
    Pretty.writeln (Pretty.big_list "calculation:" (map (ProofContext.pretty_thm ctxt) thms))
  else ();

fun proof''' f = Toplevel.proof' (f o cond_print_calc);

fun gen_calc get f args prt state =
  f (Option.map (fn srcs => get srcs state) args) prt state;

in

fun get_thmss srcs = Proof.the_facts o Proof.note_thmss [(("", []), srcs)];
fun get_thmss_i thms _ = thms;

fun also x = proof''' (ProofHistory.applys o gen_calc get_thmss Calculation.also x);
fun also_i x = proof''' (ProofHistory.applys o gen_calc get_thmss_i Calculation.also x);
fun finally x = proof''' (ProofHistory.applys o gen_calc get_thmss Calculation.finally x);
fun finally_i x = proof''' (ProofHistory.applys o gen_calc get_thmss_i Calculation.finally x);
val moreover = proof''' (ProofHistory.apply o Calculation.moreover);
val ultimately = proof''' (ProofHistory.apply o Calculation.ultimately);

end;


(* generic_setup *)

val generic_setup =
  Context.use_let "val setup: (theory -> theory) list" "Library.apply setup";


(* method_setup *)

fun method_setup (name, txt, cmt) =
  Context.use_let
    "val thm = PureThy.get_thm_closure (Context.the_context ()) o PureThy.Name;\n\
    \val thms = PureThy.get_thms_closure (Context.the_context ()) o PureThy.Name;\n\
    \val method: bstring * (Method.src -> Proof.context -> Proof.method) * string"
    "Method.add_method method"
    ("(" ^ Library.quote name ^ ", " ^ txt ^ ", " ^ Library.quote cmt ^ ")");


(* add_oracle *)

fun add_oracle (name, T, oracle) =
  let val txt =
    "local\n\
    \  type T = " ^ T ^ ";\n\
    \  val oracle: theory -> T -> term = " ^ oracle ^ ";\n\
    \  val name = " ^ quote name ^ ";\n\
    \  exception Arg of T;\n\
    \  val _ = Context.>> (Theory.add_oracle (name, fn (thy, Arg x) => oracle thy x));\n\
    \  val thy = Context.the_context ();\n\
    \  val invoke_" ^ name ^ " = Thm.invoke_oracle_i thy (Sign.full_name thy name);\n\
    \in\n\
    \  fun " ^ name ^ " thy x = invoke_" ^ name ^ " (thy, Arg x);\n\
    \end;\n";
  in Context.use_mltext_theory txt false end;


(* registration of locale interpretations *)

fun register_globally (((prfx, atts), expr), insts) int thy =
  let
    val (propss, after_qed) =
      Locale.prep_global_registration (prfx, atts) expr insts thy;
  in
    multi_theorem_i Drule.internalK (after_qed o fst) ProofContext.export_plain
      ("", []) []
      (map (fn ((n, _), props) => ((NameSpace.base n, []),
        map (fn prop => (prop, ([], []))) props)) propss) int thy
  end;

fun register_locally (((prfx, atts), expr), insts) =
  ProofHistory.apply (fn state =>
    let
      val ctxt = Proof.context_of state;
      val (propss, after_qed) =
        Locale.prep_local_registration (prfx, atts) expr insts ctxt;
    in
      state
      |> Proof.map_context (fn _ => ctxt)
      |> Proof.have_i (fn result => Seq.single o Proof.map_context (after_qed result)) true
        (map (fn ((n, _), props) => ((NameSpace.base n, []),
          map (fn prop => (prop, ([], []))) props)) propss)
    end);

fun register_in_locale (target, expr) int thy =
  let
    val target = Locale.intern thy target;
    val (propss, after_qed) =
        Locale.prep_registration_in_locale target expr thy;
  in
    locale_multi_theorem_i Drule.internalK (after_qed o fst)
      ProofContext.export_plain
      target ("",[]) []
      (map (fn ((n, _), props) => ((NameSpace.base n, []),
        map (fn prop => (prop, ([], []))) props)) propss) int thy
  end;


(* theory init and exit *)

fun gen_begin_theory upd name parents files =
  let
    val ml_filename = Path.pack (ThyLoad.ml_path name);
    (* FIXME unreliable test -- better make ThyInfo manage dependencies properly *)
    val _ = conditional (exists (equal ml_filename o #1) files) (fn () =>
      error ((quote ml_filename) ^ " not allowed in files section for theory " ^ name));
  in
    ThyInfo.begin_theory Present.begin_theory upd name parents
      (map (apfst Path.unpack) files)
  end;

val begin_theory = gen_begin_theory false;

fun end_theory thy =
  if ThyInfo.check_known_thy (Context.theory_name thy) then ThyInfo.end_theory thy
  else thy;

val kill_theory = ThyInfo.if_known_thy ThyInfo.remove_thy;


fun bg_theory (name, parents, files) int = gen_begin_theory int name parents files;
fun en_theory thy = (end_theory thy; ());

fun theory spec =
  Toplevel.init_theory (bg_theory spec) en_theory (kill_theory o Context.theory_name);


(* context switch *)

fun fetch_context f x =
  (case Context.pass NONE f x of
    ((), NONE) => raise Toplevel.UNDEF
  | ((), SOME thy) => thy);

fun init_context f x = Toplevel.init_theory (fn _ => fetch_context f x) (K ()) (K ());

val context = init_context (ThyInfo.quiet_update_thy true);

end;
