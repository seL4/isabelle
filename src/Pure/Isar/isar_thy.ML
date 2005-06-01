(*  Title:      Pure/Isar/isar_thy.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Pure/Isar derived theory operations.
*)

signature ISAR_THY =
sig
  val hide_space: string * xstring list -> theory -> theory
  val hide_space_i: string * string list -> theory -> theory
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
    -> theory -> theory * (bstring * thm list) list
  val locale_theorems_i: string -> string ->
    ((bstring * Attrib.src list) * (thm list * Attrib.src list) list) list ->
    theory -> theory * (string * thm list) list
  val smart_theorems: string -> xstring option ->
    ((bstring * Attrib.src list) * (thmref * Attrib.src list) list) list
    -> theory -> theory * (string * thm list) list
  val declare_theorems: xstring option ->
    (thmref * Attrib.src list) list -> theory -> theory
  val apply_theorems: (thmref * Attrib.src list) list -> theory -> theory * thm list
  val apply_theorems_i: (thm list * theory attribute list) list -> theory -> theory * thm list
  val have_facts: ((string * Attrib.src list) * (thmref * Attrib.src list) list) list
    -> ProofHistory.T -> ProofHistory.T
  val have_facts_i: ((string * Proof.context attribute list) *
    (thm * Proof.context attribute list) list) list -> ProofHistory.T -> ProofHistory.T
  val from_facts: (thmref * Attrib.src list) list list -> ProofHistory.T -> ProofHistory.T
  val from_facts_i: (thm * Proof.context attribute list) list list
    -> ProofHistory.T -> ProofHistory.T
  val with_facts: (thmref * Attrib.src list) list list -> ProofHistory.T -> ProofHistory.T
  val with_facts_i: (thm * Proof.context attribute list) list list
    -> ProofHistory.T -> ProofHistory.T
  val using_facts: (thmref * Attrib.src list) list list
    -> ProofHistory.T -> ProofHistory.T
  val using_facts_i: (thm * Proof.context attribute list) list list
    -> ProofHistory.T -> ProofHistory.T
  val chain: ProofHistory.T -> ProofHistory.T
  val fix: (string list * string option) list -> ProofHistory.T -> ProofHistory.T
  val fix_i: (string list * typ option) list -> ProofHistory.T -> ProofHistory.T
  val let_bind: (string list * string) list -> ProofHistory.T -> ProofHistory.T
  val let_bind_i: (term list * term) list -> ProofHistory.T -> ProofHistory.T
  val invoke_case: string * string option list * Attrib.src list -> ProofHistory.T -> ProofHistory.T
  val invoke_case_i: string * string option list * Proof.context attribute list
    -> ProofHistory.T -> ProofHistory.T
  val theorem: string -> (bstring * Attrib.src list) * (string * (string list * string list))
    -> bool -> theory -> ProofHistory.T
  val theorem_i: string -> (bstring * theory attribute list) *
    (term * (term list * term list)) -> bool -> theory -> ProofHistory.T
  val multi_theorem: string -> (theory -> theory) ->
    (cterm list -> Proof.context -> Proof.context -> thm -> thm) ->
    bstring * Attrib.src list -> Locale.element Locale.elem_expr list ->
    ((bstring * Attrib.src list) * (string * (string list * string list)) list) list
    -> bool -> theory -> ProofHistory.T
  val multi_theorem_i: string -> (theory -> theory) ->
    (cterm list -> Proof.context -> Proof.context -> thm -> thm) ->
    bstring * theory attribute list -> Locale.element_i Locale.elem_expr list
    -> ((bstring * theory attribute list) * (term * (term list * term list)) list) list
    -> bool -> theory -> ProofHistory.T
  val locale_multi_theorem: string -> xstring
    -> bstring * Attrib.src list -> Locale.element Locale.elem_expr list
    -> ((bstring * Attrib.src list) * (string * (string list * string list)) list) list
    -> bool -> theory -> ProofHistory.T
  val locale_multi_theorem_i: string -> string -> bstring * Attrib.src list
    -> Locale.element_i Locale.elem_expr list
    -> ((bstring * Attrib.src list) * (term * (term list * term list)) list) list
    -> bool -> theory -> ProofHistory.T
  val smart_multi_theorem: string -> xstring option
    -> bstring * Attrib.src list -> Locale.element Locale.elem_expr list
    -> ((bstring * Attrib.src list) * (string * (string list * string list)) list) list
    -> bool -> theory -> ProofHistory.T
  val assume: ((string * Attrib.src list) * (string * (string list * string list)) list) list
    -> ProofHistory.T -> ProofHistory.T
  val assume_i:
    ((string * Proof.context attribute list) * (term * (term list * term list)) list) list
    -> ProofHistory.T -> ProofHistory.T
  val presume: ((string * Attrib.src list) * (string * (string list * string list)) list) list
    -> ProofHistory.T -> ProofHistory.T
  val presume_i:
    ((string * Proof.context attribute list) * (term * (term list * term list)) list) list
    -> ProofHistory.T -> ProofHistory.T
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
  val local_def: (string * Attrib.src list) * (string * (string * string list))
    -> ProofHistory.T -> ProofHistory.T
  val local_def_i: (string * Attrib.src list) * (string * (term * term list))
    -> ProofHistory.T -> ProofHistory.T
  val obtain: (string list * string option) list
    * ((string * Attrib.src list) * (string * (string list * string list)) list) list
    -> Toplevel.transition -> Toplevel.transition
  val obtain_i: (string list * typ option) list
    * ((string * Proof.context attribute list) * (term * (term list * term list)) list) list
    -> Toplevel.transition -> Toplevel.transition
  val begin_block: ProofHistory.T -> ProofHistory.T
  val next_block: ProofHistory.T -> ProofHistory.T
  val end_block: ProofHistory.T -> ProofHistory.T
  val defer: int option -> ProofHistory.T -> ProofHistory.T
  val prefer: int -> ProofHistory.T -> ProofHistory.T
  val apply: Method.text -> ProofHistory.T -> ProofHistory.T
  val apply_end: Method.text -> ProofHistory.T -> ProofHistory.T
  val proof: Method.text option -> ProofHistory.T -> ProofHistory.T
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
  val parse_ast_translation: bool * string -> theory -> theory
  val parse_translation: bool * string -> theory -> theory
  val print_translation: bool * string -> theory -> theory
  val typed_print_translation: bool * string -> theory -> theory
  val print_ast_translation: bool * string -> theory -> theory
  val token_translation: string -> theory -> theory
  val generic_setup: string -> theory -> theory
  val method_setup: bstring * string * string -> theory -> theory
  val add_oracle: bstring * string -> theory -> theory
  val add_locale: bool * bstring * Locale.expr * Locale.element list -> theory -> theory
  val register_globally:
    ((string * Attrib.src list) * Locale.expr) * string option list ->
    bool -> theory -> ProofHistory.T
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
 [(Sign.classK, can o Sign.certify_class),
  (Sign.typeK, Sign.declared_tyname),
  (Sign.constK, Sign.declared_const)];

fun gen_hide intern (kind, xnames) thy =
  (case assoc (kinds, kind) of
    SOME check =>
      let
        val sg = Theory.sign_of thy;
        val names = map (intern sg kind) xnames;
        val bads = filter_out (check sg) names;
      in
        if null bads then Theory.hide_space_i true (kind, names) thy
        else error ("Attempt to hide undeclared item(s): " ^ commas_quote bads)
      end
  | NONE => error ("Bad name space specification: " ^ quote kind));

in

fun hide_space x = gen_hide Sign.intern x;
fun hide_space_i x = gen_hide (K (K I)) x;

end;


(* axioms and defs *)

fun add_axms f args thy =
  f (map (fn (x, srcs) => (x, map (Attrib.global_attribute thy) srcs)) args) thy;

val add_axioms = add_axms (#1 oo PureThy.add_axioms);
val add_axioms_i = #1 oo PureThy.add_axioms_i;
fun add_defs (x, args) = add_axms (#1 oo PureThy.add_defs x) args;
fun add_defs_i (x, args) = (#1 oo PureThy.add_defs_i x) args;


(* attributes *)

local

fun prep_attribs f = map (fn ((name, more_srcs), th_srcs) =>
  ((name, map f more_srcs), map (apsnd (map f)) th_srcs));

in

fun global_attribs thy = prep_attribs (Attrib.global_attribute thy);
fun local_attribs thy = prep_attribs (Attrib.local_attribute thy);

end;


(* theorems *)

local

fun present_thmss kind (thy, named_thmss) =
 (conditional (kind <> "" andalso kind <> Drule.internalK) (fn () =>
    Context.setmp (SOME thy) (Present.results (kind ^ "s")) named_thmss);
  (thy, named_thmss));

in

fun theorems_i k = present_thmss k oo PureThy.note_thmss_i (Drule.kind k);
fun locale_theorems_i k loc = present_thmss k oo Locale.note_thmss_i k loc;

fun theorems k args thy = thy
  |> PureThy.note_thmss (Drule.kind k) (global_attribs thy args)
  |> present_thmss k;

fun locale_theorems k loc args thy = thy
  |> Locale.note_thmss k loc args
  |> present_thmss k;

fun smart_theorems k opt_loc args thy = thy
  |> (case opt_loc of
    NONE => PureThy.note_thmss (Drule.kind k) (global_attribs thy args)
  | SOME loc => Locale.note_thmss k loc args)
  |> present_thmss k;

fun declare_theorems opt_loc args = #1 o smart_theorems "" opt_loc [(("", []), args)];

fun apply_theorems args = apsnd (List.concat o map snd) o theorems "" [(("", []), args)];
fun apply_theorems_i args = apsnd (List.concat o map snd) o theorems_i "" [(("", []), args)];

end;


(* facts and forward chaining *)

fun local_thmss f args state = f (local_attribs (Proof.theory_of state) args) state;
fun local_thmss_i f args = f (map (fn ((name, more_atts), th_atts) =>
  ((name, more_atts), map (apfst single) th_atts)) args);

fun chain_thmss f args = ProofHistory.apply (Proof.chain o f (map (pair ("", [])) args));

val have_facts = ProofHistory.apply o local_thmss Proof.note_thmss;
val have_facts_i = ProofHistory.apply o local_thmss_i Proof.note_thmss_i;
val from_facts = chain_thmss (local_thmss Proof.note_thmss);
val from_facts_i = chain_thmss (local_thmss_i Proof.note_thmss_i);
val with_facts = chain_thmss (local_thmss Proof.with_thmss);
val with_facts_i = chain_thmss (local_thmss_i Proof.with_thmss_i);

fun using_facts args = ProofHistory.apply (fn state =>
  Proof.using_thmss (map (map (apsnd (map
    (Attrib.local_attribute (Proof.theory_of state))))) args) state);

val using_facts_i = ProofHistory.apply o Proof.using_thmss_i o map (map (apfst single));

val chain = ProofHistory.apply Proof.chain;


(* context *)

val fix = ProofHistory.apply o Proof.fix;
val fix_i = ProofHistory.apply o Proof.fix_i;
val let_bind = ProofHistory.apply o Proof.let_bind;
val let_bind_i = ProofHistory.apply o Proof.let_bind_i;

fun invoke_case (name, xs, src) = ProofHistory.apply (fn state =>
  Proof.invoke_case (name, xs,
    map (Attrib.local_attribute (Proof.theory_of state)) src) state);

val invoke_case_i = ProofHistory.apply o Proof.invoke_case;


(* local results *)

local

fun prt_facts ctxt =
  List.concat o (separate [Pretty.fbrk, Pretty.str "and "]) o
    map (single o ProofContext.pretty_fact ctxt);

fun pretty_results ctxt ((kind, ""), facts) =
      Pretty.block (Pretty.str kind :: Pretty.brk 1 :: prt_facts ctxt facts)
  | pretty_results ctxt ((kind, name), facts) = Pretty.blk (1,
      [Pretty.str (kind ^ " " ^ name ^ ":"), Pretty.fbrk,
        Pretty.blk (1, Pretty.str "(" :: prt_facts ctxt facts @ [Pretty.str ")"])]);

fun pretty_rule s ctxt thm =
  Pretty.block [Pretty.str (s ^ " to solve goal by exported rule:"),
    Pretty.fbrk, ProofContext.pretty_thm ctxt thm];

in

val print_result = Pretty.writeln oo pretty_results;
fun print_result' ctxt (k, res) = print_result ctxt ((k, ""), res);

fun cond_print_result_rule int = if int
  then (print_result',
        priority oo (Pretty.string_of oo pretty_rule "Successful attempt"))
  else (K (K ()), K (K ()));

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

fun global_attributes thy ((name, src), s) = ((name, map (Attrib.global_attribute thy) src), s);
fun local_attributes thy ((name, src), s) = ((name, map (Attrib.local_attribute thy) src), s);
fun local_attributes' state = local_attributes (Proof.theory_of state);

fun global_statement f args int thy =
  ProofHistory.init (Toplevel.undo_limit int) (f (map (global_attributes thy) args) thy);
fun global_statement_i f args int thy = ProofHistory.init (Toplevel.undo_limit int) (f args thy);

fun local_statement' f g args int = ProofHistory.apply (fn state =>
  f (map (local_attributes' state) args) int (g state));
fun local_statement_i' f g args int = ProofHistory.apply (f args int o g);
fun local_statement f g args = local_statement' (K o f) g args ();
fun local_statement_i f g args = local_statement_i' (K o f) g args ();

in

fun multi_theorem k after_qed export a elems concl int thy =
  global_statement (Proof.multi_theorem k after_qed export NONE
    (apsnd (map (Attrib.global_attribute thy)) a)
    (map (Locale.intern_attrib_elem_expr thy) elems)) concl int thy;

fun multi_theorem_i k after_qed export a =
  global_statement_i o Proof.multi_theorem_i k after_qed export NONE a;

fun locale_multi_theorem k locale (name, atts) elems concl int thy =
  global_statement (Proof.multi_theorem k I  ProofContext.export_standard
      (SOME (locale,
        (map (Attrib.intern_src (Theory.sign_of thy)) atts,
         map (map (Attrib.intern_src (Theory.sign_of thy)) o snd o fst) concl)))
      (name, [])
      (map (Locale.intern_attrib_elem_expr thy) elems))
    (map (apfst (apsnd (K []))) concl) int thy;

fun locale_multi_theorem_i k locale (name, atts) elems concl =
  global_statement_i (Proof.multi_theorem_i k I ProofContext.export_standard
      (SOME (locale, (atts, map (snd o fst) concl)))
      (name, []) elems) (map (apfst (apsnd (K []))) concl);

fun theorem k (a, t) =
  multi_theorem k I ProofContext.export_standard a [] [(("", []), [t])];

fun theorem_i k (a, t) =
  multi_theorem_i k I ProofContext.export_standard a [] [(("", []), [t])];

fun smart_multi_theorem k NONE a elems =
      multi_theorem k I ProofContext.export_standard a elems
  | smart_multi_theorem k (SOME locale) a elems =
      locale_multi_theorem k locale a elems;

val assume      = local_statement Proof.assume I;
val assume_i    = local_statement_i Proof.assume_i I;
val presume     = local_statement Proof.presume I;
val presume_i   = local_statement_i Proof.presume_i I;
val have        = local_statement (Proof.have Seq.single true) I;
val have_i      = local_statement_i (Proof.have_i Seq.single true) I;
val hence       = local_statement (Proof.have Seq.single true) Proof.chain;
val hence_i     = local_statement_i (Proof.have_i Seq.single true) Proof.chain;
val show        = local_statement' (Proof.show check_goal Seq.single true) I;
val show_i      = local_statement_i' (Proof.show_i check_goal Seq.single true) I;
val thus        = local_statement' (Proof.show check_goal Seq.single true) Proof.chain;
val thus_i      = local_statement_i' (Proof.show_i check_goal Seq.single true) Proof.chain;

fun gen_def f ((name, srcs), def) = ProofHistory.apply (fn state =>
  f name (map (Attrib.local_attribute (Proof.theory_of state)) srcs) def state);

val local_def = gen_def Proof.def;
val local_def_i = gen_def Proof.def_i;

fun obtain (xs, asms) = proof'' (ProofHistory.applys o (fn print => fn state =>
  Obtain.obtain xs (map (local_attributes' state) asms) print state));

fun obtain_i (xs, asms) = proof'' (ProofHistory.applys o Obtain.obtain_i xs asms);

end;


(* blocks *)

val begin_block = ProofHistory.apply Proof.begin_block;
val next_block = ProofHistory.apply Proof.next_block;
val end_block = ProofHistory.applys Proof.end_block;


(* shuffle state *)

fun shuffle meth i = Method.refine (Method.Basic (K (meth i))) o Proof.assert_no_chain;

fun defer i = ProofHistory.applys (shuffle Method.defer i);
fun prefer i = ProofHistory.applys (shuffle Method.prefer i);


(* backward steps *)

fun apply m = ProofHistory.applys
  (Seq.map (Proof.goal_facts (K [])) o Method.refine m o Proof.assert_backward);
fun apply_end m = ProofHistory.applys (Method.refine_end m o Proof.assert_forward);
val proof = ProofHistory.applys o Method.proof;


(* local endings *)

val local_qed = proof'' o (ProofHistory.applys oo Method.local_qed true);
val skip_local_qed =
  Toplevel.skip_proof (History.apply (fn i => if i > 1 then i - 1 else raise Toplevel.UNDEF));
val local_terminal_proof = proof'' o (ProofHistory.applys oo Method.local_terminal_proof);
val local_default_proof = proof'' (ProofHistory.applys o Method.local_default_proof);
val local_immediate_proof = proof'' (ProofHistory.applys o Method.local_immediate_proof);
val local_done_proof = proof'' (ProofHistory.applys o Method.local_done_proof);
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
              (j, (PureThy.string_of_thmref (name, SOME [PureThy.Single i]), ths))
            else (j, (PureThy.string_of_thmref (name, SOME [PureThy.FromTo (i, j - 1)]), ths))
          end;
      in #2 (foldl_map name_res (1, res)) end;

fun global_result finish = Toplevel.proof_to_theory' (fn int => fn prf =>
  let
    val state = ProofHistory.current prf;
    val _ = if Proof.at_bottom state then () else raise Toplevel.UNDEF;
    val (thy, ((kind, name), res)) = finish int state;
  in
    if kind = "" orelse kind = Drule.internalK then ()
    else (print_result (Proof.context_of state) ((kind, name), res);
      Context.setmp (SOME thy) (Present.results kind) (name_results name res));
    thy
  end);

fun global_qed m = global_result (K (Method.global_qed true m));
val skip_global_qed = Toplevel.skip_proof_to_theory (equal 1 o History.current);
fun global_terminal_proof m = global_result (K (Method.global_terminal_proof m));
val global_default_proof = global_result (K Method.global_default_proof);
val global_immediate_proof = global_result (K Method.global_immediate_proof);
val global_skip_proof = global_result SkipProof.global_skip_proof;
val global_done_proof = global_result (K Method.global_done_proof);


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

fun get_thmss srcs = Proof.the_facts o local_thmss Proof.note_thmss [(("", []), srcs)];
fun get_thmss_i thms _ = thms;

fun also x = proof''' (ProofHistory.applys o gen_calc get_thmss Calculation.also x);
fun also_i x = proof''' (ProofHistory.applys o gen_calc get_thmss_i Calculation.also x);
fun finally x = proof''' (ProofHistory.applys o gen_calc get_thmss Calculation.finally x);
fun finally_i x = proof''' (ProofHistory.applys o gen_calc get_thmss_i Calculation.finally x);
val moreover = proof''' (ProofHistory.apply o Calculation.moreover);
val ultimately = proof''' (ProofHistory.apply o Calculation.ultimately);

end;


(* translation functions *)

fun advancedT false = ""
  | advancedT true = "Sign.sg -> ";

fun advancedN false = ""
  | advancedN true = "advanced_";

fun parse_ast_translation (a, txt) =
  txt |> Context.use_let ("val parse_ast_translation: (string * (" ^ advancedT a ^
      "Syntax.ast list -> Syntax.ast)) list")
    ("Theory.add_" ^ advancedN a ^ "trfuns (parse_ast_translation, [], [], [])");

fun parse_translation (a, txt) =
  txt |> Context.use_let ("val parse_translation: (string * (" ^ advancedT a ^
      "term list -> term)) list")
    ("Theory.add_" ^ advancedN a ^ "trfuns ([], parse_translation, [], [])");

fun print_translation (a, txt) =
  txt |> Context.use_let ("val print_translation: (string * (" ^ advancedT a ^
      "term list -> term)) list")
    ("Theory.add_" ^ advancedN a ^ "trfuns ([], [], print_translation, [])");

fun print_ast_translation (a, txt) =
  txt |> Context.use_let ("val print_ast_translation: (string * (" ^ advancedT a ^
      "Syntax.ast list -> Syntax.ast)) list")
    ("Theory.add_" ^ advancedN a ^ "trfuns ([], [], [], print_ast_translation)");

fun typed_print_translation (a, txt) =
  txt |> Context.use_let ("val typed_print_translation: (string * (" ^ advancedT a ^
      "bool -> typ -> term list -> term)) list")
    ("Theory.add_" ^ advancedN a ^ "trfunsT typed_print_translation");

val token_translation =
  Context.use_let "val token_translation: (string * string * (string -> string * real)) list"
    "Theory.add_tokentrfuns token_translation";


(* generic_setup *)

val generic_setup =
  Context.use_let "val setup: (theory -> theory) list" "Library.apply setup";


(* method_setup *)

fun method_setup (name, txt, cmt) =
  Context.use_let
    "val thm = PureThy.get_thm_closure (Context.the_context ());\n\
    \val thms = PureThy.get_thms_closure (Context.the_context ());\n\
    \val method: bstring * (Method.src -> Proof.context -> Proof.method) * string"
    "Method.add_method method"
    ("(" ^ Library.quote name ^ ", " ^ txt ^ ", " ^ Library.quote cmt ^ ")");


(* add_oracle *)

fun add_oracle (name, txt) =
  Context.use_let
    "val oracle: bstring * (Sign.sg * Object.T -> term)"
    "Theory.add_oracle oracle"
    ("(" ^ Library.quote name ^ ", " ^ txt ^ ")");


(* add_locale *)

fun add_locale (do_pred, name, import, body) thy =
  Locale.add_locale do_pred name import body thy;


(* registration of locale interpretations *)

fun register_globally (((prfx, atts), expr), insts) int thy =
  let
    val (thy', propss, activate) =
      Locale.prep_global_registration (prfx, atts) expr insts thy;
    fun witness id (thy, thm) = let
        val thm' = Drule.freeze_all thm;
      in
        (Locale.add_global_witness id thm' thy, thm')
      end;
  in
    multi_theorem_i Drule.internalK activate ProofContext.export_plain
      ("", []) []
      (map (fn ((n, ps), props) => 
          ((NameSpace.base n, [witness (n, map Logic.varify ps)]), 
        map (fn prop => (prop, ([], []))) props)) propss) int thy'
  end;

fun register_locally (((prfx, atts), expr), insts) =
  ProofHistory.apply (fn state =>
    let
      val ctxt = Proof.context_of state;
      val (ctxt', propss, activate) =
        Locale.prep_local_registration (prfx, atts) expr insts ctxt;
      fun witness id (ctxt, thm) = (Locale.add_local_witness id thm ctxt, thm);
    in
      state
      |> Proof.map_context (fn _ => ctxt')
      |> Proof.have_i (Seq.single o Proof.map_context activate) true
        (map (fn (id as (n, _), props) => ((NameSpace.base n, [witness id]),
          map (fn prop => (prop, ([], []))) props)) propss)
    end);


(* theory init and exit *)

fun gen_begin_theory upd name parents files =
  let val ml_filename = Path.pack (ThyLoad.ml_path name);
      val () = if exists (equal ml_filename o #1) files
               then error ((quote ml_filename) ^ " not allowed in files section for theory " ^ name)
               else ()
  in ThyInfo.begin_theory Present.begin_theory upd name parents (map (apfst Path.unpack) files) end;

val begin_theory = gen_begin_theory false;

fun end_theory thy =
  if ThyInfo.check_known_thy (PureThy.get_name thy) then ThyInfo.end_theory thy
  else thy;

val kill_theory = ThyInfo.if_known_thy ThyInfo.remove_thy;


fun bg_theory (name, parents, files) int = gen_begin_theory int name parents files;
fun en_theory thy = (end_theory thy; ());

fun theory spec = Toplevel.init_theory (bg_theory spec) en_theory (kill_theory o PureThy.get_name);


(* context switch *)

fun fetch_context f x =
  (case Context.pass NONE f x of
    ((), NONE) => raise Toplevel.UNDEF
  | ((), SOME thy) => thy);

fun init_context f x = Toplevel.init_theory (fn _ => fetch_context f x) (K ()) (K ());

val context = init_context (ThyInfo.quiet_update_thy true);

end;
