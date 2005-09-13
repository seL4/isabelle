(*  Title:      Pure/Isar/isar_thy.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Derived theory and proof operations.
*)

signature ISAR_THY =
sig
  val add_axioms: ((bstring * string) * Attrib.src list) list -> theory -> theory
  val add_axioms_i: ((bstring * term) * theory attribute list) list -> theory -> theory
  val add_defs: bool * ((bstring * string) * Attrib.src list) list -> theory -> theory
  val add_defs_i: bool * ((bstring * term) * theory attribute list) list -> theory -> theory
  val apply_theorems: (thmref * Attrib.src list) list -> theory -> theory * thm list
  val apply_theorems_i: (thm list * theory attribute list) list -> theory -> theory * thm list
  val theorems: string ->
    ((bstring * Attrib.src list) * (thmref * Attrib.src list) list) list
    -> theory -> theory * (string * thm list) list
  val theorems_i: string ->
    ((bstring * theory attribute list) * (thm list * theory attribute list) list) list
    -> theory -> theory * (string * thm list) list
  val smart_theorems: string -> xstring option ->
    ((bstring * Attrib.src list) * (thmref * Attrib.src list) list) list ->
    theory -> theory * Proof.context
  val declare_theorems: xstring option ->
    (thmref * Attrib.src list) list -> theory -> theory * Proof.context
  val have: ((string * Attrib.src list) * (string * (string list * string list)) list) list ->
    bool -> Proof.state -> Proof.state
  val hence: ((string * Attrib.src list) * (string * (string list * string list)) list) list ->
    bool -> Proof.state -> Proof.state
  val show: ((string * Attrib.src list) * (string * (string list * string list)) list) list ->
    bool -> Proof.state -> Proof.state
  val thus: ((string * Attrib.src list) * (string * (string list * string list)) list) list ->
    bool -> Proof.state -> Proof.state
  val theorem: string -> string * Attrib.src list -> string * (string list * string list) ->
    theory -> Proof.state
  val theorem_i: string -> string * theory attribute list -> term * (term list * term list) ->
    theory -> Proof.state
  val qed: Method.text option -> Toplevel.transition -> Toplevel.transition
  val terminal_proof: Method.text * Method.text option ->
    Toplevel.transition -> Toplevel.transition
  val default_proof: Toplevel.transition -> Toplevel.transition
  val immediate_proof: Toplevel.transition -> Toplevel.transition
  val done_proof: Toplevel.transition -> Toplevel.transition
  val skip_proof: Toplevel.transition -> Toplevel.transition
  val forget_proof: Toplevel.transition -> Toplevel.transition
  val begin_theory: string -> string list -> (string * bool) list -> bool -> theory
  val end_theory: theory -> theory
  val kill_theory: string -> unit
  val theory: string * string list * (string * bool) list
    -> Toplevel.transition -> Toplevel.transition
  val init_context: ('a -> unit) -> 'a -> Toplevel.transition -> Toplevel.transition
  val context: string -> Toplevel.transition -> Toplevel.transition
end;

structure IsarThy: ISAR_THY =
struct

(* axioms and defs *)

fun add_axms f args thy =
  f (map (fn (x, srcs) => (x, map (Attrib.global_attribute thy) srcs)) args) thy;

val add_axioms = add_axms (#1 oo PureThy.add_axioms);
val add_axioms_i = #1 oo PureThy.add_axioms_i;
fun add_defs (x, args) = add_axms (#1 oo PureThy.add_defs x) args;
fun add_defs_i (x, args) = (#1 oo PureThy.add_defs_i x) args;


(* theorems *)

fun present_theorems kind (thy, named_thmss) =
  conditional (kind <> "" andalso kind <> Drule.internalK) (fn () =>
    Context.setmp (SOME thy) (Present.results (kind ^ "s")) named_thmss);

fun theorems kind args thy = thy
  |> PureThy.note_thmss (Drule.kind kind) (Attrib.map_facts (Attrib.global_attribute thy) args)
  |> tap (present_theorems kind);

fun theorems_i kind args =
  PureThy.note_thmss_i (Drule.kind kind) args
  #> tap (present_theorems kind);

fun apply_theorems args = apsnd (List.concat o map snd) o theorems "" [(("", []), args)];
fun apply_theorems_i args = apsnd (List.concat o map snd) o theorems_i "" [(("", []), args)];

fun smart_theorems kind NONE args thy = thy
      |> theorems kind args
      |> tap (present_theorems kind)
      |> (fn (thy, _) => (thy, ProofContext.init thy))
  | smart_theorems kind (SOME loc) args thy = thy
      |> Locale.note_thmss kind loc args
      |> tap (present_theorems kind o apfst #1)
      |> #1;

fun declare_theorems opt_loc args =
  smart_theorems "" opt_loc [(("", []), args)];


(* goals *)

local

fun local_goal opt_chain goal stmt int =
  opt_chain #> goal (K (K Seq.single)) stmt int;

fun global_goal goal kind a propp thy =
  goal kind (K (K I)) NONE a [(("", []), [propp])] (ProofContext.init thy);

in

val have = local_goal I Proof.have;
val hence = local_goal Proof.chain Proof.have;
val show = local_goal I Proof.show;
val thus = local_goal Proof.chain Proof.show;
val theorem = global_goal Proof.theorem;
val theorem_i = global_goal Proof.theorem_i;

end;


(* local endings *)

fun local_qed m = Toplevel.proof (ProofHistory.applys (Proof.local_qed (m, true)));
val local_terminal_proof = Toplevel.proof o ProofHistory.applys o Proof.local_terminal_proof;
val local_default_proof = Toplevel.proof (ProofHistory.applys Proof.local_default_proof);
val local_immediate_proof = Toplevel.proof (ProofHistory.applys Proof.local_immediate_proof);
val local_done_proof = Toplevel.proof (ProofHistory.applys Proof.local_done_proof);
val local_skip_proof = Toplevel.proof' (ProofHistory.applys o Proof.local_skip_proof);

val skip_local_qed =
  Toplevel.skip_proof (History.apply (fn i => if i > 1 then i - 1 else raise Toplevel.UNDEF));


(* global endings *)

fun global_ending ending = Toplevel.proof_to_theory_context (fn int => fn prf =>
  let
    val state = ProofHistory.current prf;
    val _ = Proof.assert_bottom true state handle Proof.STATE _ => raise Toplevel.UNDEF;
  in ending int state end);

fun global_qed m = global_ending (K (Proof.global_qed (m, true)));
val global_terminal_proof = global_ending o K o Proof.global_terminal_proof;
val global_default_proof = global_ending (K Proof.global_default_proof);
val global_immediate_proof = global_ending (K Proof.global_immediate_proof);
val global_skip_proof = global_ending Proof.global_skip_proof;
val global_done_proof = global_ending (K Proof.global_done_proof);

val skip_global_qed = Toplevel.skip_proof_to_theory (equal 1 o History.current);


(* common endings *)

fun qed m = local_qed m o global_qed m o skip_local_qed o skip_global_qed;
fun terminal_proof m = local_terminal_proof m o global_terminal_proof m;
val default_proof = local_default_proof o global_default_proof;
val immediate_proof = local_immediate_proof o global_immediate_proof;
val done_proof = local_done_proof o global_done_proof;
val skip_proof = local_skip_proof o global_skip_proof;

val forget_proof =
  Toplevel.proof_to_theory (Proof.theory_of o ProofHistory.current) o
  Toplevel.skip_proof_to_theory (K true);


(* theory init and exit *)

fun begin_theory name imports uses =
  ThyInfo.begin_theory Present.begin_theory name imports (map (apfst Path.unpack) uses);

val end_theory = (ThyInfo.check_known_thy o Context.theory_name) ? ThyInfo.end_theory;

val kill_theory = ThyInfo.if_known_thy ThyInfo.remove_thy;

fun theory (name, imports, uses) =
  Toplevel.init_theory (begin_theory name imports uses)
    (fn thy => (end_theory thy; ()))
    (kill_theory o Context.theory_name);


(* context switch *)

fun fetch_context f x =
  (case Context.pass NONE f x of
    ((), NONE) => raise Toplevel.UNDEF
  | ((), SOME thy) => thy);

fun init_context f x = Toplevel.init_theory (fn _ => fetch_context f x) (K ()) (K ());

val context = init_context (ThyInfo.quiet_update_thy true);

end;
