(*  Title:      Pure/Isar/isar_thy.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Derived theory and proof operations.
*)

signature ISAR_THY =
sig
  val add_axioms: ((bstring * string) * Attrib.src list) list -> theory -> theory
  val add_defs: (bool * bool) * ((bstring * string) * Attrib.src list) list -> theory -> theory
  val apply_theorems: (thmref * Attrib.src list) list -> theory -> thm list * theory
  val apply_theorems_i: (thm list * attribute list) list -> theory -> thm list * theory
  val have: ((string * Attrib.src list) * (string * string list) list) list ->
    bool -> Proof.state -> Proof.state
  val hence: ((string * Attrib.src list) * (string * string list) list) list ->
    bool -> Proof.state -> Proof.state
  val show: ((string * Attrib.src list) * (string * string list) list) list ->
    bool -> Proof.state -> Proof.state
  val thus: ((string * Attrib.src list) * (string * string list) list) list ->
    bool -> Proof.state -> Proof.state
  val theorem: string -> string * Attrib.src list -> string * string list -> theory -> Proof.state
  val theorem_i: string -> string * attribute list -> term * term list -> theory -> Proof.state
  val qed: Method.text option -> Toplevel.transition -> Toplevel.transition
  val terminal_proof: Method.text * Method.text option ->
    Toplevel.transition -> Toplevel.transition
  val default_proof: Toplevel.transition -> Toplevel.transition
  val immediate_proof: Toplevel.transition -> Toplevel.transition
  val done_proof: Toplevel.transition -> Toplevel.transition
  val skip_proof: Toplevel.transition -> Toplevel.transition
  val begin_theory: string -> string list -> (string * bool) list -> bool -> theory
  val end_theory: theory -> theory
  val kill_theory: string -> unit
  val theory: string * string list * (string * bool) list
    -> Toplevel.transition -> Toplevel.transition
  val init_context: ('a -> unit) -> 'a -> Toplevel.transition -> Toplevel.transition
end;

structure IsarThy: ISAR_THY =
struct

(* axioms *)

fun add_axms f args thy =
  f (map (fn (x, srcs) => (x, map (Attrib.attribute thy) srcs)) args) thy;

val add_axioms = add_axms (snd oo PureThy.add_axioms);

fun add_defs ((unchecked, overloaded), args) =
  add_axms
    (snd oo (if unchecked then PureThy.add_defs_unchecked else PureThy.add_defs) overloaded) args;


(* facts *)

fun apply_theorems args thy =
  let val facts = Attrib.map_facts (Attrib.attribute thy) [(("", []), args)]
  in apfst (maps snd) (PureThy.note_thmss "" facts thy) end;

fun apply_theorems_i args = apfst (maps snd) o PureThy.note_thmss_i "" [(("", []), args)];


(* goals *)

local

fun local_goal opt_chain goal stmt int =
  opt_chain #> goal NONE (K Seq.single) stmt int;

fun global_goal goal kind a propp thy =
  goal kind NONE (K I) (SOME "") a [(("", []), [propp])] (ProofContext.init thy);

in

val have = local_goal I Proof.have;
val hence = local_goal Proof.chain Proof.have;
val show = local_goal I Proof.show;
val thus = local_goal Proof.chain Proof.show;
val theorem = global_goal Proof.theorem;
val theorem_i = global_goal Proof.theorem_i;

end;


(* local endings *)

fun local_qed m = Toplevel.proofs (Proof.local_qed (m, true));
val local_terminal_proof = Toplevel.proofs o Proof.local_terminal_proof;
val local_default_proof = Toplevel.proofs Proof.local_default_proof;
val local_immediate_proof = Toplevel.proofs Proof.local_immediate_proof;
val local_done_proof = Toplevel.proofs Proof.local_done_proof;
val local_skip_proof = Toplevel.proofs' Proof.local_skip_proof;

val skip_local_qed =
  Toplevel.skip_proof (History.apply (fn i => if i > 1 then i - 1 else raise Toplevel.UNDEF));


(* global endings *)

fun global_qed m = Toplevel.end_proof (K (Proof.global_qed (m, true)));
val global_terminal_proof = Toplevel.end_proof o K o Proof.global_terminal_proof;
val global_default_proof = Toplevel.end_proof (K Proof.global_default_proof);
val global_immediate_proof = Toplevel.end_proof (K Proof.global_immediate_proof);
val global_skip_proof = Toplevel.end_proof Proof.global_skip_proof;
val global_done_proof = Toplevel.end_proof (K Proof.global_done_proof);

val skip_global_qed = Toplevel.skip_proof_to_theory (equal 1);


(* common endings *)

fun qed m = local_qed m o global_qed m o skip_local_qed o skip_global_qed;
fun terminal_proof m = local_terminal_proof m o global_terminal_proof m;
val default_proof = local_default_proof o global_default_proof;
val immediate_proof = local_immediate_proof o global_immediate_proof;
val done_proof = local_done_proof o global_done_proof;
val skip_proof = local_skip_proof o global_skip_proof;


(* theory init and exit *)

fun begin_theory name imports uses =
  ThyInfo.begin_theory Present.begin_theory name imports (map (apfst Path.unpack) uses);

val end_theory = (ThyInfo.check_known_thy o Context.theory_name) ? ThyInfo.end_theory;

val kill_theory = ThyInfo.if_known_thy ThyInfo.remove_thy;

fun theory (name, imports, uses) =
  Toplevel.init_theory (begin_theory name imports uses)
    (fn thy => (end_theory thy; ()))
    (kill_theory o Context.theory_name);

fun init_context f x = Toplevel.init_theory
  (fn _ =>
    (case Context.pass NONE f x of
      ((), NONE) => raise Toplevel.UNDEF
    | ((), SOME thy) => thy))
  (K ()) (K ());

end;
