(*  Title:      Pure/Isar/isar_cmd.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Non-logical toplevel commands.
*)

signature ISAR_CMD =
sig
  val break: Toplevel.transition -> Toplevel.transition
  val exit: Toplevel.transition -> Toplevel.transition
  val restart: Toplevel.transition -> Toplevel.transition
  val quit: Toplevel.transition -> Toplevel.transition
  val use: string -> Toplevel.transition -> Toplevel.transition
  val use_mltext_theory: string -> Toplevel.transition -> Toplevel.transition
  val use_mltext: string -> Toplevel.transition -> Toplevel.transition
  val use_commit: Toplevel.transition -> Toplevel.transition
  val cd: string -> Toplevel.transition -> Toplevel.transition
  val pwd: Toplevel.transition -> Toplevel.transition
  val use_thy: string -> Toplevel.transition -> Toplevel.transition
  val update_thy: string -> Toplevel.transition -> Toplevel.transition
  val print_theory: Toplevel.transition -> Toplevel.transition
  val print_syntax: Toplevel.transition -> Toplevel.transition
  val print_theorems: Toplevel.transition -> Toplevel.transition
  val print_attributes: Toplevel.transition -> Toplevel.transition
  val print_methods: Toplevel.transition -> Toplevel.transition
  val print_binds: Toplevel.transition -> Toplevel.transition
  val print_lthms: Toplevel.transition -> Toplevel.transition
  val print_thms: xstring * Args.src list -> Toplevel.transition -> Toplevel.transition
  val print_prop: string -> Toplevel.transition -> Toplevel.transition
  val print_term: string -> Toplevel.transition -> Toplevel.transition
  val print_type: string -> Toplevel.transition -> Toplevel.transition
end;

structure IsarCmd: ISAR_CMD =
struct


(* variations on exit *)

val break = Toplevel.keep (fn state => raise Toplevel.BREAK state);

val exit = Toplevel.keep (fn state =>
  (Context.set_context (try Toplevel.theory_of state);
    writeln "Leaving the Isar loop.  Invoke 'main_loop();' to restart.";
    raise Toplevel.TERMINATE));

val restart = Toplevel.imperative (fn () => raise Toplevel.RESTART);
val quit = Toplevel.imperative quit;


(* use ML text *)

fun use name = Toplevel.imperative (fn () => ThyInfo.use name);

(*passes changes of theory context*)
val use_mltext_theory = Toplevel.theory o IsarThy.use_mltext_theory;

(*ignore result theory context*)
fun use_mltext txt = Toplevel.keep (fn state =>
  (IsarThy.use_mltext txt (try Toplevel.theory_of state); ()));

(*Note: commit is dynamically bound*)
val use_commit = use_mltext "commit();";


(* current working directory *)

fun print_cd _ = writeln (Path.pack (File.pwd ()));

fun cd dir = Toplevel.imperative (fn () => (File.cd (Path.unpack dir); print_cd ()));
val pwd = Toplevel.imperative print_cd;


(* load theory files *)

fun use_thy name = Toplevel.imperative (fn () => Context.save ThyInfo.use_thy name);
fun update_thy name = Toplevel.imperative (fn () => Context.save ThyInfo.update_thy name);


(* print theory contents *)

val print_theory = Toplevel.keep (PureThy.print_theory o Toplevel.theory_of);
val print_syntax = Toplevel.keep (Display.print_syntax o Toplevel.theory_of);
val print_theorems = Toplevel.keep (PureThy.print_theorems o Toplevel.theory_of);
val print_attributes = Toplevel.keep (Attrib.print_attributes o Toplevel.theory_of);
val print_methods = Toplevel.keep (Method.print_methods o Toplevel.theory_of);


(* print proof context contents *)

val print_binds = Toplevel.keep (ProofContext.print_binds o Proof.context_of o Toplevel.proof_of);
val print_lthms = Toplevel.keep (ProofContext.print_thms o Proof.context_of o Toplevel.proof_of);


(* print theorems *)

fun global_attribs thy ths srcs =
  #2 (Thm.applys_attributes ((Theory.copy thy, ths), map (Attrib.global_attribute thy) srcs));

fun local_attribs st ths srcs =
  #2 (Thm.applys_attributes ((Proof.context_of st, ths),
    map (Attrib.local_attribute (Proof.theory_of st)) srcs));

fun print_thms (name, srcs) = Toplevel.keep (fn state =>
  let
    val ths = map (Thm.transfer (Toplevel.theory_of state))
      (Toplevel.node_cases PureThy.get_thms (ProofContext.get_thms o Proof.context_of)
        state name);
    val ths' = Toplevel.node_cases global_attribs local_attribs state ths srcs;
  in Display.print_thms ths' end);


(* print types, terms and props *)

fun read_typ thy = Sign.read_typ (Theory.sign_of thy, K None);

fun read_term T thy s =
  Thm.term_of (#1 (Thm.read_def_cterm (Theory.sign_of thy, K None, K None) [] true (s, T)));


fun print_type s = Toplevel.keep (fn state =>
  let
    val sign = Toplevel.sign_of state;
    val T = Toplevel.node_cases read_typ (ProofContext.read_typ o Proof.context_of) state s;
  in Pretty.writeln (Pretty.quote (Sign.pretty_typ sign T)) end);

fun print_term s = Toplevel.keep (fn state =>
  let
    val sign = Toplevel.sign_of state;
    val t = Toplevel.node_cases (read_term (TVar (("'z", 0), logicS)))
      (ProofContext.read_term o Proof.context_of) state s;
    val T = Term.type_of t;
  in
    Pretty.writeln (Pretty.block [Pretty.quote (Sign.pretty_term sign t), Pretty.fbrk,
      Pretty.str "::", Pretty.brk 1, Pretty.quote (Sign.pretty_typ sign T)])
  end);

fun print_prop s = Toplevel.keep (fn state =>
  let
    val sign = Toplevel.sign_of state;
    val prop =
      Toplevel.node_cases (read_term propT) (ProofContext.read_prop o Proof.context_of) state s;
  in Pretty.writeln (Pretty.quote (Sign.pretty_term sign prop)) end);


end;
