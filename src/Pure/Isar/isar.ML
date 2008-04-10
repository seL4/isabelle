(*  Title:      Pure/Isar/isar.ML
    ID:         $Id$
    Author:     Makarius

The global Isabelle/Isar state and main read-eval-print loop.
*)

signature ISAR =
sig
  val state: unit -> Toplevel.state
  val exn: unit -> (exn * string) option
  val context: unit -> Proof.context
  val goal: unit -> thm
  val >> : Toplevel.transition -> bool
  val >>> : Toplevel.transition list -> unit
  val init: unit -> unit
  val crashes: exn list ref
  val toplevel_loop: {init: bool, sync: bool, secure: bool} -> unit
  val loop: unit -> unit
  val main: unit -> unit
end;

structure Isar: ISAR =
struct

(* the global state *)

val global_state = ref (Toplevel.toplevel, NONE: (exn * string) option);

fun state () = #1 (! global_state);
fun exn () = #2 (! global_state);

fun context () =
  Toplevel.context_of (state ())
    handle Toplevel.UNDEF => error "Unknown context";

fun goal () =
  #2 (#2 (Proof.get_goal (Toplevel.proof_of (state ()))))
    handle Toplevel.UNDEF => error "No goal present";


(* interactive state transformations --- NOT THREAD-SAFE! *)

nonfix >> >>>;

fun >> tr =
  (case Toplevel.transition true tr (state ()) of
    NONE => false
  | SOME (state', exn_info) =>
      (global_state := (state', exn_info);
        (case exn_info of
          NONE => ()
        | SOME err => Toplevel.error_msg tr err);
        true));

fun >>> [] = ()
  | >>> (tr :: trs) = if >> tr then >>> trs else ();

fun init () = (>> (Toplevel.init_empty (K true) (K ()) Toplevel.empty); ());


(* toplevel loop *)

val crashes = ref ([]: exn list);

local

fun raw_loop secure src =
  let
    fun check_secure () =
      (if secure then warning "Secure loop -- cannot exit to ML" else (); secure);
  in
    (case Source.get_single (Source.set_prompt Source.default_prompt src) of
      NONE => if secure then quit () else ()
    | SOME (tr, src') => if >> tr orelse check_secure () then raw_loop secure src' else ())
    handle exn => (Output.error_msg (Toplevel.exn_message exn) handle crash =>
      (CRITICAL (fn () => change crashes (cons crash));
        warning "Recovering after Isar toplevel crash -- see also Isar.crashes");
      raw_loop secure src)
  end;

in

fun toplevel_loop {init = do_init, sync, secure} =
 (Context.set_thread_data NONE;
  if do_init then (init (); writeln (Session.welcome ())) else ();
  uninterruptible (fn _ => fn () => raw_loop secure (OuterSyntax.isar sync)) ());

end;

fun loop () = toplevel_loop {init = false, sync = false, secure = Secure.is_secure ()};
fun main () = toplevel_loop {init = true, sync = false, secure = Secure.is_secure ()};

end;

