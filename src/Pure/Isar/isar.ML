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
  val main: unit -> unit
  val loop: unit -> unit
  val sync_main: unit -> unit
  val sync_loop: unit -> unit
  val secure_main: unit -> unit
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


(* main loop *)

val crashes = ref ([]: exn list);

local

(*Spurious interrupts ahead!  Race condition?*)
fun get_interrupt src = SOME (Source.get_single src) handle Interrupt => NONE;

fun raw_loop secure src =
  let
    fun check_secure () =
      (if secure then warning "Secure loop -- cannot exit to ML" else (); secure);
  in
    (case get_interrupt (Source.set_prompt Source.default_prompt src) of
      NONE => (writeln "\nInterrupt."; raw_loop secure src)
    | SOME NONE => if secure then quit () else ()
    | SOME (SOME (tr, src')) => if >> tr orelse check_secure () then raw_loop secure src' else ())
    handle exn => (Output.error_msg (Toplevel.exn_message exn) handle crash =>
      (CRITICAL (fn () => change crashes (cons crash));
        warning "Recovering after Isar toplevel crash -- see also Isar.crashes");
      raw_loop secure src)
  end;

in

fun gen_loop secure do_terminate =
 (Context.set_thread_data NONE;
  uninterruptible (fn _ => fn () => raw_loop secure (OuterSyntax.isar do_terminate)) ());

fun gen_main secure do_terminate =
 (init ();
  writeln (Session.welcome ());
  gen_loop secure do_terminate);

end;

fun main () = gen_main (Secure.is_secure ()) false;
fun loop () = gen_loop (Secure.is_secure ()) false;
fun sync_main () = gen_main (Secure.is_secure ()) true;
fun sync_loop () = gen_loop (Secure.is_secure ()) true;
fun secure_main () = (init (); gen_loop true true);

end;

