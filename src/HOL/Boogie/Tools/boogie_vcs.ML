(*  Title:      HOL/Boogie/Tools/boogie_vcs.ML
    Author:     Sascha Boehme, TU Muenchen

Store for Boogie's verification conditions.
*)

signature BOOGIE_VCS =
sig
  val set: (string * term) list -> theory -> theory
  val lookup: theory -> string -> term option
  val discharge: string * thm -> theory -> theory
  val close: theory -> theory
  val is_closed: theory -> bool
  val as_list: theory -> (string * term * bool) list
end

structure Boogie_VCs: BOOGIE_VCS =
struct

fun err_vcs () = error "undischarged Boogie verification conditions found"

structure VCs = Theory_Data
(
  type T = (term * bool) Symtab.table option
  val empty = NONE
  val extend = I
  fun merge (NONE, NONE) = NONE
    | merge _ = err_vcs ()
)

fun set vcs = VCs.map (fn
    NONE => SOME (Symtab.make (map (apsnd (rpair false)) vcs))
  | SOME _ => err_vcs ())

fun lookup thy name = 
  (case VCs.get thy of
    SOME vcs => Option.map fst (Symtab.lookup vcs name)
  | NONE => NONE)

fun discharge (name, thm) thy = VCs.map (fn
    SOME vcs => SOME (Symtab.map_entry name (fn (t, proved) =>
      if proved then (t, proved)
      else (t, Pattern.matches thy (Thm.prop_of thm, t))) vcs)
  | NONE => NONE) thy

val close = VCs.map (fn
    SOME vcs =>
      if Symtab.exists (fn (_, (_, proved)) => not proved) vcs then err_vcs ()
      else NONE
  | NONE => NONE)

val is_closed = is_none o VCs.get

fun as_list thy =
  (case VCs.get thy of
    SOME vcs => map (fn (n, (t, p)) => (n, t, p)) (Symtab.dest vcs)
  | NONE => [])

end
