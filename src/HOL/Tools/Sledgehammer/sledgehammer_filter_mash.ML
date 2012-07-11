(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_filter_mash.ML
    Author:     Jasmin Blanchette, TU Muenchen

Sledgehammer's machine-learning-based relevance filter (MaSh).
*)

signature SLEDGEHAMMER_FILTER_MASH =
sig
  val reset : unit -> unit
  val can_suggest : unit -> bool
  val can_learn_thy : theory -> bool
  val learn_thy : theory -> real -> unit
  val learn_proof : theory -> term -> thm list -> unit
end;

structure Sledgehammer_Filter_MaSh : SLEDGEHAMMER_FILTER_MASH =
struct

fun mash_reset () =
  tracing "MaSh RESET"

fun mash_add fact (access, feats, deps) =
  tracing ("MaSh ADD " ^ fact ^ ": " ^ space_implode " " access ^ "; " ^
           space_implode " " feats ^ "; " ^ space_implode " " deps)

fun mash_del fact =
  tracing ("MaSh DEL " ^ fact)

fun mash_suggest fact (access, feats) =
  tracing ("MaSh SUGGEST " ^ fact ^ ": " ^ space_implode " " access ^ "; " ^
           space_implode " " feats)

fun reset () =
  ()

fun can_suggest () =
  true

fun can_learn_thy thy =
  true

fun learn_thy thy timeout =
  ()

fun learn_proof theory t thms =
  ()

end;
