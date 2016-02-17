(*  Title:      Pure/RAW/ml_system.ML
    Author:     Makarius

ML system and platform operations.
*)

signature ML_SYSTEM =
sig
  val name: string
  val platform: string
  val platform_is_windows: bool
  val share_common_data: unit -> unit
  val save_state: string -> unit
end;

structure ML_System: ML_SYSTEM =
struct

val SOME name = OS.Process.getEnv "ML_SYSTEM";

val SOME platform = OS.Process.getEnv "ML_PLATFORM";
val platform_is_windows = String.isSuffix "windows" platform;

fun share_common_data () = ();
fun save_state _ = raise Fail "Cannot save state -- undefined operation";

end;

