(*  Title:      Pure/ML-Systems/windows_path.ML
    Author:     Makarius

Windows file-system paths.
*)

fun ml_platform_path path =
  if String.isPrefix "/" path andalso not (String.isPrefix "//" path) then
    (case String.tokens (fn c => c = #"/") path of
      "cygdrive" :: drive :: arcs =>
        let
          val vol =
            (case Char.fromString drive of
              NONE => drive ^ ":"
            | SOME d => String.str (Char.toUpper d) ^ ":");
        in OS.Path.toString {vol = vol, arcs = arcs, isAbs = true} end
    | arcs =>
        (case OS.Process.getEnv "CYGWIN_ROOT" of
          SOME root =>
            OS.Path.concat (root, OS.Path.toString {vol = "", arcs = arcs, isAbs = false})
        | NONE => raise Fail "Unknown environment variable CYGWIN_ROOT"))
  else String.translate (fn #"/" => "\\" | c => String.str c) path;

fun ml_standard_path path =
  let
    val {vol, arcs, isAbs} = OS.Path.fromString path;
    val path' = String.translate (fn #"\\" => "/" | c => String.str c) path;
  in
    if isAbs then
      (case String.explode vol of
        [d, #":"] =>
          String.concatWith "/" ("/cygdrive" :: String.str (Char.toLower d) :: arcs)
      | _ => path')
    else path'
  end;
