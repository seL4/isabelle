(*  Title:      Pure/ML-Systems/ml_platform_path_polyml.ML
    Author:     Makarius

Poly/ML support for native Windows (MinGW).
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

structure OS =
struct
  open OS;

  structure FileSys =
  struct
    open FileSys;

    val openDir = openDir o ml_platform_path;

    val chDir = chDir o ml_platform_path;
    val getDir = ml_standard_path o getDir;
    val mkDir = mkDir o ml_platform_path;
    val rmDir = rmDir o ml_platform_path;
    val isDir = isDir o ml_platform_path;
    val isLink = isLink o ml_platform_path;
    val readLink = readLink o ml_platform_path;
    val fullPath = ml_standard_path o fullPath o ml_platform_path;
    val realPath = ml_standard_path o realPath o ml_platform_path;
    val modTime = modTime o ml_platform_path;
    val fileSize = fileSize o ml_platform_path;
    fun setTime (file, time) = FileSys.setTime (ml_platform_path file, time);
    val remove = remove o ml_platform_path;
    fun rename {old, new} = FileSys.rename {old = ml_platform_path old, new = ml_platform_path new};

    fun access (file, modes) = FileSys.access (ml_platform_path file, modes);

    val tmpName = ml_standard_path o tmpName;

    val fileId = fileId o ml_platform_path;
  end;
end;

structure TextIO =
struct
  open TextIO;
  val openIn = openIn o ml_platform_path;
  val openOut = openOut o ml_platform_path;
  val openAppend = openAppend o ml_platform_path;
end;

structure PolyML =
struct
  open PolyML
  structure SaveState =
  struct
    open SaveState;
    val loadState = loadState o ml_platform_path;
    val saveState = saveState o ml_platform_path;
  end;
end;
