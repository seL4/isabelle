(*  Title:      Pure/ML-Systems/windows_polyml.ML
    Author:     Makarius

Poly/ML support for native Windows (MinGW).
*)

structure OS =
struct
  fun windows path =
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

  fun cygwin path =
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

  open OS;

  structure FileSys =
  struct
    open FileSys;

    val openDir = openDir o windows;

    val chDir = chDir o windows;
    val getDir = cygwin o getDir;
    val mkDir = mkDir o windows;
    val rmDir = rmDir o windows;
    val isDir = isDir o windows;
    val isLink = isLink o windows;
    val readLink = readLink o windows;
    val fullPath = cygwin o fullPath o windows;
    val realPath = cygwin o realPath o windows;
    val modTime = modTime o windows;
    val fileSize = fileSize o windows;
    fun setTime (file, time) = FileSys.setTime (windows file, time);
    val remove = remove o windows;
    fun rename {old, new} = FileSys.rename {old = windows old, new = windows new};

    fun access (file, modes) = FileSys.access (windows file, modes);

    val tmpName = cygwin o tmpName;

    val fileId = fileId o windows;
  end;
end;

structure TextIO =
struct
  open TextIO;
  val openIn = openIn o OS.windows;
  val openOut = openOut o OS.windows;
  val openAppend = openAppend o OS.windows;
end;

structure PolyML =
struct
  open PolyML
  structure SaveState =
  struct
    open SaveState;
    val loadState = loadState o OS.windows;
    val saveState = saveState o OS.windows;
  end;
end;

val ml_platform_path = OS.windows;
