(*  Title:      Tools/cache_io.ML
    Author:     Sascha Boehme, TU Muenchen

Cache for output of external processes.
*)

signature CACHE_IO =
sig
  type cache
  val unsynchronized_init: Path.T -> cache
  val cache_path_of: cache -> Path.T
  val lookup: cache -> string -> Process_Result.T option * string
  val run: Bash.params -> string -> Process_Result.T
  val run_and_cache: cache -> string -> Bash.params -> string -> Process_Result.T
  val run_cached: cache -> Bash.params -> string -> Process_Result.T
end

structure Cache_IO : CACHE_IO =
struct

abstype cache = Cache of {
  path: Path.T,
  table: (int * (int * int * int) Symtab.table) Synchronized.var }
with

fun cache_path_of (Cache {path, ...}) = path

fun unsynchronized_init cache_path =
  let
    val table =
      if File.exists cache_path then
        let
          fun err () = error ("Cache IO: corrupted cache file: " ^ Path.print cache_path)

          fun int_of_string s =
            (case read_int (raw_explode s) of
              (i, []) => i
            | _ => err ())

          fun split line =
            (case space_explode " " line of
              [key, len1, len2] => (key, int_of_string len1, int_of_string len2)
            | _ => err ())

          fun parse line ((i, l), tab) =
            if i = l
            then
              let val (key, l1, l2) = split line
              in ((i+1, l+l1+l2+1), Symtab.update (key, (i+1, l1, l2)) tab) end
            else ((i+1, l), tab)
        in apfst fst (fold parse (File.read_lines cache_path) ((1, 1), Symtab.empty)) end
      else (1, Symtab.empty)
  in Cache {path = cache_path, table = Synchronized.var "Cache_IO" table} end

fun lookup (Cache {path = cache_path, table}) str =
  let val key = SHA1.rep (SHA1.digest str)
  in
    Synchronized.change_result table (fn tab =>
      (case Symtab.lookup (snd tab) key of
        NONE => ((NONE, key), tab)
      | SOME (p, len1, len2) =>
          let
            fun load line (i, xsp) =
              if i < p then (i+1, xsp)
              else if i < p + len1 then (i+1, apfst (cons line) xsp)
              else if i < p + len2 then (i+1, apsnd (cons line) xsp)
              else (i, xsp)
            val (out, err) =
              apply2 rev (snd (fold load (File.read_lines cache_path) (1, ([], []))))
            val result =
              Process_Result.make {rc = 0, out_lines = out, err_lines = err, timing = Timing.zero}
          in ((SOME result, key), tab) end))
  end

fun run cmd input =
  let
    val result = cmd
      |> Bash.input (Bytes.string input)
      |> Bash.redirect
      |> Isabelle_System.bash_process
    val rc = Process_Result.rc result
  in
    if rc = Process_Result.startup_failure_rc then
      Process_Result.make
       {rc = rc,
        err_lines = Process_Result.out_lines result,
        out_lines = [],
        timing = Process_Result.timing result}
    else result
  end

fun run_and_cache (Cache {path = cache_path, table}) key cmd input =
  let
    val result = run cmd input
    val out_lines = Process_Result.out_lines result
    val err_lines = Process_Result.err_lines result
    val (l1, l2) = apply2 length (out_lines, err_lines)
    val header = key ^ " " ^ string_of_int l1 ^ " " ^ string_of_int l2
    val lines = map (suffix "\n") (header :: out_lines @ err_lines)

    val _ = Synchronized.change table (fn (p, tab) =>
      if Symtab.defined tab key then (p, tab)
      else
        let val _ = File.append_list cache_path lines
        in (p+l1+l2+1, Symtab.update (key, (p+1, l1, l2)) tab) end)
  in result end

fun run_cached cache cmd input =
  (case lookup cache input of
    (NONE, key) => run_and_cache cache key cmd input
  | (SOME output, _) => output)

end

end
