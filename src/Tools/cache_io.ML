(*  Title:      Tools/cache_io.ML
    Author:     Sascha Boehme, TU Muenchen

Cache for output of external processes.
*)

signature CACHE_IO =
sig
  (*IO wrapper*)
  type result = {
    output: string list,
    redirected_output: string list,
    return_code: int}
  val raw_run: (Path.T -> Path.T -> string) -> string -> Path.T -> Path.T -> result
  val run: (Path.T -> Path.T -> string) -> string -> result

  (*cache*)
  type cache
  val unsynchronized_init: Path.T -> cache
  val cache_path_of: cache -> Path.T
  val lookup: cache -> string -> result option * string
  val run_and_cache: cache -> string -> (Path.T -> Path.T -> string) -> string -> result
  val run_cached: cache -> (Path.T -> Path.T -> string) -> string -> result
end

structure Cache_IO : CACHE_IO =
struct

(* IO wrapper *)

val cache_io_prefix = "cache-io-"

type result = {
  output: string list,
  redirected_output: string list,
  return_code: int}

fun try_read_lines path =
  let
    fun loop n =
      (case try File.read_lines path of
        SOME lines => lines
      | NONE => if n > 0 then (OS.Process.sleep (seconds 0.05); loop (n - 1)) else [])
  in if File.exists path then loop (if ML_System.platform_is_windows then 20 else 0) else [] end

fun raw_run make_cmd str in_path out_path =
  let
    val _ = File.write in_path str
    val (out2, rc) = Isabelle_System.bash_output (make_cmd in_path out_path)
    val out1 = try_read_lines out_path
  in {output = split_lines out2, redirected_output = out1, return_code = rc} end

fun run make_cmd str =
  Isabelle_System.with_tmp_file cache_io_prefix "" (fn in_path =>
    Isabelle_System.with_tmp_file cache_io_prefix "" (fn out_path =>
      raw_run make_cmd str in_path out_path))


(* cache *)

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
          in ((SOME {output = err, redirected_output = out, return_code = 0}, key), tab) end))
  end

fun run_and_cache (Cache {path = cache_path, table}) key make_cmd str =
  let
    val {output = err, redirected_output=out, return_code} = run make_cmd str
    val (l1, l2) = apply2 length (out, err)
    val header = key ^ " " ^ string_of_int l1 ^ " " ^ string_of_int l2
    val lines = map (suffix "\n") (header :: out @ err)

    val _ = Synchronized.change table (fn (p, tab) =>
      if Symtab.defined tab key then (p, tab)
      else
        let val _ = File.append_list cache_path lines
        in (p+l1+l2+1, Symtab.update (key, (p+1, l1, l2)) tab) end)
  in {output = err, redirected_output = out, return_code = return_code} end

fun run_cached cache make_cmd str =
  (case lookup cache str of
    (NONE, key) => run_and_cache cache key make_cmd str
  | (SOME output, _) => output)

end

end
