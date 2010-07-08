(*  Title:      Tools/cache_io.ML
    Author:     Sascha Boehme, TU Muenchen

Cache for output of external processes.
*)

signature CACHE_IO =
sig
  val with_tmp_file: string -> (Path.T -> 'a) -> 'a
  val with_tmp_dir: string -> (Path.T -> 'a) -> 'a
  val run: (Path.T -> Path.T -> string) -> string -> string list * string list

  type cache
  val make: Path.T -> cache
  val cache_path_of: cache -> Path.T
  val lookup: cache -> string -> (string list * string list) option * string
  val run_and_cache: cache -> string -> (Path.T -> Path.T -> string) ->
    string -> string list * string list
  val run_cached: cache -> (Path.T -> Path.T -> string) -> string ->
    string list * string list
end

structure Cache_IO : CACHE_IO =
struct

val cache_io_prefix = "cache-io-"

fun with_tmp_file name f =
  let
    val path = File.tmp_path (Path.explode (name ^ serial_string ()))
    val x = Exn.capture f path
    val _ = try File.rm path
  in Exn.release x end

fun with_tmp_dir name f =
  let
    val path = File.tmp_path (Path.explode (name ^ serial_string ()))
    val _ = File.mkdir path
    val x = Exn.capture f path
    val _ = try File.rm_tree path
  in Exn.release x end

fun run make_cmd str =
  with_tmp_file cache_io_prefix (fn in_path =>
  with_tmp_file cache_io_prefix (fn out_path =>
    let
      val _ = File.write in_path str
      val (out2, _) = bash_output (make_cmd in_path out_path)
      val out1 = the_default [] (try (rev o File.fold_lines cons out_path) [])
    in (out1, split_lines out2) end))



abstype cache = Cache of {
  path: Path.T,
  table: (int * (int * int * int) Symtab.table) Synchronized.var }
with


fun cache_path_of (Cache {path, ...}) = path


fun load cache_path =
  let
    fun err () = error ("Cache IO: corrupted cache file: " ^
      File.shell_path cache_path)

    fun int_of_string s =
      (case read_int (explode s) of
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
  in apfst fst (File.fold_lines parse cache_path ((1, 1), Symtab.empty)) end 

fun make path =
  let val table = if File.exists path then load path else (1, Symtab.empty)
  in Cache {path=path, table=Synchronized.var (Path.implode path) table} end


fun load_cached_result cache_path (p, len1, len2) =
  let
    fun load line (i, xsp) =
      if i < p then (i+1, xsp)
      else if i < p + len1 then (i+1, apfst (cons line) xsp)
      else if i < p + len2 then (i+1, apsnd (cons line) xsp)
      else (i, xsp)
  in pairself rev (snd (File.fold_lines load cache_path (1, ([], [])))) end


fun lookup (Cache {path=cache_path, table}) str =
  let val key = SHA1.digest str
  in
    (case Symtab.lookup (snd (Synchronized.value table)) key of
      NONE => (NONE, key)
    | SOME pos => (SOME (load_cached_result cache_path pos), key))
  end


fun run_and_cache (Cache {path=cache_path, table}) key make_cmd str =
  let
    val res as (out, err) = run make_cmd str
    val (l1, l2) = pairself length res
    val header = key ^ " " ^ string_of_int l1 ^ " " ^ string_of_int l2
    val lines = map (suffix "\n") (header :: out @ err)

    val _ = Synchronized.change table (fn (p, tab) =>
      if Symtab.defined tab key then (p, tab)
      else
        let val _ = File.append_list cache_path lines
        in (p+l1+l2+1, Symtab.update (key, (p+1, l1, l2)) tab) end)
  in res end


fun run_cached cache make_cmd str =
  (case lookup cache str of
    (NONE, key) => run_and_cache cache key make_cmd str
  | (SOME output, _) => output)

end
end
