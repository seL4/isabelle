(*  Title:      Tools/Cache_IO/cache_io.ML
    Author:     Sascha Boehme, TU Muenchen

Cache for output of external processes.
*)

signature CACHE_IO =
sig
  val with_tmp_file: string -> (Path.T -> 'a) -> 'a
  val run: (Path.T -> string) -> Path.T -> string list
  val run': (Path.T -> Path.T -> string) -> Path.T -> string list * string list

  type cache
  val make: Path.T -> cache
  val cache_path_of: cache -> Path.T
  val cached: cache -> (Path.T -> string) -> Path.T -> string list
  val cached': cache -> (Path.T -> Path.T -> string) -> Path.T ->
    string list * string list
end

structure Cache_IO : CACHE_IO =
struct

fun with_tmp_file name f =
  let
    val path = File.tmp_path (Path.explode (name ^ serial_string ()))
    val x = Exn.capture f path
    val _ = try File.rm path
  in Exn.release x end

fun run' make_cmd in_path =
  with_tmp_file "cache-io-" (fn out_path =>
    let
      val (out2, _) = bash_output (make_cmd in_path out_path)
      val out1 = the_default [] (try (rev o File.fold_lines cons out_path) [])
    in (out1, split_lines out2) end)

fun run make_cmd = snd o run' (fn in_path => fn _ => make_cmd in_path)



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


fun get_hash_key path =
  let
    val arg = File.shell_path path
    val (out, res) = bash_output (getenv "COMPUTE_HASH_KEY" ^ " " ^ arg)
  in
    if res = 0 then hd (split_lines out)
    else error ("Cache IO: failed to generate hash key for file " ^ arg)
  end

fun load_cached_result cache_path (p, len1, len2) =
  let
    fun load line (i, xsp) =
      if i < p then (i+1, xsp)
      else if i < p + len1 then (i+1, apfst (cons line) xsp)
      else if i < p + len2 then (i+1, apsnd (cons line) xsp)
      else (i, xsp)
  in pairself rev (snd (File.fold_lines load cache_path (1, ([], [])))) end

fun cached' (Cache {path=cache_path, table}) make_cmd in_path =
  let val key = get_hash_key in_path
  in
    (case Symtab.lookup (snd (Synchronized.value table)) key of
      SOME pos => load_cached_result cache_path pos
    | NONE =>
        let
          val res as (out, err) = run' make_cmd in_path
          val (l1, l2) = pairself length res
          val header = key ^ " " ^ string_of_int l1 ^ " " ^ string_of_int l2
          val lines = map (suffix "\n") (header :: out @ err)

          val _ = Synchronized.change table (fn (p, tab) =>
            if Symtab.defined tab key then (p, tab)
            else
              let val _ = File.append_list cache_path lines
              in (p+l1+l2+1, Symtab.update (key, (p+1, l1, l2)) tab) end)
        in res end)
  end

fun cached cache make_cmd =
  snd o cached' cache (fn in_path => fn _ => make_cmd in_path)

end
end
