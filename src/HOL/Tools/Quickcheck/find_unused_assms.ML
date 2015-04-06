(*  Title:      HOL/Tools/Quickcheck/find_unused_assms.ML
    Author:     Lukas Bulwahn, TU Muenchen

Finding unused assumptions in lemmas (using Quickcheck).
*)

signature FIND_UNUSED_ASSMS =
sig
  val find_unused_assms : Proof.context -> string -> (string * int list list option) list
  val print_unused_assms : Proof.context -> string option -> unit
end

structure Find_Unused_Assms : FIND_UNUSED_ASSMS =
struct

fun thms_of thy thy_name = Global_Theory.all_thms_of thy false
  |> filter (fn (_, th) => Context.theory_name (Thm.theory_of_thm th) = thy_name)

fun do_while P f s list =
  if P s then
    let val s' = f s
    in do_while P f s' (cons s' list) end
  else list

fun drop_indexes is xs =
  fold_index (fn (i, x) => if member (op =) is i then I else cons x) xs []

fun find_max_subsets [] = []
  | find_max_subsets (ss :: sss) = ss ::
      (find_max_subsets (map (filter_out (fn s => exists (fn s' => subset (op =) (s, s')) ss)) sss))


(* main functionality *)

fun find_unused_assms ctxt thy_name =
  let
    val ctxt' = ctxt
       |> Config.put Quickcheck.abort_potential true
       |> Config.put Quickcheck.quiet true
    val all_thms =
      filter (fn (s, _) => length (Long_Name.explode s) = 2)  (* FIXME !? *)
        (thms_of (Proof_Context.theory_of ctxt) thy_name)
    fun check_single conjecture =
      (case try (Quickcheck.test_terms ctxt' (true, true) []) [(conjecture, [])] of
        SOME (SOME _) => false
      | SOME NONE => true
      | NONE => false)
    fun build X Ss =
      fold
        (fn S => fold
          (fn x =>
            if member (op =) S x then I
            else insert (eq_set (op =)) (insert (op =) x S)) X) Ss []
    fun check (s, th) =
      (case Logic.strip_horn (Thm.prop_of (Thm.unvarify_global th)) of
        ([], _) => (s, NONE)
      | (ts, t) =>
          let
            fun mk_conjecture is = Logic.list_implies (drop_indexes is ts, t)
            val singles = filter (check_single o mk_conjecture o single) (0 upto (length ts - 1))
            val multiples =
              do_while (not o null)
                (fn I => filter (check_single o mk_conjecture) (build singles I))
                (map single singles) [(map single singles)]
            val maximals = flat (find_max_subsets multiples)
          in
            (s, SOME maximals)
          end)
  in
    rev (Par_List.map check all_thms)
  end


(* printing results *)

local

fun pretty_indexes is =
  Pretty.block
    (flat (separate [Pretty.str " and", Pretty.brk 1]
      (map (fn i => [Pretty.str (string_of_int (i + 1))]) (sort int_ord is))))

fun pretty_thm (s, set_of_indexes) =
  Pretty.block (Pretty.str s :: Pretty.str ":" :: Pretty.brk 1 ::
    Pretty.str "unnecessary assumption(s) " ::
    separate (Pretty.str " or ") (map pretty_indexes set_of_indexes))

in

fun print_unused_assms ctxt opt_thy_name =
  let
    val thy_name = the_default (Context.theory_name (Proof_Context.theory_of ctxt)) opt_thy_name
    val results = find_unused_assms ctxt thy_name
    val total = length results
    val with_assumptions = length (filter (is_some o snd) results)
    val with_superfluous_assumptions =
      map_filter (fn (_, NONE) => NONE | (_, SOME []) => NONE | (s, SOME r) => SOME (s, r)) results

    val msg =
      "Found " ^ string_of_int (length with_superfluous_assumptions) ^
      " theorems with (potentially) superfluous assumptions"
    val end_msg =
      "Checked " ^ string_of_int with_assumptions ^ " theorems with assumptions (" ^
      string_of_int total ^ " total) in the theory " ^ quote thy_name
  in
    [Pretty.str (msg ^ ":"), Pretty.str ""] @
    map pretty_thm with_superfluous_assumptions @
    [Pretty.str "", Pretty.str end_msg]
  end |> Pretty.writeln_chunks

end

val _ =
  Outer_Syntax.command @{command_keyword find_unused_assms}
    "find theorems with (potentially) superfluous assumptions"
    (Scan.option Parse.name >> (fn name =>
      Toplevel.keep (fn state => print_unused_assms (Toplevel.context_of state) name)))

end
