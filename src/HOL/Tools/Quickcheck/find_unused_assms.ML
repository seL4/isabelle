(*  Title:      HOL/Tools/Quickcheck/find_unused_assms.ML
    Author:     Lukas Bulwahn, TU Muenchen

Finding unused assumptions in lemmas (using Quickcheck)
*)

signature FIND_UNUSED_ASSMS =
sig
  val find_unused_assms : Proof.context -> string -> (string * int list list option) list
  val print_unused_assms : Proof.context -> string option -> unit
end;

structure Find_Unused_Assms : FIND_UNUSED_ASSMS =
struct

fun all_unconcealed_thms_of thy =
  let
    val facts = Global_Theory.facts_of thy
  in
    Facts.fold_static
      (fn (s, ths) =>
        if Facts.is_concealed facts s then I else append (map (`(Thm.get_name_hint)) ths))
      facts []
  end;

fun thms_of thy thy_name = all_unconcealed_thms_of thy
  |> filter (fn (_, th) => Context.theory_name (theory_of_thm th) = thy_name);

fun do_while P f s = if P s then (let val s' = f s in (do_while P f s') o (cons s') end) else I

fun drop_indexes is xs = fold_index (fn (i, x) => if member (op =) is i then I else cons x) xs []

fun find_max_subsets [] = []
  | find_max_subsets (ss :: sss) = ss ::
      (find_max_subsets (map (filter_out (fn s => exists (fn s' => subset (op =) (s, s')) ss)) sss))

(* main functionality *)

fun find_unused_assms ctxt thy_name =
  let
    val ctxt' = ctxt
       |> Config.put Quickcheck.abort_potential true
       |> Config.put Quickcheck.quiet true
    val all_thms = filter (fn (s, _) => length (Long_Name.explode s) = 2)  (* FIXME !? *)
      (thms_of (Proof_Context.theory_of ctxt) thy_name)
    fun check_single conjecture =
      case try (Quickcheck.test_terms ctxt' (true, true) []) [(conjecture, [])] of
         SOME (SOME _) => false
       | SOME NONE => true
       | NONE => false
    fun build X Ss =
      fold (fn S => fold
        (fn x => if member (op =) S x then I
          else insert (eq_set (op =)) (insert (op =) x S)) X) Ss []
    fun check (s, th) =
      case Logic.strip_horn (prop_of (Thm.unvarify_global th)) of
        ([], _) => cons (s, NONE)
      | (ts, t) =>
        let
          fun mk_conjecture is = (Logic.list_implies (drop_indexes is ts, t))
          val singles = filter (check_single o mk_conjecture o single) (map_index fst ts) 
          val multiples = do_while (not o null)
            (fn I => filter (check_single o mk_conjecture) (build singles I))
            (map single singles) [(map single singles)]
          val maximals = flat (find_max_subsets multiples)
        in
          cons (s, SOME maximals)
        end
  in
    fold check all_thms []
  end

(* printing results *)

fun pretty_indexes is =
  Pretty.block (separate (Pretty.str " and ")
      (map (fn x => Pretty.str (string_of_int (x + 1))) (sort int_ord is))
     @ [Pretty.brk 1])
  
fun pretty_thm (s, SOME set_of_indexes) =
  Pretty.block (Pretty.str s :: Pretty.str ":" :: Pretty.brk 1 ::
    Pretty.str "unnecessary assumption(s) " ::
    separate (Pretty.str ", or ") (map pretty_indexes set_of_indexes))

fun print_unused_assms ctxt opt_thy_name =
  let
    val start = Timing.start ()
    val thy_name = the_default (Context.theory_name (Proof_Context.theory_of ctxt)) opt_thy_name
    val results = find_unused_assms ctxt thy_name
    val total = length results
    val with_assumptions = length (filter (is_some o snd) results)
    val with_superfluous_assumptions = filter_out (fn (_, r) => r = SOME [])
      (filter (is_some o snd) results)

    val msg = "Found " ^ string_of_int (length with_superfluous_assumptions)
      ^ " theorem(s) with (potentially) superfluous assumptions"      
    val end_msg = "Checked " ^ string_of_int with_assumptions ^ " theorem(s) with assumptions"
      ^ " in the theory " ^ quote thy_name
      ^ " with a total of " ^ string_of_int total ^ " theorem(s)"  
      ^ " in " ^ Time.toString (#cpu (Timing.result start)) ^ " secs";
  in
    ([Pretty.str (msg ^ ":"), Pretty.str ""] @
        map pretty_thm with_superfluous_assumptions
    @ [Pretty.str "", Pretty.str end_msg])
  end |> Pretty.chunks |> Pretty.writeln;


val _ =
  Outer_Syntax.improper_command "find_unused_assms" "find theorems with superfluous assumptions"
    Keyword.diag
    (Scan.option Parse.name
      >> (fn opt_thy_name =>
        Toplevel.no_timing o Toplevel.keep (fn state =>
          print_unused_assms (Toplevel.context_of state) opt_thy_name)));

end;
