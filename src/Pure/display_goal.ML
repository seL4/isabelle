(*  Title:      Pure/display_goal.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Makarius

Display tactical goal state.
*)

signature DISPLAY_GOAL =
sig
  val goals_limit: int ref
  val show_consts: bool ref
  val pretty_flexpair: Pretty.pp -> term * term -> Pretty.T
  val pretty_goals_aux: Pretty.pp -> Markup.T -> bool * bool -> int -> thm -> Pretty.T list
  val pretty_goals: int -> thm -> Pretty.T list
  val print_goals: int -> thm -> unit
end;

structure Display_Goal: DISPLAY_GOAL =
struct

val goals_limit = ref 10;      (*max number of goals to print*)
val show_consts = ref false;   (*true: show consts with types in proof state output*)

fun pretty_flexpair pp (t, u) = Pretty.block
  [Pretty.term pp t, Pretty.str " =?=", Pretty.brk 1, Pretty.term pp u];


(*print thm A1,...,An/B in "goal style" -- premises as numbered subgoals*)

local

fun ins_entry (x, y) =
  AList.default (op =) (x, []) #>
  AList.map_entry (op =) x (insert (op =) y);

val add_consts = Term.fold_aterms
  (fn Const (c, T) => ins_entry (T, (c, T))
    | _ => I);

val add_vars = Term.fold_aterms
  (fn Free (x, T) => ins_entry (T, (x, ~1))
    | Var (xi, T) => ins_entry (T, xi)
    | _ => I);

val add_varsT = Term.fold_atyps
  (fn TFree (x, S) => ins_entry (S, (x, ~1))
    | TVar (xi, S) => ins_entry (S, xi)
    | _ => I);

fun sort_idxs vs = map (apsnd (sort (prod_ord string_ord int_ord))) vs;
fun sort_cnsts cs = map (apsnd (sort_wrt fst)) cs;

fun consts_of t = sort_cnsts (add_consts t []);
fun vars_of t = sort_idxs (add_vars t []);
fun varsT_of t = rev (sort_idxs (Term.fold_types add_varsT t []));

in

fun pretty_goals_aux pp markup (msg, main) maxgoals state =
  let
    fun prt_atoms prt prtT (X, xs) = Pretty.block
      [Pretty.block (Pretty.commas (map prt xs)), Pretty.str " ::",
        Pretty.brk 1, prtT X];

    fun prt_var (x, ~1) = Pretty.term pp (Syntax.free x)
      | prt_var xi = Pretty.term pp (Syntax.var xi);

    fun prt_varT (x, ~1) = Pretty.typ pp (TFree (x, []))
      | prt_varT xi = Pretty.typ pp (TVar (xi, []));

    val prt_consts = prt_atoms (Pretty.term pp o Const) (Pretty.typ pp);
    val prt_vars = prt_atoms prt_var (Pretty.typ pp);
    val prt_varsT = prt_atoms prt_varT (Pretty.sort pp);


    fun pretty_list _ _ [] = []
      | pretty_list name prt lst = [Pretty.big_list name (map prt lst)];

    fun pretty_subgoal (n, A) = Pretty.markup markup
      [Pretty.str (" " ^ string_of_int n ^ ". "), Pretty.term pp A];
    fun pretty_subgoals As = map pretty_subgoal (1 upto length As ~~ As);

    val pretty_ffpairs = pretty_list "flex-flex pairs:" (pretty_flexpair pp);

    val pretty_consts = pretty_list "constants:" prt_consts o consts_of;
    val pretty_vars = pretty_list "variables:" prt_vars o vars_of;
    val pretty_varsT = pretty_list "type variables:" prt_varsT o varsT_of;


    val {prop, tpairs, ...} = Thm.rep_thm state;
    val (As, B) = Logic.strip_horn prop;
    val ngoals = length As;

    fun pretty_gs (types, sorts) =
      (if main then [Pretty.term pp B] else []) @
       (if ngoals = 0 then [Pretty.str "No subgoals!"]
        else if ngoals > maxgoals then
          pretty_subgoals (Library.take (maxgoals, As)) @
          (if msg then [Pretty.str ("A total of " ^ string_of_int ngoals ^ " subgoals...")]
           else [])
        else pretty_subgoals As) @
      pretty_ffpairs tpairs @
      (if ! show_consts then pretty_consts prop else []) @
      (if types then pretty_vars prop else []) @
      (if sorts then pretty_varsT prop else []);
  in
    setmp show_no_free_types true
      (setmp show_types (! show_types orelse ! show_sorts orelse ! show_all_types)
        (setmp show_sorts false pretty_gs))
   (! show_types orelse ! show_sorts orelse ! show_all_types, ! show_sorts)
  end;

fun pretty_goals n th =
  pretty_goals_aux (Syntax.pp_global (Thm.theory_of_thm th)) Markup.none (true, true) n th;

val print_goals = (Pretty.writeln o Pretty.chunks) oo pretty_goals;

end;

end;

