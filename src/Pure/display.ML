(*  Title:      Pure/display.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Printing of theories, theorems, etc.
*)

signature BASIC_DISPLAY =
sig
  val goals_limit: int ref
  val show_hyps: bool ref
  val show_tags: bool ref
  val string_of_thm: thm -> string
  val print_thm: thm -> unit
  val print_thms: thm list -> unit
  val prth: thm -> thm
  val prthq: thm Seq.seq -> thm Seq.seq
  val prths: thm list -> thm list
  val string_of_ctyp: ctyp -> string
  val print_ctyp: ctyp -> unit
  val string_of_cterm: cterm -> string
  val print_cterm: cterm -> unit
  val print_syntax: theory -> unit
  val show_consts: bool ref
end;

signature DISPLAY =
sig
  include BASIC_DISPLAY
  val pretty_thm_aux: (sort -> Pretty.T) * (term -> Pretty.T) -> bool -> thm -> Pretty.T
  val pretty_thm_no_quote: thm -> Pretty.T
  val pretty_thm: thm -> Pretty.T
  val pretty_thms: thm list -> Pretty.T
  val pretty_thm_sg: Sign.sg -> thm -> Pretty.T
  val pretty_thms_sg: Sign.sg -> thm list -> Pretty.T
  val pprint_thm: thm -> pprint_args -> unit
  val pretty_ctyp: ctyp -> Pretty.T
  val pprint_ctyp: ctyp -> pprint_args -> unit
  val pretty_cterm: cterm -> Pretty.T
  val pprint_cterm: cterm -> pprint_args -> unit
  val pretty_theory: theory -> Pretty.T
  val pprint_theory: theory -> pprint_args -> unit
  val pretty_full_theory: theory -> Pretty.T list
  val pretty_name_space: string * NameSpace.T -> Pretty.T
  val pretty_goals_aux: (sort -> Pretty.T) * (typ -> Pretty.T) * (term -> Pretty.T)
    -> string -> bool * bool -> int -> thm -> Pretty.T list
  val pretty_goals: int -> thm -> Pretty.T list
  val print_goals: int -> thm -> unit
  val current_goals_markers: (string * string * string) ref
  val pretty_current_goals: int -> int -> thm -> Pretty.T list
  val print_current_goals_default: int -> int -> thm -> unit
  val print_current_goals_fn: (int -> int -> thm -> unit) ref
end;

structure Display: DISPLAY =
struct


(** print thm **)

val goals_limit = ref 10;       (*max number of goals to print -- set by user*)
val show_hyps = ref false;      (*false: print meta-hypotheses as dots*)
val show_tags = ref false;      (*false: suppress tags*)

fun pretty_tag (name, args) = Pretty.strs (name :: map quote args);
val pretty_tags = Pretty.list "[" "]" o map pretty_tag;

fun pretty_thm_aux (pretty_sort, pretty_term) quote th =
  let
    val {hyps, prop, der = (ora, _), ...} = rep_thm th;
    val xshyps = Thm.extra_shyps th;
    val (_, tags) = Thm.get_name_tags th;

    val prt_term = (if quote then Pretty.quote else I) o pretty_term;

    val hlen = length xshyps + length hyps;
    val hsymbs =
      if hlen = 0 andalso not ora then []
      else if ! show_hyps then
        [Pretty.brk 2, Pretty.list "[" "]"
          (map prt_term hyps @ map pretty_sort xshyps @
            (if ora then [Pretty.str "!"] else []))]
      else [Pretty.brk 2, Pretty.str ("[" ^ implode (replicate hlen ".") ^
        (if ora then "!" else "") ^ "]")];
    val tsymbs =
      if null tags orelse not (! show_tags) then []
      else [Pretty.brk 1, pretty_tags tags];
  in Pretty.block (prt_term prop :: (hsymbs @ tsymbs)) end;

fun gen_pretty_thm quote th =
  let val sg = Thm.sign_of_thm th
  in pretty_thm_aux (Sign.pretty_sort sg, Sign.pretty_term sg) quote th end;

val pretty_thm = gen_pretty_thm true;
val pretty_thm_no_quote = gen_pretty_thm false;


val string_of_thm = Pretty.string_of o pretty_thm;
val pprint_thm = Pretty.pprint o pretty_thm;

fun pretty_thms [th] = pretty_thm th
  | pretty_thms ths = Pretty.block (Pretty.fbreaks (map pretty_thm ths));

val pretty_thm_sg = pretty_thm oo Thm.transfer_sg;
val pretty_thms_sg = pretty_thms oo (map o Thm.transfer_sg);


(* top-level commands for printing theorems *)

val print_thm = Pretty.writeln o pretty_thm;
val print_thms = Pretty.writeln o pretty_thms;

fun prth th = (print_thm th; th);

(*Print and return a sequence of theorems, separated by blank lines. *)
fun prthq thseq =
  (Seq.print (fn _ => print_thm) 100000 thseq; thseq);

(*Print and return a list of theorems, separated by blank lines. *)
fun prths ths = (seq (fn th => (print_thm th; writeln "")) ths; ths);


(* other printing commands *)

fun pretty_ctyp cT =
  let val {sign, T} = rep_ctyp cT in Sign.pretty_typ sign T end;

fun pprint_ctyp cT =
  let val {sign, T} = rep_ctyp cT in Sign.pprint_typ sign T end;

fun string_of_ctyp cT =
  let val {sign, T} = rep_ctyp cT in Sign.string_of_typ sign T end;

val print_ctyp = writeln o string_of_ctyp;

fun pretty_cterm ct =
  let val {sign, t, ...} = rep_cterm ct in Sign.pretty_term sign t end;

fun pprint_cterm ct =
  let val {sign, t, ...} = rep_cterm ct in Sign.pprint_term sign t end;

fun string_of_cterm ct =
  let val {sign, t, ...} = rep_cterm ct in Sign.string_of_term sign t end;

val print_cterm = writeln o string_of_cterm;



(** print theory **)

val pretty_theory = Sign.pretty_sg o Theory.sign_of;
val pprint_theory = Sign.pprint_sg o Theory.sign_of;

val print_syntax = Syntax.print_syntax o Theory.syn_of;


(* pretty_name_space  *)

fun pretty_name_space (kind, space) =
  let
    fun prt_entry (name, accs) = Pretty.block
      (Pretty.str (quote name ^ " =") :: Pretty.brk 1 ::
        Pretty.commas (map (Pretty.str o quote) accs));
  in
    Pretty.fbreaks (Pretty.str (kind ^ ":") :: map prt_entry (NameSpace.dest space))
    |> Pretty.block
  end;


(* pretty_full_theory *)

fun pretty_full_theory thy =
  let
    val sg = Theory.sign_of thy;

    fun prt_cls c = Sign.pretty_sort sg [c];
    fun prt_sort S = Sign.pretty_sort sg S;
    fun prt_arity t (c, Ss) = Sign.pretty_arity sg (t, Ss, [c]);
    fun prt_typ_no_tvars ty = Pretty.quote (Sign.pretty_typ sg (#1 (Type.freeze_thaw_type ty)));
    fun prt_term t = Pretty.quote (Sign.pretty_term sg t);

    fun pretty_classes cs = Pretty.block
      (Pretty.breaks (Pretty.str "classes:" :: map prt_cls cs));

    fun pretty_classrel (c, cs) = Pretty.block
      (prt_cls c :: Pretty.str " <" :: Pretty.brk 1 ::
        Pretty.commas (map prt_cls cs));

    fun pretty_default S = Pretty.block
      [Pretty.str "default:", Pretty.brk 1, prt_sort S];

    fun pretty_ty (t, n) = Pretty.block
      [Pretty.str t, Pretty.brk 1, Pretty.str (string_of_int n)];

    fun pretty_log_types ts = Pretty.block
      (Pretty.breaks (Pretty.str "logical types:" :: map Pretty.str ts));

    fun pretty_witness None = Pretty.str "universal non-emptiness witness: --"
      | pretty_witness (Some (T, S)) = Pretty.block
          [Pretty.str "universal non-emptiness witness:", Pretty.brk 1, prt_typ_no_tvars T,
            Pretty.brk 1, prt_sort S];

    fun pretty_abbr (t, (vs, rhs)) = Pretty.block
      [prt_typ_no_tvars (Type (t, map (fn v => TVar ((v, 0), [])) vs)),
        Pretty.str " =", Pretty.brk 1, prt_typ_no_tvars rhs];

    fun pretty_arities (t, ars) = map (prt_arity t) ars;

    fun pretty_const (c, ty) = Pretty.block
      [Pretty.str c, Pretty.str " ::", Pretty.brk 1, prt_typ_no_tvars ty];

    fun prt_axm (a, t) = Pretty.block [Pretty.str (a ^ ":"), Pretty.brk 1, prt_term t];


    val {self = _, tsig, const_tab, syn = _, path, spaces, data} = Sign.rep_sg sg;
    val {axioms, oracles, ...} = Theory.rep_theory thy;
    val spaces' = Library.sort_wrt fst spaces;
    val {classes, classrel, default, tycons = type_tab, log_types, univ_witness, abbrs, arities} =
      Type.rep_tsig tsig;
    val tycons = Sign.cond_extern_table sg Sign.typeK type_tab;
    val consts = Sign.cond_extern_table sg Sign.constK const_tab;
    val axms = Sign.cond_extern_table sg Theory.axiomK axioms;
    val oras = Sign.cond_extern_table sg Theory.oracleK oracles;
  in
    [Pretty.strs ("stamps:" :: Sign.stamp_names_of sg),
      Pretty.strs ("data:" :: Sign.data_kinds data),
      Pretty.strs ["name prefix:", NameSpace.pack (if_none path ["-"])],
      Pretty.big_list "name spaces:" (map pretty_name_space spaces'),
      pretty_classes classes,
      Pretty.big_list "class relation:" (map pretty_classrel (Symtab.dest classrel)),
      pretty_default default,
      pretty_log_types log_types,
      pretty_witness univ_witness,
      Pretty.big_list "type constructors:" (map pretty_ty tycons),
      Pretty.big_list "type abbreviations:" (map pretty_abbr (Symtab.dest abbrs)),
      Pretty.big_list "type arities:" (flat (map pretty_arities (Symtab.dest arities))),
      Pretty.big_list "consts:" (map pretty_const consts),
      Pretty.big_list "axioms:" (map prt_axm axms),
      Pretty.strs ("oracles:" :: (map #1 oras))]
  end;



(** print_goals **)

(* print_goals etc. *)

(*show consts with types in proof state output?*)
val show_consts = ref false;


(*print thm A1,...,An/B in "goal style" -- premises as numbered subgoals*)

local

fun ins_entry (x, y) [] = [(x, [y])]
  | ins_entry (x, y) ((pair as (x', ys')) :: pairs) =
      if x = x' then (x', y ins ys') :: pairs
      else pair :: ins_entry (x, y) pairs;

fun add_consts (Const (c, T), env) = ins_entry (T, (c, T)) env
  | add_consts (t $ u, env) = add_consts (u, add_consts (t, env))
  | add_consts (Abs (_, _, t), env) = add_consts (t, env)
  | add_consts (_, env) = env;

fun add_vars (Free (x, T), env) = ins_entry (T, (x, ~1)) env
  | add_vars (Var (xi, T), env) = ins_entry (T, xi) env
  | add_vars (Abs (_, _, t), env) = add_vars (t, env)
  | add_vars (t $ u, env) = add_vars (u, add_vars (t, env))
  | add_vars (_, env) = env;

fun add_varsT (Type (_, Ts), env) = foldr add_varsT (Ts, env)
  | add_varsT (TFree (x, S), env) = ins_entry (S, (x, ~1)) env
  | add_varsT (TVar (xi, S), env) = ins_entry (S, xi) env;

fun sort_idxs vs = map (apsnd (sort (prod_ord string_ord int_ord))) vs;
fun sort_cnsts cs = map (apsnd (sort_wrt fst)) cs;

fun consts_of t = sort_cnsts (add_consts (t, []));
fun vars_of t = sort_idxs (add_vars (t, []));
fun varsT_of t = rev (sort_idxs (it_term_types add_varsT (t, [])));

in

fun pretty_goals_aux (prt_sort, prt_typ, prt_term) begin_goal (msg, main) maxgoals state =
  let
    fun prt_atoms prt prtT (X, xs) = Pretty.block
      [Pretty.block (Pretty.commas (map prt xs)), Pretty.str " ::",
        Pretty.brk 1, prtT X];

    fun prt_var (x, ~1) = prt_term (Syntax.free x)
      | prt_var xi = prt_term (Syntax.var xi);

    fun prt_varT (x, ~1) = prt_typ (TFree (x, []))
      | prt_varT xi = prt_typ (TVar (xi, []));

    val prt_consts = prt_atoms (prt_term o Const) prt_typ;
    val prt_vars = prt_atoms prt_var prt_typ;
    val prt_varsT = prt_atoms prt_varT prt_sort;


    fun pretty_list _ _ [] = []
      | pretty_list name prt lst = [Pretty.big_list name (map prt lst)];

    fun pretty_subgoal (n, A) =
      Pretty.blk (0, [Pretty.str (begin_goal ^ " " ^ string_of_int n ^ ". "), prt_term A]);
    fun pretty_subgoals As = map pretty_subgoal (1 upto length As ~~ As);

    val pretty_ffpairs = pretty_list "flex-flex pairs:" (prt_term o Logic.mk_flexpair);

    val pretty_consts = pretty_list "constants:" prt_consts o consts_of;
    val pretty_vars = pretty_list "variables:" prt_vars o vars_of;
    val pretty_varsT = pretty_list "type variables:" prt_varsT o varsT_of;


    val {prop, ...} = rep_thm state;
    val (tpairs, As, B) = Logic.strip_horn prop;
    val ngoals = length As;

    fun pretty_gs (types, sorts) =
      (if main then [prt_term B] else []) @
       (if ngoals = 0 then [Pretty.str "No subgoals!"]
        else if ngoals > maxgoals then
          pretty_subgoals (take (maxgoals, As)) @
          (if msg then [Pretty.str ("A total of " ^ string_of_int ngoals ^ " subgoals...")]
           else [])
        else pretty_subgoals As) @
      pretty_ffpairs tpairs @
      (if ! show_consts then pretty_consts prop else []) @
      (if types then pretty_vars prop else []) @
      (if sorts then pretty_varsT prop else []);
  in
    setmp show_no_free_types true
      (setmp show_types (! show_types orelse ! show_sorts)
        (setmp show_sorts false pretty_gs))
   (! show_types orelse ! show_sorts, ! show_sorts)
  end;

fun pretty_goals_marker bg n th =
  let val sg = Thm.sign_of_thm th in
    pretty_goals_aux (Sign.pretty_sort sg, Sign.pretty_typ sg, Sign.pretty_term sg)
      bg (true, true) n th
  end;

val pretty_goals = pretty_goals_marker "";
val print_goals = (Pretty.writeln o Pretty.chunks) oo pretty_goals_marker "";

end;


(* print_current_goals *)

val current_goals_markers = ref ("", "", "");

fun pretty_current_goals n m th =
  let
    val ref (begin_state, end_state, begin_goal) = current_goals_markers;
    val ngoals = nprems_of th;
  in
    (if begin_state = "" then [] else [Pretty.str begin_state]) @
    [Pretty.str ("Level " ^ string_of_int n ^
      (if ngoals > 0 then " (" ^ string_of_int ngoals ^ " subgoal" ^
        (if ngoals <> 1 then "s" else "") ^ ")"
      else ""))] @
    pretty_goals_marker begin_goal m th @
    (if end_state = "" then [] else [Pretty.str end_state])
  end;

fun print_current_goals_default n m th =
  Pretty.writeln (Pretty.chunks (pretty_current_goals n m th));

val print_current_goals_fn = ref print_current_goals_default;

end;

structure BasicDisplay: BASIC_DISPLAY = Display;
open BasicDisplay;
