(*  Title:      Pure/display.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Printing of theories, theorems, etc.
*)

signature DISPLAY =
  sig
  val pprint_cterm	: cterm -> pprint_args -> unit
  val pprint_ctyp	: ctyp -> pprint_args -> unit
  val pprint_theory	: theory -> pprint_args -> unit
  val pprint_thm	: thm -> pprint_args -> unit
  val pretty_ctyp	: ctyp -> Pretty.T
  val pretty_cterm	: cterm -> Pretty.T
  val pretty_thm	: thm -> Pretty.T
  val print_cterm	: cterm -> unit
  val print_ctyp	: ctyp -> unit
  val show_consts	: bool ref
  val print_goals	: int -> thm -> unit
  val pretty_name_space : string * NameSpace.T -> Pretty.T
  val print_syntax	: theory -> unit
  val print_theory	: theory -> unit
  val print_data	: theory -> string -> unit
  val print_thm		: thm -> unit
  val prth		: thm -> thm
  val prthq		: thm Seq.seq -> thm Seq.seq
  val prths		: thm list -> thm list
  val show_hyps		: bool ref
  val string_of_cterm	: cterm -> string
  val string_of_ctyp	: ctyp -> string
  val string_of_thm	: thm -> string
  end;


structure Display : DISPLAY =
struct

(*If false, hypotheses are printed as dots*)
val show_hyps = ref true;

fun pretty_thm th =
  let
    val {sign, hyps, prop, ...} = rep_thm th;
    val xshyps = extra_shyps th;
    val hlen = length xshyps + length hyps;
    val hsymbs =
      if hlen = 0 then []
      else if ! show_hyps then
        [Pretty.brk 2, Pretty.list "[" "]"
          (map (Sign.pretty_term sign) hyps @
           map (Sign.pretty_sort sign) xshyps)]
      else
        [Pretty.brk 2, Pretty.str ("[" ^ implode (replicate hlen ".") ^ "]")];
  in
    Pretty.block (Sign.pretty_term sign prop :: hsymbs)
  end;

val string_of_thm = Pretty.string_of o pretty_thm;
val pprint_thm = Pretty.pprint o Pretty.quote o pretty_thm;


(** Top-level commands for printing theorems **)
val print_thm = writeln o string_of_thm;

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

val pprint_theory = Sign.pprint_sg o sign_of;

val print_syntax = Syntax.print_syntax o syn_of;
val print_data = Sign.print_data o sign_of;


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



(* print signature *)

fun print_sign sg =
  let
    fun prt_cls c = Sign.pretty_sort sg [c];
    fun prt_sort S = Sign.pretty_sort sg S;
    fun prt_arity t (c, Ss) = Sign.pretty_arity sg (t, Ss, [c]);
    fun prt_typ ty = Pretty.quote (Sign.pretty_typ sg ty);

    val ext_class = Sign.cond_extern sg Sign.classK;
    val ext_tycon = Sign.cond_extern sg Sign.typeK;
    val ext_const = Sign.cond_extern sg Sign.constK;


    fun pretty_classes cs = Pretty.block
      (Pretty.breaks (Pretty.str "classes:" :: map prt_cls cs));

    fun pretty_classrel (c, cs) = Pretty.block
      (prt_cls c :: Pretty.str " <" :: Pretty.brk 1 ::
        Pretty.commas (map prt_cls cs));

    fun pretty_default S = Pretty.block
      [Pretty.str "default:", Pretty.brk 1, prt_sort S];

    fun pretty_ty (t, n) = Pretty.block
      [Pretty.str (ext_tycon t), Pretty.str (" " ^ string_of_int n)];

    fun pretty_abbr (t, (vs, rhs)) = Pretty.block
      [prt_typ (Type (t, map (fn v => TVar ((v, 0), [])) vs)),
        Pretty.str " =", Pretty.brk 1, prt_typ rhs];

    fun pretty_arities (t, ars) = map (prt_arity t) ars;

    fun pretty_const (c, ty) = Pretty.block
      [Pretty.str c, Pretty.str " ::", Pretty.brk 1, prt_typ ty];

    val {self = _, tsig, const_tab, syn = _, path, spaces, data} = Sign.rep_sg sg;
    val spaces' = sort_wrt fst spaces;
    val {classes, classrel, default, tycons, abbrs, arities} =
      Type.rep_tsig tsig;
    val consts = sort_wrt fst (map (apfst ext_const) (Symtab.dest const_tab));
  in
    Pretty.writeln (Pretty.strs ("stamps:" :: Sign.stamp_names_of sg));
    Pretty.writeln (Pretty.strs ("data:" :: Sign.data_kinds data));
    Pretty.writeln (Pretty.strs ["name prefix:", NameSpace.pack path]);
    Pretty.writeln (Pretty.big_list "name spaces:" (map pretty_name_space spaces'));
    Pretty.writeln (pretty_classes classes);
    Pretty.writeln (Pretty.big_list "class relation:" (map pretty_classrel classrel));
    Pretty.writeln (pretty_default default);
    Pretty.writeln (Pretty.big_list "type constructors:" (map pretty_ty tycons));
    Pretty.writeln (Pretty.big_list "type abbreviations:" (map pretty_abbr abbrs));
    Pretty.writeln (Pretty.big_list "type arities:" (flat (map pretty_arities arities)));
    Pretty.writeln (Pretty.big_list "consts:" (map pretty_const consts))
  end;


(* print axioms, oracles, theorems *)

fun print_thy thy =
  let
    val {sign, axioms, oracles, ...} = rep_theory thy;
    val axioms = Symtab.dest axioms;
    val oras = map fst (Symtab.dest oracles);

    fun prt_axm (a, t) = Pretty.block
      [Pretty.str (Sign.cond_extern sign Theory.axiomK a ^ ":"), Pretty.brk 1,
        Pretty.quote (Sign.pretty_term sign t)];
  in
    Pretty.writeln (Pretty.big_list "axioms:" (map prt_axm axioms));
    Pretty.writeln (Pretty.strs ("oracles:" :: oras));
    print_data thy "Pure/theorems"	(*forward reference!*)
  end;

fun print_theory thy = (print_sign (sign_of thy); print_thy thy);



(** print_goals **)

(*print thm A1,...,An/B in "goal style" -- premises as numbered subgoals*)

(*also show consts in case of showing types?*)
val show_consts = ref false;


local

  (* utils *)

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


  (* prepare atoms *)

  fun consts_of t = sort_cnsts (add_consts (t, []));
  fun vars_of t = sort_idxs (add_vars (t, []));
  fun varsT_of t = rev (sort_idxs (it_term_types add_varsT (t, [])));

in

  fun print_goals maxgoals state =
    let
      val {sign, ...} = rep_thm state;

      val prt_term = Sign.pretty_term sign;
      val prt_typ = Sign.pretty_typ sign;
      val prt_sort = Sign.pretty_sort sign;

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


      fun print_list _ _ [] = ()
        | print_list name prt lst = (writeln "";
            Pretty.writeln (Pretty.big_list name (map prt lst)));

      fun print_subgoals (_, []) = ()
        | print_subgoals (n, A :: As) = (Pretty.writeln (Pretty.blk (0,
            [Pretty.str (" " ^ string_of_int n ^ ". "), prt_term A]));
              print_subgoals (n + 1, As));

      val print_ffpairs =
        print_list "Flex-flex pairs:" (prt_term o Logic.mk_flexpair);

      val print_consts = print_list "Constants:" prt_consts o consts_of;
      val print_vars = print_list "Variables:" prt_vars o vars_of;
      val print_varsT = print_list "Type variables:" prt_varsT o varsT_of;


      val {prop, ...} = rep_thm state;
      val (tpairs, As, B) = Logic.strip_horn prop;
      val ngoals = length As;

      fun print_gs (types, sorts) =
       (Pretty.writeln (prt_term B);
        if ngoals = 0 then writeln "No subgoals!"
        else if ngoals > maxgoals then
          (print_subgoals (1, take (maxgoals, As));
            writeln ("A total of " ^ string_of_int ngoals ^ " subgoals..."))
        else print_subgoals (1, As);

        print_ffpairs tpairs;

        if types andalso ! show_consts then print_consts prop else ();
        if types then print_vars prop else ();
        if sorts then print_varsT prop else ());
    in
      setmp show_no_free_types true
        (setmp show_types (! show_types orelse ! show_sorts)
          (setmp show_sorts false print_gs))
     (! show_types orelse ! show_sorts, ! show_sorts)
  end;

end;


end;

open Display;
