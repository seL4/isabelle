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
  val pretty_thm	: thm -> Pretty.T
  val print_cterm	: cterm -> unit
  val print_ctyp	: ctyp -> unit
  val print_goals	: int -> thm -> unit
  val print_goals_ref	: (int -> thm -> unit) ref
  val print_syntax	: theory -> unit
  val print_theory	: theory -> unit
  val print_thm		: thm -> unit
  val prth		: thm -> thm
  val prthq		: thm Sequence.seq -> thm Sequence.seq
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
          (map (Sign.pretty_term sign) hyps @ map Sign.pretty_sort xshyps)]
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
  (Sequence.prints (fn _ => print_thm) 100000 thseq; thseq);

(*Print and return a list of theorems, separated by blank lines. *)
fun prths ths = (print_list_ln print_thm ths; ths);


(* other printing commands *)

fun pprint_ctyp cT =
  let val {sign, T} = rep_ctyp cT in Sign.pprint_typ sign T end;

fun string_of_ctyp cT =
  let val {sign, T} = rep_ctyp cT in Sign.string_of_typ sign T end;

val print_ctyp = writeln o string_of_ctyp;

fun pprint_cterm ct =
  let val {sign, t, ...} = rep_cterm ct in Sign.pprint_term sign t end;

fun string_of_cterm ct =
  let val {sign, t, ...} = rep_cterm ct in Sign.string_of_term sign t end;

val print_cterm = writeln o string_of_cterm;


(* print theory *)

val pprint_theory = Sign.pprint_sg o sign_of;

val print_syntax = Syntax.print_syntax o syn_of;

fun print_axioms thy =
  let
    val {sign, new_axioms, ...} = rep_theory thy;
    val axioms = Symtab.dest new_axioms;

    fun prt_axm (a, t) = Pretty.block [Pretty.str (a ^ ":"), Pretty.brk 1,
      Pretty.quote (Sign.pretty_term sign t)];
  in
    Pretty.writeln (Pretty.big_list "additional axioms:" (map prt_axm axioms))
  end;

fun print_theory thy = (Sign.print_sg (sign_of thy); print_axioms thy);



(** Print thm A1,...,An/B in "goal style" -- premises as numbered subgoals **)

(* get type_env, sort_env of term *)

local
  open Syntax;

  fun ins_entry (x, y) [] = [(x, [y])]
    | ins_entry (x, y) ((pair as (x', ys')) :: pairs) =
        if x = x' then (x', y ins_string ys') :: pairs
        else pair :: ins_entry (x, y) pairs;

  fun add_type_env (Free (x, T), env) = ins_entry (T, x) env
    | add_type_env (Var (xi, T), env) = ins_entry (T, string_of_vname xi) env
    | add_type_env (Abs (_, _, t), env) = add_type_env (t, env)
    | add_type_env (t $ u, env) = add_type_env (u, add_type_env (t, env))
    | add_type_env (_, env) = env;

  fun add_sort_env (Type (_, Ts), env) = foldr add_sort_env (Ts, env)
    | add_sort_env (TFree (x, S), env) = ins_entry (S, x) env
    | add_sort_env (TVar (xi, S), env) = ins_entry (S, string_of_vname xi) env;

  fun sort l = map (apsnd sort_strings) l;
in
  fun type_env t = sort (add_type_env (t, []));
  fun sort_env t = rev (sort (it_term_types add_sort_env (t, [])));
end;


(* print_goals *)

fun print_goals maxgoals state =
  let
    open Syntax;

    val {sign, prop, ...} = rep_thm state;

    val pretty_term = Sign.pretty_term sign;
    val pretty_typ = Sign.pretty_typ sign;
    val pretty_sort = Sign.pretty_sort;

    fun pretty_vars prtf (X, vs) = Pretty.block
      [Pretty.block (Pretty.commas (map Pretty.str vs)),
        Pretty.str " ::", Pretty.brk 1, prtf X];

    fun print_list _ _ [] = ()
      | print_list name prtf lst =
          (writeln ""; Pretty.writeln (Pretty.big_list name (map prtf lst)));


    fun print_goals (_, []) = ()
      | print_goals (n, A :: As) = (Pretty.writeln (Pretty.blk (0,
          [Pretty.str (" " ^ string_of_int n ^ ". "), pretty_term A]));
            print_goals (n + 1, As));

    val print_ffpairs =
      print_list "Flex-flex pairs:" (pretty_term o Logic.mk_flexpair);

    val print_types = print_list "Types:" (pretty_vars pretty_typ) o type_env;
    val print_sorts = print_list "Sorts:" (pretty_vars pretty_sort) o sort_env;


    val (tpairs, As, B) = Logic.strip_horn prop;
    val ngoals = length As;

    val orig_no_freeTs = ! show_no_free_types;
    val orig_types = ! show_types;
    val orig_sorts = ! show_sorts;

    fun restore () =
      (show_no_free_types := orig_no_freeTs;
        show_types := orig_types;
        show_sorts := orig_sorts);
  in
    (show_no_free_types := true;
      show_types := (orig_types orelse orig_sorts);
      show_sorts := false;
      Pretty.writeln (pretty_term B);
      if ngoals = 0 then writeln "No subgoals!"
      else if ngoals > maxgoals then
        (print_goals (1, take (maxgoals, As));
          writeln ("A total of " ^ string_of_int ngoals ^ " subgoals..."))
      else print_goals (1, As);

      print_ffpairs tpairs;

      if orig_sorts then
        (print_types prop; print_sorts prop)
      else if orig_types then
        print_types prop
      else ())
    handle exn => (restore (); raise exn);
    restore ()
  end;


(*"hook" for user interfaces: allows print_goals to be replaced*)	(* FIXME remove!? *)
val print_goals_ref = ref print_goals;

end;

open Display;
