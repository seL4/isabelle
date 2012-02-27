(*  Title:      Pure/Tools/find_consts.ML
    Author:     Timothy Bourke and Gerwin Klein, NICTA

Hoogle-like (http://www-users.cs.york.ac.uk/~ndm/hoogle) searching by
type over constants, but matching is not fuzzy.
*)

signature FIND_CONSTS =
sig
  datatype criterion =
      Strict of string
    | Loose of string
    | Name of string
  val find_consts : Proof.context -> (bool * criterion) list -> unit
end;

structure Find_Consts : FIND_CONSTS =
struct

(* search criteria *)

datatype criterion =
    Strict of string
  | Loose of string
  | Name of string;


(* matching types/consts *)

fun matches_subtype thy typat =
  Term.exists_subtype (fn ty => Sign.typ_instance thy (ty, typat));

fun check_const pred (nm, (ty, _)) =
  if pred (nm, ty) then SOME (Term.size_of_typ ty) else NONE;

fun opt_not f (c as (_, (ty, _))) =
  if is_some (f c) then NONE else SOME (Term.size_of_typ ty);

fun filter_const _ NONE = NONE
  | filter_const f (SOME (c, r)) =
      (case f c of
        NONE => NONE
      | SOME i => SOME (c, Int.min (r, i)));


(* pretty results *)

fun pretty_criterion (b, c) =
  let
    fun prfx s = if b then s else "-" ^ s;
  in
    (case c of
      Strict pat => Pretty.str (prfx "strict: " ^ quote pat)
    | Loose pat => Pretty.str (prfx (quote pat))
    | Name name => Pretty.str (prfx "name: " ^ quote name))
  end;

fun pretty_const ctxt (nm, ty) =
  let
    val ty' = Logic.unvarifyT_global ty;
  in
    Pretty.block
     [Pretty.str nm, Pretty.str " ::", Pretty.brk 1,
      Pretty.quote (Syntax.pretty_typ ctxt ty')]
  end;


(* find_consts *)

fun find_consts ctxt raw_criteria =
  let
    val thy = Proof_Context.theory_of ctxt;
    val low_ranking = 10000;

    fun user_visible consts (nm, _) =
      if Consts.is_concealed consts nm then NONE else SOME low_ranking;

    fun make_pattern crit =
      let
        val raw_T = Syntax.parse_typ ctxt crit;
        val t =
          Syntax.check_term
            (Proof_Context.set_mode Proof_Context.mode_pattern ctxt)
            (Term.dummy_pattern raw_T);
      in Term.type_of t end;

    fun make_match (Strict arg) =
          let val qty = make_pattern arg; in
            fn (_, (ty, _)) =>
              let
                val tye = Sign.typ_match thy (qty, ty) Vartab.empty;
                val sub_size =
                  Vartab.fold (fn (_, (_, t)) => fn n => Term.size_of_typ t + n) tye 0;
              in SOME sub_size end handle Type.TYPE_MATCH => NONE
          end
      | make_match (Loose arg) =
          check_const (matches_subtype thy (make_pattern arg) o snd)
      | make_match (Name arg) = check_const (match_string arg o fst);

    fun make_criterion (b, crit) = (if b then I else opt_not) (make_match crit);
    val criteria = map make_criterion raw_criteria;

    val consts = Sign.consts_of thy;
    val (_, consts_tab) = #constants (Consts.dest consts);
    fun eval_entry c =
      fold filter_const (user_visible consts :: criteria)
        (SOME (c, low_ranking));

    val matches =
      Symtab.fold (cons o eval_entry) consts_tab []
      |> map_filter I
      |> sort (rev_order o int_ord o pairself snd)
      |> map (apsnd fst o fst);
  in
    Pretty.big_list "searched for:" (map pretty_criterion raw_criteria) ::
    Pretty.str "" ::
    Pretty.str
     (if null matches
      then "nothing found"
      else "found " ^ string_of_int (length matches) ^ " constant(s):") ::
    Pretty.str "" ::
    map (pretty_const ctxt) matches
  end |> Pretty.chunks |> Pretty.writeln;


(* command syntax *)

local

val criterion =
  Parse.reserved "strict" |-- Parse.!!! (Parse.$$$ ":" |-- Parse.xname) >> Strict ||
  Parse.reserved "name" |-- Parse.!!! (Parse.$$$ ":" |-- Parse.xname) >> Name ||
  Parse.xname >> Loose;

in

val _ =
  Outer_Syntax.improper_command "find_consts" "search constants by type pattern" Keyword.diag
    (Scan.repeat ((Scan.option Parse.minus >> is_none) -- criterion)
      >> (fn spec => Toplevel.no_timing o
        Toplevel.keep (fn state => find_consts (Toplevel.context_of state) spec)));

end;

end;

