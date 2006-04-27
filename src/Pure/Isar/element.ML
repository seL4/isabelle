(*  Title:      Pure/Isar/element.ML
    ID:         $Id$
    Author:     Makarius

Explicit data structures for some Isar language elements.
*)

signature ELEMENT =
sig
  datatype ('typ, 'term) stmt =
    Shows of ((string * Attrib.src list) * ('term * ('term list * 'term list)) list) list |
    Obtains of (string * ((string * 'typ option) list * 'term list)) list
  type statement  (*= (string, string) stmt*)
  type statement_i  (*= (typ, term) stmt*)
  datatype ('typ, 'term, 'fact) ctxt =
    Fixes of (string * 'typ option * mixfix) list |
    Constrains of (string * 'typ) list |
    Assumes of ((string * Attrib.src list) * ('term * ('term list * 'term list)) list) list |
    Defines of ((string * Attrib.src list) * ('term * 'term list)) list |
    Notes of ((string * Attrib.src list) * ('fact * Attrib.src list) list) list
  type context (*= (string, string, thmref) ctxt*)
  type context_i (*= (typ, term, thm list) ctxt*)
  val map_ctxt: {name: string -> string,
    var: string * mixfix -> string * mixfix,
    typ: 'typ -> 'a, term: 'term -> 'b, fact: 'fact -> 'c,
    attrib: Attrib.src -> Attrib.src} -> ('typ, 'term, 'fact) ctxt -> ('a, 'b, 'c) ctxt
  val map_ctxt_values: (typ -> typ) -> (term -> term) -> (thm -> thm) -> context_i -> context_i
  val rename: (string * (string * mixfix option)) list -> string -> string
  val rename_var: (string * (string * mixfix option)) list -> string * mixfix -> string * mixfix
  val rename_term: (string * (string * mixfix option)) list -> term -> term
  val rename_thm: (string * (string * mixfix option)) list -> thm -> thm
  val rename_ctxt: (string * (string * mixfix option)) list -> context_i -> context_i
  val instT_type: typ Symtab.table -> typ -> typ
  val instT_term: typ Symtab.table -> term -> term
  val instT_thm: theory -> typ Symtab.table -> thm -> thm
  val instT_ctxt: theory -> typ Symtab.table -> context_i -> context_i
  val inst_term: typ Symtab.table * term Symtab.table -> term -> term
  val inst_thm: theory -> typ Symtab.table * term Symtab.table -> thm -> thm
  val inst_ctxt: theory -> typ Symtab.table * term Symtab.table -> context_i -> context_i
  val pretty_stmt: ProofContext.context -> statement_i -> Pretty.T list
  val pretty_ctxt: ProofContext.context -> context_i -> Pretty.T list
  val pretty_statement: ProofContext.context -> string -> thm -> Pretty.T
end;

structure Element: ELEMENT =
struct


(** conclusions **)

datatype ('typ, 'term) stmt =
  Shows of ((string * Attrib.src list) * ('term * ('term list * 'term list)) list) list |
  Obtains of (string * ((string * 'typ option) list * 'term list)) list;

type statement = (string, string) stmt;
type statement_i = (typ, term) stmt;



(** context elements **)

(* datatype ctxt *)

datatype ('typ, 'term, 'fact) ctxt =
  Fixes of (string * 'typ option * mixfix) list |
  Constrains of (string * 'typ) list |
  Assumes of ((string * Attrib.src list) * ('term * ('term list * 'term list)) list) list |
  Defines of ((string * Attrib.src list) * ('term * 'term list)) list |
  Notes of ((string * Attrib.src list) * ('fact * Attrib.src list) list) list;

type context = (string, string, thmref) ctxt;
type context_i = (typ, term, thm list) ctxt;

fun map_ctxt {name, var, typ, term, fact, attrib} =
  fn Fixes fixes => Fixes (fixes |> map (fn (x, T, mx) =>
       let val (x', mx') = var (x, mx) in (x', Option.map typ T, mx') end))
   | Constrains xs => Constrains (xs |> map (fn (x, T) => (#1 (var (x, NoSyn)), typ T)))
   | Assumes asms => Assumes (asms |> map (fn ((a, atts), propps) =>
      ((name a, map attrib atts), propps |> map (fn (t, (ps, qs)) =>
        (term t, (map term ps, map term qs))))))
   | Defines defs => Defines (defs |> map (fn ((a, atts), (t, ps)) =>
      ((name a, map attrib atts), (term t, map term ps))))
   | Notes facts => Notes (facts |> map (fn ((a, atts), bs) =>
      ((name a, map attrib atts), bs |> map (fn (ths, btts) => (fact ths, map attrib btts)))));

fun map_ctxt_values typ term thm = map_ctxt
  {name = I, var = I, typ = typ, term = term, fact = map thm,
    attrib = Args.map_values I typ term thm};



(** logical operations **)

(* derived rules *)

fun instantiate_tfrees thy subst =
  let
    val certT = Thm.ctyp_of thy;
    fun inst vs (a, T) = AList.lookup (op =) vs a
      |> Option.map (fn v => (certT (TVar v), certT T));
  in
    Drule.tvars_intr_list (map fst subst) #->
    (fn vs => Thm.instantiate (map_filter (inst vs) subst, []))
  end;

fun instantiate_frees thy subst =
  let val cert = Thm.cterm_of thy in
    Drule.forall_intr_list (map (cert o Free o fst) subst) #>
    Drule.forall_elim_list (map (cert o snd) subst)
  end;

fun hyps_rule rule th =
  let
    val cterm_rule = Thm.reflexive #> rule #> Thm.cprop_of #> Drule.dest_equals #> #1;
    val {hyps, ...} = Thm.crep_thm th;
  in
    Drule.implies_elim_list
      (rule (Drule.implies_intr_list hyps th))
      (map (Thm.assume o cterm_rule) hyps)
  end;


(* renaming *)

fun rename ren x =
  (case AList.lookup (op =) ren (x: string) of
    NONE => x
  | SOME (x', _) => x');

fun rename_var ren (x, mx) =
  (case (AList.lookup (op =) ren (x: string), mx) of
    (NONE, _) => (x, mx)
  | (SOME (x', NONE), Structure) => (x', mx)
  | (SOME (x', SOME _), Structure) =>
      error ("Attempt to change syntax of structure parameter " ^ quote x)
  | (SOME (x', NONE), _) => (x', NoSyn)
  | (SOME (x', SOME mx'), _) => (x', mx'));

fun rename_term ren (Free (x, T)) = Free (rename ren x, T)
  | rename_term ren (t $ u) = rename_term ren t $ rename_term ren u
  | rename_term ren (Abs (x, T, t)) = Abs (x, T, rename_term ren t)
  | rename_term _ a = a;

fun rename_thm ren th =
  let
    val subst = Drule.frees_of th
      |> map_filter (fn (x, T) =>
        let val x' = rename ren x
        in if x = x' then NONE else SOME ((x, T), (Free (x', T))) end);
  in
    if null subst then th
    else th |> hyps_rule (instantiate_frees (Thm.theory_of_thm th) subst)
  end;

fun rename_ctxt ren =
  map_ctxt_values I (rename_term ren) (rename_thm ren)
  #> map_ctxt {name = I, typ = I, term = I, fact = I, attrib = I, var = rename_var ren};


(* type instantiation *)

fun instT_type env =
  if Symtab.is_empty env then I
  else Term.map_type_tfree (fn (x, S) => the_default (TFree (x, S)) (Symtab.lookup env x));

fun instT_term env =
  if Symtab.is_empty env then I
  else Term.map_term_types (instT_type env);

fun instT_subst env th =
  Drule.tfrees_of th
  |> map_filter (fn (a, S) =>
    let
      val T = TFree (a, S);
      val T' = the_default T (Symtab.lookup env a);
    in if T = T' then NONE else SOME (a, T') end);

fun instT_thm thy env th =
  if Symtab.is_empty env then th
  else
    let val subst = instT_subst env th
    in if null subst then th else th |> hyps_rule (instantiate_tfrees thy subst) end;

fun instT_ctxt thy env =
  map_ctxt_values (instT_type env) (instT_term env) (instT_thm thy env);


(* type and term instantiation *)

fun inst_term (envT, env) =
  if Symtab.is_empty env then instT_term envT
  else
    let
      val instT = instT_type envT;
      fun inst (Const (x, T)) = Const (x, instT T)
        | inst (Free (x, T)) =
            (case Symtab.lookup env x of
              NONE => Free (x, instT T)
            | SOME t => t)
        | inst (Var (xi, T)) = Var (xi, instT T)
        | inst (b as Bound _) = b
        | inst (Abs (x, T, t)) = Abs (x, instT T, inst t)
        | inst (t $ u) = inst t $ inst u;
    in Envir.beta_norm o inst end;

fun inst_thm thy (envT, env) th =
  if Symtab.is_empty env then instT_thm thy envT th
  else
    let
      val substT = instT_subst envT th;
      val subst = Drule.frees_of th
        |> map_filter (fn (x, T) =>
          let
            val T' = instT_type envT T;
            val t = Free (x, T');
            val t' = the_default t (Symtab.lookup env x);
          in if t aconv t' then NONE else SOME ((x, T'), t') end);
    in
      if null substT andalso null subst then th
      else th |> hyps_rule
       (instantiate_tfrees thy substT #>
        instantiate_frees thy subst #>
        Drule.fconv_rule (Thm.beta_conversion true))
    end;

fun inst_ctxt thy envs =
  map_ctxt_values (instT_type (#1 envs)) (inst_term envs) (inst_thm thy envs);



(** pretty printing **)

fun pretty_items _ _ [] = []
  | pretty_items keyword sep (x :: ys) =
      Pretty.block [Pretty.keyword keyword, Pretty.brk 1, x] ::
        map (fn y => Pretty.block [Pretty.str "  ", Pretty.keyword sep, Pretty.brk 1, y]) ys;

fun pretty_name_atts ctxt (name, atts) sep =
  if name = "" andalso null atts then []
  else [Pretty.block (Pretty.breaks (Pretty.str (ProofContext.extern_thm ctxt name) ::
    Args.pretty_attribs ctxt atts @ [Pretty.str sep]))];


(* pretty_stmt *)

fun pretty_stmt ctxt =
  let
    val prt_typ = Pretty.quote o ProofContext.pretty_typ ctxt;
    val prt_term = Pretty.quote o ProofContext.pretty_term ctxt;
    val prt_terms = separate (Pretty.keyword "and") o map prt_term;
    val prt_name_atts = pretty_name_atts ctxt;

    fun prt_show (a, ts) =
      Pretty.block (Pretty.breaks (prt_name_atts a ":" @ prt_terms (map fst ts)));

    fun prt_var (x, SOME T) = Pretty.block [Pretty.str (x ^ " ::"), Pretty.brk 1, prt_typ T]
      | prt_var (x, NONE) = Pretty.str x;

    fun prt_obtain (_, ([], ts)) = Pretty.block (Pretty.breaks (prt_terms ts))
      | prt_obtain (_, (xs, ts)) = Pretty.block (Pretty.breaks
          (map prt_var xs @ [Pretty.keyword "where"] @ prt_terms ts));
  in
    fn Shows shows => pretty_items "shows" "and" (map prt_show shows)
     | Obtains obtains => pretty_items "obtains" "|" (map prt_obtain obtains)
  end;


(* pretty_ctxt *)

fun pretty_ctxt ctxt =
  let
    val prt_typ = Pretty.quote o ProofContext.pretty_typ ctxt;
    val prt_term = Pretty.quote o ProofContext.pretty_term ctxt;
    val prt_thm = Pretty.backquote o ProofContext.pretty_thm ctxt;
    val prt_name_atts = pretty_name_atts ctxt;

    fun prt_mixfix NoSyn = []
      | prt_mixfix mx = [Pretty.brk 2, Syntax.pretty_mixfix mx];

    fun prt_fix (x, SOME T, mx) = Pretty.block (Pretty.str (x ^ " ::") :: Pretty.brk 1 ::
          prt_typ T :: Pretty.brk 1 :: prt_mixfix mx)
      | prt_fix (x, NONE, mx) = Pretty.block (Pretty.str x :: Pretty.brk 1 :: prt_mixfix mx);
    fun prt_constrain (x, T) = prt_fix (x, SOME T, NoSyn);

    fun prt_asm (a, ts) =
      Pretty.block (Pretty.breaks (prt_name_atts a ":" @ map (prt_term o fst) ts));
    fun prt_def (a, (t, _)) =
      Pretty.block (Pretty.breaks (prt_name_atts a ":" @ [prt_term t]));

    fun prt_fact (ths, []) = map prt_thm ths
      | prt_fact (ths, atts) = Pretty.enclose "(" ")"
          (Pretty.breaks (map prt_thm ths)) :: Args.pretty_attribs ctxt atts;
    fun prt_note (a, ths) =
      Pretty.block (Pretty.breaks (flat (prt_name_atts a "=" :: map prt_fact ths)));
  in
    fn Fixes fixes => pretty_items "fixes" "and" (map prt_fix fixes)
     | Constrains xs => pretty_items "constrains" "and" (map prt_constrain xs)
     | Assumes asms => pretty_items "assumes" "and" (map prt_asm asms)
     | Defines defs => pretty_items "defines" "and" (map prt_def defs)
     | Notes facts => pretty_items "notes" "and" (map prt_note facts)
  end;


(* pretty_statement *)

local

fun thm_name kind th prts =
  let val head =
    (case #1 (Thm.get_name_tags th) of
      "" => Pretty.command kind
    | a => Pretty.block [Pretty.command kind, Pretty.brk 1, Pretty.str (Sign.base_name a ^ ":")])
  in Pretty.block (Pretty.fbreaks (head :: prts)) end;

fun obtain prop ctxt =
  let
    val xs = ProofContext.rename_frees ctxt [] (Logic.strip_params prop);
    val args = rev (map Free xs);
    val As = Logic.strip_assums_hyp prop |> map (fn t => Term.subst_bounds (args, t));
    val ctxt' = ctxt |> fold ProofContext.declare_term args;
  in (("", (map (apsnd SOME) xs, As)), ctxt') end;

in

fun pretty_statement ctxt kind raw_th =
  let
    val thy = ProofContext.theory_of ctxt;
    val th = Goal.norm_hhf raw_th;

    fun standard_thesis t =
      let
        val C = ObjectLogic.drop_judgment thy (Thm.concl_of th);
        val C' = Var ((AutoBind.thesisN, Thm.maxidx_of th + 1), Term.fastype_of C);
      in Term.subst_atomic [(C, C')] t end;

    val raw_prop =
      Thm.prop_of th
      |> singleton (ProofContext.monomorphic ctxt)
      |> K (ObjectLogic.is_elim th) ? standard_thesis
      |> Term.zero_var_indexes;

    val vars = Term.add_vars raw_prop [];
    val frees = ProofContext.rename_frees ctxt [raw_prop] (map (apfst fst) vars);
    val fixes = rev (filter_out (fn (x, _) => x = AutoBind.thesisN) frees);

    val prop = Term.instantiate ([], vars ~~ map Free frees) raw_prop;
    val (prems, concl) = Logic.strip_horn prop;
    val thesis = ObjectLogic.fixed_judgment thy AutoBind.thesisN;
    val (asms, cases) = take_suffix (fn prem => thesis aconv Logic.strip_assums_concl prem) prems;
  in
    pretty_ctxt ctxt (Fixes (map (fn (x, T) => (x, SOME T, NoSyn)) fixes)) @
    pretty_ctxt ctxt (Assumes (map (fn t => (("", []), [(t, ([], []))])) asms)) @
    pretty_stmt ctxt
     (if null cases then Shows [(("", []), [(concl, ([], []))])]
      else Obtains (#1 (fold_map obtain cases (ctxt |> ProofContext.declare_term prop))))
  end |> thm_name kind raw_th;

end;

end;
