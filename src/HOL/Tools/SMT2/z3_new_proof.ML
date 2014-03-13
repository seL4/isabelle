(*  Title:      HOL/Tools/SMT2/z3_new_proof.ML
    Author:     Sascha Boehme, TU Muenchen

Z3 proofs: parsing and abstract syntax tree.
*)

signature Z3_NEW_PROOF =
sig
  (*proof rules*)
  datatype z3_rule = True_Axiom | Asserted | Goal | Modus_Ponens | Reflexivity |
    Symmetry | Transitivity | Transitivity_Star | Monotonicity | Quant_Intro |
    Distributivity | And_Elim | Not_Or_Elim | Rewrite | Rewrite_Star |
    Pull_Quant | Pull_Quant_Star | Push_Quant | Elim_Unused_Vars |
    Dest_Eq_Res | Quant_Inst | Hypothesis | Lemma | Unit_Resolution |
    Iff_True | Iff_False | Commutativity | Def_Axiom | Intro_Def | Apply_Def |
    Iff_Oeq | Nnf_Pos | Nnf_Neg | Nnf_Star | Cnf_Star | Skolemize |
    Modus_Ponens_Oeq | Th_Lemma of string
  val string_of_rule: z3_rule -> string

  (*proofs*)
  datatype z3_step = Z3_Step of {
    id: int,
    rule: z3_rule,
    prems: int list,
    concl: term,
    fixes: string list,
    is_fix_step: bool}

  (*type and term parsers*)
  type type_parser = SMTLIB2.tree * typ list -> typ option
  type term_parser = SMTLIB2.tree * term list -> term option
  val add_type_parser: type_parser -> Context.generic -> Context.generic
  val add_term_parser: term_parser -> Context.generic -> Context.generic

  (*proof parser*)
  val parse: typ Symtab.table -> term Symtab.table -> string list ->
    Proof.context -> z3_step list * Proof.context
end

structure Z3_New_Proof: Z3_NEW_PROOF =
struct

(* proof rules *)

datatype z3_rule = True_Axiom | Asserted | Goal | Modus_Ponens | Reflexivity |
  Symmetry | Transitivity | Transitivity_Star | Monotonicity | Quant_Intro |
  Distributivity | And_Elim | Not_Or_Elim | Rewrite | Rewrite_Star |
  Pull_Quant | Pull_Quant_Star | Push_Quant | Elim_Unused_Vars | Dest_Eq_Res |
  Quant_Inst | Hypothesis | Lemma | Unit_Resolution | Iff_True | Iff_False |
  Commutativity | Def_Axiom | Intro_Def | Apply_Def | Iff_Oeq | Nnf_Pos |
  Nnf_Neg | Nnf_Star | Cnf_Star | Skolemize | Modus_Ponens_Oeq |
  Th_Lemma of string
  (* TODO: some proof rules come with further information
     that is currently dropped by the parser *)

val rule_names = Symtab.make [
  ("true-axiom", True_Axiom),
  ("asserted", Asserted),
  ("goal", Goal),
  ("mp", Modus_Ponens),
  ("refl", Reflexivity),
  ("symm", Symmetry),
  ("trans", Transitivity),
  ("trans*", Transitivity_Star),
  ("monotonicity", Monotonicity),
  ("quant-intro", Quant_Intro),
  ("distributivity", Distributivity),
  ("and-elim", And_Elim),
  ("not-or-elim", Not_Or_Elim),
  ("rewrite", Rewrite),
  ("rewrite*", Rewrite_Star),
  ("pull-quant", Pull_Quant),
  ("pull-quant*", Pull_Quant_Star),
  ("push-quant", Push_Quant),
  ("elim-unused", Elim_Unused_Vars),
  ("der", Dest_Eq_Res),
  ("quant-inst", Quant_Inst),
  ("hypothesis", Hypothesis),
  ("lemma", Lemma),
  ("unit-resolution", Unit_Resolution),
  ("iff-true", Iff_True),
  ("iff-false", Iff_False),
  ("commutativity", Commutativity),
  ("def-axiom", Def_Axiom),
  ("intro-def", Intro_Def),
  ("apply-def", Apply_Def),
  ("iff~", Iff_Oeq),
  ("nnf-pos", Nnf_Pos),
  ("nnf-neg", Nnf_Neg),
  ("nnf*", Nnf_Star),
  ("cnf*", Cnf_Star),
  ("sk", Skolemize),
  ("mp~", Modus_Ponens_Oeq)]

fun rule_of_string name =
  (case Symtab.lookup rule_names name of
    SOME rule => rule
  | NONE => error ("unknown Z3 proof rule " ^ quote name))

fun string_of_rule (Th_Lemma kind) = "th-lemma " ^ kind
  | string_of_rule r =
      let fun eq_rule (s, r') = if r = r' then SOME s else NONE 
      in the (Symtab.get_first eq_rule rule_names) end



(* proofs *)

datatype z3_node = Z3_Node of {
  id: int,
  rule: z3_rule,
  prems: z3_node list,
  concl: term,
  bounds: string list}

fun mk_node id rule prems concl bounds =
  Z3_Node {id=id, rule=rule, prems=prems, concl=concl, bounds=bounds}

datatype z3_step = Z3_Step of {
  id: int,
  rule: z3_rule,
  prems: int list,
  concl: term,
  fixes: string list,
  is_fix_step: bool}

fun mk_step id rule prems concl fixes is_fix_step =
  Z3_Step {id=id, rule=rule, prems=prems, concl=concl, fixes=fixes,
    is_fix_step=is_fix_step}



(* core type and term parser *)

fun core_type_parser (SMTLIB2.Sym "Bool", []) = SOME @{typ HOL.bool}
  | core_type_parser (SMTLIB2.Sym "Int", []) = SOME @{typ Int.int}
  | core_type_parser _ = NONE

fun mk_unary n t =
  let val T = fastype_of t
  in Const (n, T --> T) $ t end

fun mk_binary' n T U t1 t2 = Const (n, [T, T] ---> U) $ t1 $ t2

fun mk_binary n t1 t2 =
  let val T = fastype_of t1
  in mk_binary' n T T t1 t2 end

fun mk_rassoc f t ts =
  let val us = rev (t :: ts)
  in fold f (tl us) (hd us) end

fun mk_lassoc f t ts = fold (fn u1 => fn u2 => f u2 u1) ts t

fun mk_lassoc' n = mk_lassoc (mk_binary n)

fun mk_binary_pred n S t1 t2 =
  let
    val T1 = fastype_of t1
    val T2 = fastype_of t2
    val T =
      if T1 <> Term.dummyT then T1
      else if T2 <> Term.dummyT then T2
      else TVar (("?a", serial ()), S)
  in mk_binary' n T @{typ HOL.bool} t1 t2 end

fun mk_less t1 t2 = mk_binary_pred @{const_name ord_class.less} @{sort linorder} t1 t2
fun mk_less_eq t1 t2 = mk_binary_pred @{const_name ord_class.less_eq} @{sort linorder} t1 t2

fun core_term_parser (SMTLIB2.Sym "true", _) = SOME @{const HOL.True}
  | core_term_parser (SMTLIB2.Sym "false", _) = SOME @{const HOL.False}
  | core_term_parser (SMTLIB2.Sym "not", [t]) = SOME (HOLogic.mk_not t)
  | core_term_parser (SMTLIB2.Sym "and", t :: ts) = SOME (mk_rassoc (curry HOLogic.mk_conj) t ts)
  | core_term_parser (SMTLIB2.Sym "or", t :: ts) = SOME (mk_rassoc (curry HOLogic.mk_disj) t ts)
  | core_term_parser (SMTLIB2.Sym "=>", [t1, t2]) = SOME (HOLogic.mk_imp (t1, t2))
  | core_term_parser (SMTLIB2.Sym "implies", [t1, t2]) = SOME (HOLogic.mk_imp (t1, t2))
  | core_term_parser (SMTLIB2.Sym "=", [t1, t2]) = SOME (HOLogic.mk_eq (t1, t2))
  | core_term_parser (SMTLIB2.Sym "~", [t1, t2]) = SOME (HOLogic.mk_eq (t1, t2))
  | core_term_parser (SMTLIB2.Sym "ite", [t1, t2, t3]) =
      let
        val T = fastype_of t2
        val c = Const (@{const_name HOL.If}, [@{typ HOL.bool}, T, T] ---> T)
      in SOME (c $ t1 $ t2 $ t3) end
  | core_term_parser (SMTLIB2.Num i, []) = SOME (HOLogic.mk_number @{typ Int.int} i)
  | core_term_parser (SMTLIB2.Sym "-", [t]) = SOME (mk_unary @{const_name uminus_class.uminus} t)
  | core_term_parser (SMTLIB2.Sym "~", [t]) = SOME (mk_unary @{const_name uminus_class.uminus} t)
  | core_term_parser (SMTLIB2.Sym "+", t :: ts) =
      SOME (mk_lassoc' @{const_name plus_class.plus} t ts)
  | core_term_parser (SMTLIB2.Sym "-", t :: ts) =
      SOME (mk_lassoc' @{const_name minus_class.minus} t ts)
  | core_term_parser (SMTLIB2.Sym "*", t :: ts) =
      SOME (mk_lassoc' @{const_name times_class.times} t ts)
  | core_term_parser (SMTLIB2.Sym "div", [t1, t2]) = SOME (mk_binary @{const_name SMT2.z3div} t1 t2)
  | core_term_parser (SMTLIB2.Sym "mod", [t1, t2]) = SOME (mk_binary @{const_name SMT2.z3mod} t1 t2)
  | core_term_parser (SMTLIB2.Sym "<", [t1, t2]) = SOME (mk_less t1 t2)
  | core_term_parser (SMTLIB2.Sym ">", [t1, t2]) = SOME (mk_less t2 t1)
  | core_term_parser (SMTLIB2.Sym "<=", [t1, t2]) = SOME (mk_less_eq t1 t2)
  | core_term_parser (SMTLIB2.Sym ">=", [t1, t2]) = SOME (mk_less_eq t2 t1)
  | core_term_parser _ = NONE



(* type and term parsers *)

type type_parser = SMTLIB2.tree * typ list -> typ option

type term_parser = SMTLIB2.tree * term list -> term option

fun id_ord ((id1, _), (id2, _)) = int_ord (id1, id2)

structure Parsers = Generic_Data
(
  type T = (int * type_parser) list * (int * term_parser) list
  val empty = ([(serial (), core_type_parser)], [(serial (), core_term_parser)])
  val extend = I
  fun merge ((tys1, ts1), (tys2, ts2)) =
    (Ord_List.merge id_ord (tys1, tys2), Ord_List.merge id_ord (ts1, ts2))
)

fun add_type_parser type_parser =
  Parsers.map (apfst (Ord_List.insert id_ord (serial (), type_parser)))

fun add_term_parser term_parser =
  Parsers.map (apsnd (Ord_List.insert id_ord (serial (), term_parser)))

fun get_type_parsers ctxt = map snd (fst (Parsers.get (Context.Proof ctxt)))
fun get_term_parsers ctxt = map snd (snd (Parsers.get (Context.Proof ctxt)))

fun apply_parsers parsers x =
  let
    fun apply [] = NONE
      | apply (parser :: parsers) =
          (case parser x of
            SOME y => SOME y
          | NONE => apply parsers)
  in apply parsers end



(* proof parser context *)

datatype shared = Tree of SMTLIB2.tree | Term of term | Proof of z3_node | None

type 'a context = {
  ctxt: Proof.context,
  id: int,
  syms: shared Symtab.table,
  typs: typ Symtab.table,
  funs: term Symtab.table,
  extra: 'a}

fun mk_context ctxt id syms typs funs extra: 'a context =
  {ctxt=ctxt, id=id, syms=syms, typs=typs, funs=funs, extra=extra}

fun empty_context ctxt typs funs = mk_context ctxt 1 Symtab.empty typs funs []

fun ctxt_of ({ctxt, ...}: 'a context) = ctxt

fun next_id ({ctxt, id, syms, typs, funs, extra}: 'a context) =
  (id, mk_context ctxt (id + 1) syms typs funs extra)

fun lookup_binding ({syms, ...}: 'a context) =
  the_default None o Symtab.lookup syms

fun map_syms f ({ctxt, id, syms, typs, funs, extra}: 'a context) =
  mk_context ctxt id (f syms) typs funs extra

fun update_binding b = map_syms (Symtab.update b)

fun with_bindings bs f cx =
  let val bs' = map (lookup_binding cx o fst) bs
  in
    cx
    |> fold update_binding bs
    |> f
    ||> fold2 (fn (name, _) => update_binding o pair name) bs bs'
  end

fun lookup_typ ({typs, ...}: 'a context) = Symtab.lookup typs
fun lookup_fun ({funs, ...}: 'a context) = Symtab.lookup funs

fun fresh_fun add name n T ({ctxt, id, syms, typs, funs, extra}: 'a context) =
  let
    val (n', ctxt') = yield_singleton Variable.variant_fixes n ctxt
    val t = Free (n', T)
    val funs' = Symtab.update (name, t) funs
  in (t, mk_context ctxt' id syms typs funs' (add (n', T) extra)) end

fun declare_fun name n T = snd o fresh_fun cons name n T
fun declare_free name n T = fresh_fun (cons o pair name) name n T

fun with_fresh_names f ({ctxt, id, syms, typs, funs, extra}: 'a context) =
  let
    fun bind (_, v as (_, T)) t = Logic.all_const T $ Term.absfree v t

    val needs_inferT = equal Term.dummyT orf Term.is_TVar
    val needs_infer = Term.exists_type (Term.exists_subtype needs_inferT)
    fun infer_types ctxt =
      singleton (Type_Infer_Context.infer_types ctxt) #>
      singleton (Proof_Context.standard_term_check_finish ctxt)
    fun infer ctxt t = if needs_infer t then infer_types ctxt t else t

    type bindings = (string * (string * typ)) list
    val (t, {ctxt=ctxt', extra=names, ...}: bindings context) =
      f (mk_context ctxt id syms typs funs [])
    val t' = infer ctxt' (fold_rev bind names (HOLogic.mk_Trueprop t))
   
  in ((t', map fst names), mk_context ctxt id syms typs funs extra) end



(* proof parser *)

exception Z3_PARSE of string * SMTLIB2.tree

val desymbolize = Name.desymbolize false o perhaps (try (unprefix "?"))

fun parse_type cx ty Ts =
  (case apply_parsers (get_type_parsers (ctxt_of cx)) (ty, Ts) of
    SOME T => T
  | NONE =>
      (case ty of
        SMTLIB2.Sym name =>
          (case lookup_typ cx name of
            SOME T => T
          | NONE => raise Z3_PARSE ("unknown Z3 type", ty))
      | _ => raise Z3_PARSE ("bad Z3 type format", ty)))

fun parse_term t ts cx =
  (case apply_parsers (get_term_parsers (ctxt_of cx)) (t, ts) of
    SOME u => (u, cx)
  | NONE =>
      (case t of
        SMTLIB2.Sym name =>
          (case lookup_fun cx name of
            SOME u => (Term.list_comb (u, ts), cx)
          | NONE =>
              if null ts then declare_free name (desymbolize name) Term.dummyT cx
              else raise Z3_PARSE ("bad Z3 term", t))
      | _ => raise Z3_PARSE ("bad Z3 term format", t)))

fun type_of cx ty =
  (case try (parse_type cx ty) [] of
    SOME T => T
  | NONE =>
      (case ty of
        SMTLIB2.S (ty' :: tys) => parse_type cx ty' (map (type_of cx) tys)
      | _ => raise Z3_PARSE ("bad Z3 type", ty)))

fun dest_var cx (SMTLIB2.S [SMTLIB2.Sym name, ty]) = (name, (desymbolize name, type_of cx ty))
  | dest_var _ v = raise Z3_PARSE ("bad Z3 quantifier variable format", v)

fun dest_body (SMTLIB2.S (SMTLIB2.Sym "!" :: body :: _)) = dest_body body
  | dest_body body = body

fun dest_binding (SMTLIB2.S [SMTLIB2.Sym name, t]) = (name, Tree t)
  | dest_binding b = raise Z3_PARSE ("bad Z3 let binding format", b)

fun term_of t cx =
  (case t of
    SMTLIB2.S [SMTLIB2.Sym "forall", SMTLIB2.S vars, body] =>
      quant HOLogic.mk_all vars body cx
  | SMTLIB2.S [SMTLIB2.Sym "exists", SMTLIB2.S vars, body] =>
      quant HOLogic.mk_exists vars body cx
  | SMTLIB2.S [SMTLIB2.Sym "let", SMTLIB2.S bindings, body] =>
      with_bindings (map dest_binding bindings) (term_of body) cx
  | SMTLIB2.S (SMTLIB2.Sym "!" :: t :: _) => term_of t cx
  | SMTLIB2.S (f :: args) =>
      cx
      |> fold_map term_of args
      |-> parse_term f
  | SMTLIB2.Sym name =>
      (case lookup_binding cx name of
        Tree u =>
          cx
          |> term_of u
          |-> (fn u' => pair u' o update_binding (name, Term u'))
      | Term u => (u, cx)
      | None => parse_term t [] cx
      | _ => raise Z3_PARSE ("bad Z3 term format", t))
  | _ => parse_term t [] cx)

and quant q vars body cx =
  let val vs = map (dest_var cx) vars
  in
    cx
    |> with_bindings (map (apsnd (Term o Free)) vs) (term_of (dest_body body))
    |>> fold_rev (fn (_, (n, T)) => fn t => q (n, T, t)) vs
  end

fun rule_of (SMTLIB2.Sym name) = rule_of_string name
  | rule_of (SMTLIB2.S (SMTLIB2.Sym "_" :: SMTLIB2.Sym name :: args)) =
      (case (name, args) of
        ("th-lemma", SMTLIB2.Sym kind :: _) => Th_Lemma kind
      | _ => rule_of_string name)
  | rule_of r = raise Z3_PARSE ("bad Z3 proof rule format", r)

fun node_of p cx =
  (case p of
    SMTLIB2.Sym name =>
      (case lookup_binding cx name of
        Proof node => (node, cx)
      | Tree p' =>
          cx
          |> node_of p'
          |-> (fn node => pair node o update_binding (name, Proof node))
      | _ => raise Z3_PARSE ("bad Z3 proof format", p))
  | SMTLIB2.S [SMTLIB2.Sym "let", SMTLIB2.S bindings, p] =>
      with_bindings (map dest_binding bindings) (node_of p) cx
  | SMTLIB2.S (name :: parts) =>
      let
        val (ps, p) = split_last parts
        val r = rule_of name
      in
        cx
        |> fold_map node_of ps
        ||>> with_fresh_names (term_of p)
        ||>> next_id
        |>> (fn ((prems, (t, ns)), id) => mk_node id r prems t ns)
      end
  | _ => raise Z3_PARSE ("bad Z3 proof format", p))

fun dest_name (SMTLIB2.Sym name) = name
  | dest_name t = raise Z3_PARSE ("bad name", t)

fun dest_seq (SMTLIB2.S ts) = ts
  | dest_seq t = raise Z3_PARSE ("bad Z3 proof format", t)

fun parse' (SMTLIB2.S (SMTLIB2.Sym "set-logic" :: _) :: ts) cx = parse' ts cx
  | parse' (SMTLIB2.S [SMTLIB2.Sym "declare-fun", n, tys, ty] :: ts) cx =
      let
        val name = dest_name n
        val Ts = map (type_of cx) (dest_seq tys)
        val T = type_of cx ty
      in parse' ts (declare_fun name (desymbolize name) (Ts ---> T) cx) end
  | parse' (SMTLIB2.S [SMTLIB2.Sym "proof", p] :: _) cx = node_of p cx
  | parse' ts _ = raise Z3_PARSE ("bad Z3 proof declarations", SMTLIB2.S ts)

fun parse_proof typs funs lines ctxt =
  let
    val ts = dest_seq (SMTLIB2.parse lines)
    val (node, cx) = parse' ts (empty_context ctxt typs funs)
  in (node, ctxt_of cx) end
  handle SMTLIB2.PARSE (l, msg) =>
           error ("parsing error at line " ^ string_of_int l ^ ": " ^ msg)
       | Z3_PARSE (msg, t) =>
           error (msg ^ ": " ^ SMTLIB2.str_of t)



(* handling of bound variables *)

fun subst_of tyenv =
  let fun add (ix, (S, T)) = cons (TVar (ix, S), T)
  in Vartab.fold add tyenv [] end

fun substTs_same subst = 
  let val applyT = Same.function (AList.lookup (op =) subst)
  in Term_Subst.map_atypsT_same applyT end

fun subst_types ctxt env bounds t =
  let
    val match = Sign.typ_match (Proof_Context.theory_of ctxt)

    val t' = singleton (Variable.polymorphic ctxt) t
    val patTs = map snd (Term.strip_qnt_vars @{const_name all} t')
    val objTs = map (the o Symtab.lookup env) bounds
    val subst = subst_of (fold match (patTs ~~ objTs) Vartab.empty)
  in Same.commit (Term_Subst.map_types_same (substTs_same subst)) t' end

fun eq_quant (@{const_name HOL.All}, _) (@{const_name HOL.All}, _) = true
  | eq_quant (@{const_name HOL.Ex}, _) (@{const_name HOL.Ex}, _) = true
  | eq_quant _ _ = false

fun opp_quant (@{const_name HOL.All}, _) (@{const_name HOL.Ex}, _) = true
  | opp_quant (@{const_name HOL.Ex}, _) (@{const_name HOL.All}, _) = true
  | opp_quant _ _ = false

fun with_quant pred i (Const q1 $ Abs (_, T1, t1), Const q2 $ Abs (_, T2, t2)) =
      if pred q1 q2 andalso T1 = T2 then
        let val t = Var (("", i), T1)
        in SOME (pairself Term.subst_bound ((t, t1), (t, t2))) end
      else NONE
  | with_quant _ _ _ = NONE

fun dest_quant_pair i (@{term HOL.Not} $ t1, t2) =
      Option.map (apfst HOLogic.mk_not) (with_quant opp_quant i (t1, t2))
  | dest_quant_pair i (t1, t2) = with_quant eq_quant i (t1, t2)

fun dest_quant i t =
  (case dest_quant_pair i (HOLogic.dest_eq (HOLogic.dest_Trueprop t)) of
    SOME (t1, t2) => HOLogic.mk_Trueprop (HOLogic.mk_eq (t1, t2))
  | NONE => raise TERM ("lift_quant", [t]))

fun match_types ctxt pat obj =
  (Vartab.empty, Vartab.empty)
  |> Pattern.first_order_match (Proof_Context.theory_of ctxt) (pat, obj)

fun strip_match ctxt pat i obj =
  (case try (match_types ctxt pat) obj of
    SOME (tyenv, _) => subst_of tyenv
  | NONE => strip_match ctxt pat (i + 1) (dest_quant i obj))

fun dest_all i (Const (@{const_name all}, _) $ (a as Abs (_, T, _))) =
      dest_all (i + 1) (Term.betapply (a, Var (("", i), T)))
  | dest_all i t = (i, t)

fun dest_alls t = dest_all (Term.maxidx_of_term t + 1) t

fun match_rule ctxt env (Z3_Node {bounds=bs', concl=t', ...}) bs t =
  let
    val t'' = singleton (Variable.polymorphic ctxt) t'
    val (i, obj) = dest_alls (subst_types ctxt env bs t)
  in
    (case try (strip_match ctxt (snd (dest_alls t'')) i) obj of
      NONE => NONE
    | SOME subst =>
        let
          val applyT = Same.commit (substTs_same subst)
          val patTs = map snd (Term.strip_qnt_vars @{const_name all} t'')
        in SOME (Symtab.make (bs' ~~ map applyT patTs)) end)
  end



(* linearizing proofs and resolving types of bound variables *)

fun has_step (tab, _) = Inttab.defined tab

fun add_step id rule bounds concl is_fix_step ids (tab, sts) =
  let val step = mk_step id rule ids concl bounds is_fix_step
  in (id, (Inttab.update (id, ()) tab, step :: sts)) end

fun is_fix_rule rule prems =
  member (op =) [Quant_Intro, Nnf_Pos, Nnf_Neg] rule andalso length prems = 1

fun lin_proof ctxt env (Z3_Node {id, rule, prems, concl, bounds}) steps =
  if has_step steps id then (id, steps)
  else
    let
      val t = subst_types ctxt env bounds concl
      val add = add_step id rule bounds t
      fun rec_apply e b = fold_map (lin_proof ctxt e) prems #-> add b
    in
      if is_fix_rule rule prems then
        (case match_rule ctxt env (hd prems) bounds t of
          NONE => rec_apply env false steps
        | SOME env' => rec_apply env' true steps)
      else rec_apply env false steps
    end

fun linearize ctxt node =
  rev (snd (snd (lin_proof ctxt Symtab.empty node (Inttab.empty, []))))



(* overall proof parser *)

fun parse typs funs lines ctxt =
  let val (node, ctxt') = parse_proof typs funs lines ctxt
  in (linearize ctxt' node, ctxt') end

end
