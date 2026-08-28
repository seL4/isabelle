(*  Title:      HOL/Tools/SMT/z3_proof.ML
    Author:     Sascha Boehme, TU Muenchen

Z3 proofs: parsing and abstract syntax tree.
*)

signature Z3_PROOF =
sig
  (*proof rules*)
  datatype z3_rule =
    True_Axiom | Asserted | Goal | Modus_Ponens | Reflexivity | Symmetry | Transitivity |
    Transitivity_Star | Monotonicity | Quant_Intro | Distributivity | And_Elim | Not_Or_Elim |
    Rewrite | Rewrite_Star | Pull_Quant | Pull_Quant_Star | Push_Quant | Elim_Unused_Vars |
    Dest_Eq_Res | Quant_Inst | Hypothesis | Lemma | Unit_Resolution | Iff_True | Iff_False |
    Commutativity | Def_Axiom | Intro_Def | Apply_Def | Iff_Oeq | Nnf_Pos | Nnf_Neg | Nnf_Star |
    Cnf_Star | Skolemize | Modus_Ponens_Oeq | Th_Lemma of string

  val is_assumption: z3_rule -> bool
  val string_of_rule: z3_rule -> string

  (*proofs*)
  datatype z3_step = Z3_Step of {
    id: int,
    rule: z3_rule,
    prems: int list,
    concl: term,
    fixes: string list,
    is_fix_step: bool}

  (*proof parser*)
  val parse: typ Symtab.table -> term Symtab.table -> string list ->
    Proof.context -> z3_step list * Proof.context
end;

structure Z3_Proof: Z3_PROOF =
struct

open SMTLIB_Proof


(* proof rules *)

datatype z3_rule =
  True_Axiom | Asserted | Goal | Modus_Ponens | Reflexivity | Symmetry | Transitivity |
  Transitivity_Star | Monotonicity | Quant_Intro | Distributivity | And_Elim | Not_Or_Elim |
  Rewrite | Rewrite_Star | Pull_Quant | Pull_Quant_Star | Push_Quant | Elim_Unused_Vars |
  Dest_Eq_Res | Quant_Inst | Hypothesis | Lemma | Unit_Resolution | Iff_True | Iff_False |
  Commutativity | Def_Axiom | Intro_Def | Apply_Def | Iff_Oeq | Nnf_Pos | Nnf_Neg | Nnf_Star |
  Cnf_Star | Skolemize | Modus_Ponens_Oeq | Th_Lemma of string
  (* some proof rules include further information that is currently dropped by the parser *)

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

fun is_assumption Asserted = true
  | is_assumption Goal = true
  | is_assumption Hypothesis = true
  | is_assumption Intro_Def = true
  | is_assumption Skolemize = true
  | is_assumption _ = false

fun rule_of_string name =
  (case Symtab.lookup rule_names name of
    SOME rule => rule
  | NONE => error ("unknown Z3 proof rule " ^ quote name))

fun string_of_rule (Th_Lemma kind) = "th-lemma" ^ (if kind = "" then "" else " " ^ kind)
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
  Z3_Node {id = id, rule = rule, prems = prems, concl = concl, bounds = bounds}

fun string_of_node ctxt =
  let
    fun str depth (Z3_Node {id, rule, prems, concl, bounds}) =
      Symbol.spaces (2 * depth) ^
      enclose "{" "}" (commas
        [string_of_int id,
         string_of_rule rule,
         enclose "[" "]" (implode_space bounds),
         Syntax.string_of_term ctxt concl] ^
        cat_lines (map (prefix "\n" o str (depth + 1)) prems))
  in str 0 end

datatype z3_step = Z3_Step of {
  id: int,
  rule: z3_rule,
  prems: int list,
  concl: term,
  fixes: string list,
  is_fix_step: bool}

fun mk_step id rule prems concl fixes is_fix_step =
  Z3_Step {id = id, rule = rule, prems = prems, concl = concl, fixes = fixes,
    is_fix_step = is_fix_step}


(* proof parser *)

fun rule_of (SMTLIB.Sym name) = rule_of_string name
  | rule_of (SMTLIB.S (SMTLIB.Sym "_" :: SMTLIB.Sym name :: args)) =
      (case (name, args) of
        ("th-lemma", SMTLIB.Sym kind :: _) => Th_Lemma kind
      | _ => rule_of_string name)
  | rule_of r = raise SMTLIB_PARSE ("bad Z3 proof rule format", r)

fun node_of p cx =
  (case p of
    SMTLIB.Sym name =>
      (case lookup_binding cx name of
        Proof node => (node, cx)
      | Tree p' =>
          cx
          |> node_of p'
          |-> (fn node => pair node o update_binding (name, Proof node))
      | _ => raise SMTLIB_PARSE ("bad Z3 proof format", p))
  | SMTLIB.S [SMTLIB.Sym "let", SMTLIB.S bindings, p] =>
      with_bindings (map dest_binding bindings) (node_of p) cx
  | SMTLIB.S (name :: parts) =>
      let
        val (ps, p) = split_last parts
        val r = rule_of name
      in
        cx
        |> fold_map node_of ps
        ||>> `(with_fresh_names (term_of p))
        ||>> next_id
        |>> (fn ((prems, (t, ns)), id) => mk_node id r prems t ns)
      end
  | _ => raise SMTLIB_PARSE ("bad Z3 proof format", p))

fun dest_name (SMTLIB.Sym name) = name
  | dest_name t = raise SMTLIB_PARSE ("bad name", t)

fun dest_seq (SMTLIB.S ts) = ts
  | dest_seq t = raise SMTLIB_PARSE ("bad Z3 proof format", t)

fun parse' (SMTLIB.S (SMTLIB.Sym "set-logic" :: _) :: ts) cx = parse' ts cx
  | parse' (SMTLIB.S [SMTLIB.Sym "declare-fun", n, tys, ty] :: ts) cx =
      let
        val name = dest_name n
        val Ts = map (type_of cx) (dest_seq tys)
        val T = type_of cx ty
      in parse' ts (declare_fun name (Ts ---> T) cx) end
  | parse' (SMTLIB.S [SMTLIB.Sym "proof", p] :: _) cx = node_of p cx
  | parse' ts _ = raise SMTLIB_PARSE ("bad Z3 proof declarations", SMTLIB.S ts)

fun parse_proof typs funs lines ctxt =
  let
    val ts = dest_seq (SMTLIB.parse lines)
    val (node, cx) = parse' ts (empty_context ctxt typs funs)
  in (node, ctxt_of cx) end
  handle SMTLIB.PARSE (l, msg) => error ("parsing error at line " ^ string_of_int l ^ ": " ^ msg)
       | SMTLIB_PARSE (msg, t) => error (msg ^ ": " ^ SMTLIB.str_of t)


(* handling of bound variables *)

fun subst_of tyenv =
  let fun add (ix, (S, T)) = cons (TVar (ix, S), T)
  in Vartab.fold add tyenv [] end

fun substTs_same subst =
  let val applyT = Same.function (AList.lookup (op =) subst)
  in Term.map_atyps_same applyT end

fun subst_types ctxt env bounds t =
  let
    val match = Sign.typ_match (Proof_Context.theory_of ctxt)

    fun objT_of bound =
      (case Symtab.lookup env bound of
        SOME objT => objT
      | NONE => raise Fail ("Replaying the proof trace produced by Z3 failed: " ^
          "the bound " ^ quote bound ^ " is undeclared; this indicates a bug in Z3"))

    val t' = singleton (Variable.polymorphic ctxt) t
    val patTs = map snd (Term.strip_qnt_vars \<^const_name>\<open>Pure.all\<close> t')
    val objTs = map objT_of bounds
    val subst = subst_of (fold match (patTs ~~ objTs) Vartab.empty)
  in Term.map_types (substTs_same subst) t' end

fun eq_quant (\<^const_name>\<open>HOL.All\<close>, _) (\<^const_name>\<open>HOL.All\<close>, _) = true
  | eq_quant (\<^const_name>\<open>HOL.Ex\<close>, _) (\<^const_name>\<open>HOL.Ex\<close>, _) = true
  | eq_quant _ _ = false

fun opp_quant (\<^const_name>\<open>HOL.All\<close>, _) (\<^const_name>\<open>HOL.Ex\<close>, _) = true
  | opp_quant (\<^const_name>\<open>HOL.Ex\<close>, _) (\<^const_name>\<open>HOL.All\<close>, _) = true
  | opp_quant _ _ = false

fun with_quant pred i (Const q1 $ Abs (_, T1, t1), Const q2 $ Abs (_, T2, t2)) =
      if pred q1 q2 andalso T1 = T2 then
        let val t = Var (("", i), T1)
        in SOME (apply2 Term.subst_bound ((t, t1), (t, t2))) end
      else NONE
  | with_quant _ _ _ = NONE

fun dest_quant_pair i (\<^term>\<open>HOL.Not\<close> $ t1, t2) =
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

fun dest_all i (Const (\<^const_name>\<open>Pure.all\<close>, _) $ (a as Abs (_, T, _))) =
      dest_all (i + 1) (Term.betapply (a, Var (("", i), T)))
  | dest_all i t = (i, t)

fun dest_alls t = dest_all (Term.maxidx_of_term t + 1) t

fun match_rule ctxt env (Z3_Node {bounds = bs', concl = t', ...}) bs t =
  let
    val t'' = singleton (Variable.polymorphic ctxt) t'
    val (i, obj) = dest_alls (subst_types ctxt env bs t)
  in
    (case try (strip_match ctxt (snd (dest_alls t'')) i) obj of
      NONE => NONE
    | SOME subst =>
        let
          val applyT = Same.commit (substTs_same subst)
          val patTs = map snd (Term.strip_qnt_vars \<^const_name>\<open>Pure.all\<close> t'')
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

end;
