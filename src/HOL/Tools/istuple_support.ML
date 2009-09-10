(*  Title:	HOL/Tools/ntuple_support.ML
    Author:	Thomas Sewell, NICTA

Support for defining instances of tuple-like types and extracting
introduction rules needed by the record package.
*)


signature ISTUPLE_SUPPORT =
sig
  val add_istuple_type: bstring * string list -> (typ * typ) -> theory ->
            (term * theory);
  type tagged_net = ((string * int) * thm) Net.net;

  val get_istuple_intros: theory -> tagged_net;

  val build_tagged_net: string -> thm list -> tagged_net;
  val resolve_from_tagged_net: tagged_net -> int -> tactic;
  val tag_thm_trace: thm list ref;
  val merge_tagged_nets: (tagged_net * tagged_net) -> tagged_net;
end;

structure IsTupleSupport : ISTUPLE_SUPPORT =
struct

val consN = "_NTupleCons";
val defN = "_def";

val istuple_UNIV_I = thm "istuple_UNIV_I";
val istuple_True_simp = thm "istuple_True_simp";

val istuple_intro = thm "isomorphic_tuple.intro";
val istuple_intros = thms "isomorphic_tuple.intros";

val init_intros = thms "tuple_automorphic.intros";

type tagged_net = ((string * int) * thm) Net.net;

(* broadly similar to the use of nets in Tactic.resolve_from_net_tac.
   the tag strings identify which group of theorems a theorem in the
   net belongs to. *)
fun build_tagged_net tag thms = let
    fun add_to_net thm (i, net) =
        (i + 1, Net.insert_term (K false) (concl_of thm, ((tag, i), thm)) net);
    val (n, net) = fold add_to_net thms (0, Net.empty);
  in net end;

val tag_thm_trace = ref ([] : thm list);

(* we check here that only theorems from a single group are being
   selected for unification, and that there are no duplicates. this
   is a good test that the net is doing its job, picking exactly the
   appropriate rules rather than overapproximating. *)
fun tagged_thms_check t xs = let
    val tags = sort_distinct string_ord (map (fst o fst) xs);
    val ids  = sort_distinct int_ord (map (snd o fst) xs);
    val thms = map snd xs;
in
   if length tags > 1
   then (tag_thm_trace := t :: thms;
     raise THM ("tag mismatch " ^ hd tags ^ ", " ^ nth tags 1, 1, t :: thms))
   else if length ids < length xs
   then (tag_thm_trace := t :: thms;
     raise THM ("tag match duplicate id ", 1, t :: thms))
   else ()
end;

fun resolve_from_tagged_net net i t =
  SUBGOAL (fn (prem, i) => let
      val options = Net.unify_term net (Logic.strip_assums_concl prem);
      val sorted  = sort (int_ord o pairself (snd o fst)) options;
      val check   = tagged_thms_check t sorted;
    in resolve_tac (map snd sorted) i end) i t;

val merge_tagged_nets = Net.merge (Thm.eq_thm_prop o pairself snd);

structure IsTupleIntros = TheoryDataFun
(
  type T = tagged_net;
  val empty = build_tagged_net "initial introduction rules" init_intros;
  val copy = I;
  val extend = I;
  val merge = K merge_tagged_nets;
);

val get_istuple_intros = IsTupleIntros.get;

fun do_typedef name repT alphas thy =
  let
    fun get_thms thy name =
      let
        val SOME { Rep_inject=rep_inject, Abs_name=absN, abs_type=absT,
          Abs_inverse=abs_inverse, ...} = Typedef.get_info thy name;
        val rewrite_rule = MetaSimplifier.rewrite_rule [istuple_UNIV_I, istuple_True_simp];
      in (map rewrite_rule [rep_inject, abs_inverse],
            Const (absN, repT --> absT)) end;
  in
    thy
    |> Typecopy.typecopy (Binding.name name, alphas) repT NONE
    |-> (fn (name, _) => `(fn thy => get_thms thy name))
  end;

(* copied from earlier version of HOLogic *)
fun mk_curry t =
  (case Term.fastype_of t of
    T as (Type ("fun", [Type ("*", [A, B]), C])) =>
      Const ("curry", T --> A --> B --> C) $ t
  | _ => raise TERM ("mk_curry: bad body type", [t]));

fun add_istuple_type (name, alphas) (left, right) thy =
let
  val repT = HOLogic.mk_prodT (left, right);

  val (([rep_inject, abs_inverse], abs), typ_thy) =
    thy
    |> do_typedef name repT alphas
    ||> Sign.add_path name;

  val abs_curry = mk_curry abs;
  val consT     = fastype_of abs_curry;
  val consBind  = Binding.name (name ^ consN);
  val cons      = Const (Sign.full_name typ_thy consBind, consT);
  val cons_spec = (name ^ consN ^ defN, Logic.mk_equals (cons, abs_curry));

  val ([cons_def], cdef_thy) =
    typ_thy
    |> Sign.add_consts_i [Syntax.no_syn (consBind, consT)]
    |> PureThy.add_defs false [Thm.no_attributes (apfst Binding.name cons_spec)];

  val istuple = [abs_inverse, cons_def] MRS (rep_inject RS istuple_intro);
  val intros = [istuple] RL istuple_intros;
  val intro_net = build_tagged_net name intros;

  val thm_thy =
    cdef_thy
    |> IsTupleIntros.map (curry merge_tagged_nets intro_net)
    |> Sign.parent_path;
in
  (cons, thm_thy)
end;

end;


