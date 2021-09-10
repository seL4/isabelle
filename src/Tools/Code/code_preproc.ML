(*  Title:      Tools/Code/code_preproc.ML
    Author:     Florian Haftmann, TU Muenchen

Preprocessing code equations into a well-sorted system
in a graph with explicit dependencies.
*)

signature CODE_PREPROC =
sig
  val map_pre: (Proof.context -> Proof.context) -> theory -> theory
  val map_post: (Proof.context -> Proof.context) -> theory -> theory
  val add_functrans: string * (Proof.context -> (thm * bool) list -> (thm * bool) list option) -> theory -> theory
  val del_functrans: string -> theory -> theory
  val simple_functrans: (Proof.context -> thm list -> thm list option)
    -> Proof.context -> (thm * bool) list -> (thm * bool) list option
  val print_codeproc: Proof.context -> unit

  type code_algebra
  type code_graph
  val cert: code_graph -> string -> Code.cert
  val sortargs: code_graph -> string -> sort list
  val all: code_graph -> string list
  val pretty: Proof.context -> code_graph -> Pretty.T
  val obtain: bool -> { ctxt: Proof.context, consts: string list, terms: term list } ->
    { algebra: code_algebra, eqngr: code_graph }
  val dynamic_conv: Proof.context
    -> (code_algebra -> code_graph -> term -> conv) -> conv
  val dynamic_value: Proof.context -> ((term -> term) -> 'a -> 'b)
    -> (code_algebra -> code_graph -> term -> 'a) -> term -> 'b
  val static_conv: { ctxt: Proof.context, consts: string list }
    -> ({ algebra: code_algebra, eqngr: code_graph } -> Proof.context -> term -> conv)
    -> Proof.context -> conv
  val static_value: { ctxt: Proof.context, lift_postproc: ((term -> term) -> 'a -> 'b), consts: string list }
    -> ({ algebra: code_algebra, eqngr: code_graph } -> Proof.context -> term -> 'a)
    -> Proof.context -> term -> 'b

  val trace_none: Context.generic -> Context.generic
  val trace_all: Context.generic -> Context.generic
  val trace_only: string list -> Context.generic -> Context.generic
  val trace_only_ext: string list -> Context.generic -> Context.generic

  val timing: bool Config.T
  val timed: string -> ('a -> Proof.context) -> ('a -> 'b) -> 'a -> 'b
  val timed_exec: string -> (unit -> 'a) -> Proof.context -> 'a
  val timed_conv: string -> (Proof.context -> conv) -> Proof.context -> conv
  val timed_value: string -> (Proof.context -> term -> 'a) -> Proof.context -> term -> 'a
end

structure Code_Preproc : CODE_PREPROC =
struct

(** timing **)

val timing = Attrib.setup_config_bool \<^binding>\<open>code_timing\<close> (K false);

fun timed msg ctxt_of f x =
  if Config.get (ctxt_of x) timing
  then timeap_msg msg f x
  else f x;

fun timed_exec msg f ctxt =
  if Config.get ctxt timing
  then timeap_msg msg f ()
  else f ();

fun timed' msg f ctxt x =
  if Config.get ctxt timing
  then timeap_msg msg (f ctxt) x
  else f ctxt x;

val timed_conv = timed';
val timed_value = timed';



(** preprocessor administration **)

(* theory data *)

datatype thmproc = Thmproc of {
  pre: simpset,
  post: simpset,
  functrans: (string * (serial * (Proof.context -> (thm * bool) list -> (thm * bool) list option))) list
};

fun make_thmproc ((pre, post), functrans) =
  Thmproc { pre = pre, post = post, functrans = functrans };
fun map_thmproc f (Thmproc { pre, post, functrans }) =
  make_thmproc (f ((pre, post), functrans));
fun merge_thmproc (Thmproc { pre = pre1, post = post1, functrans = functrans1 },
  Thmproc { pre = pre2, post = post2, functrans = functrans2 }) =
    let
      val pre = Simplifier.merge_ss (pre1, pre2);
      val post = Simplifier.merge_ss (post1, post2);
      val functrans = AList.merge (op =) (eq_fst (op =)) (functrans1, functrans2)
        handle AList.DUP => error ("Duplicate function transformer");
    in make_thmproc ((pre, post), functrans) end;

structure Code_Preproc_Data = Theory_Data
(
  type T = thmproc;
  val empty = make_thmproc ((Simplifier.empty_ss, Simplifier.empty_ss), []);
  val extend = I;
  val merge = merge_thmproc;
);

fun the_thmproc thy = case Code_Preproc_Data.get thy
 of Thmproc x => x;

fun delete_force msg key xs =
  if AList.defined (op =) xs key then AList.delete (op =) key xs
  else error ("No such " ^ msg ^ ": " ^ quote key);

val map_data = Code_Preproc_Data.map o map_thmproc;

val map_pre_post = map_data o apfst;

fun map_simpset which f thy =
  map_pre_post (which (simpset_map (Proof_Context.init_global thy) f)) thy;
val map_pre = map_simpset apfst;
val map_post = map_simpset apsnd;

fun process_unfold add_del = map_pre o add_del;
fun process_post add_del = map_post o add_del;

fun process_abbrev add_del raw_thm thy =
  let
    val ctxt = Proof_Context.init_global thy;
    val thm = Local_Defs.meta_rewrite_rule ctxt raw_thm;
    val thm_sym = Thm.symmetric thm;
  in
    thy |> map_pre_post (fn (pre, post) =>
      (pre |> simpset_map ctxt (add_del thm_sym),
       post |> simpset_map ctxt (add_del thm)))
  end;

fun add_functrans (name, f) = (map_data o apsnd)
  (AList.update (op =) (name, (serial (), f)));

fun del_functrans name = (map_data o apsnd)
  (delete_force "function transformer" name);


(* algebra of sandwiches: cterm transformations with pending postprocessors *)

fun matches_transitive eq1 eq2 = Thm.rhs_of eq1 aconvc Thm.lhs_of eq2;

fun trans_comb eq1 eq2 =
  (*explicit assertions: evaluation conversion stacks are error-prone*)
  if Thm.is_reflexive eq1 then (\<^assert> (matches_transitive eq1 eq2); eq2)
  else if Thm.is_reflexive eq2 then (\<^assert> (matches_transitive eq1 eq2); eq1)
  else Thm.transitive eq1 eq2;

fun trans_conv_rule conv eq = trans_comb eq (conv (Thm.rhs_of eq));

structure Sandwich : sig
  type T = Proof.context -> cterm -> (Proof.context -> thm -> thm) * cterm;
  val chain: T -> T -> T
  val lift: (Proof.context -> cterm -> (Proof.context -> cterm -> thm) * thm) -> T
  val conversion: T -> (Proof.context -> term -> conv) -> Proof.context -> conv;
  val computation: T -> ((term -> term) -> 'a -> 'b) ->
    (Proof.context -> term -> 'a) -> Proof.context -> term -> 'b;
end = struct

type T = Proof.context -> cterm -> (Proof.context -> thm -> thm) * cterm;

fun chain sandwich2 sandwich1 ctxt =
  sandwich1 ctxt
  ##>> sandwich2 ctxt
  #>> (fn (f, g) => fn ctxt => f ctxt o g ctxt);

fun lift conv_sandwhich ctxt ct =
  let
    val (postproc_conv, eq) = conv_sandwhich ctxt ct;
    fun potentail_trans_comb eq1 eq2 =
      if matches_transitive eq1 eq2 then trans_comb eq1 eq2 else eq2;
        (*weakened protocol for plain term evaluation*)
  in (fn ctxt => trans_conv_rule (postproc_conv ctxt) o potentail_trans_comb eq, Thm.rhs_of eq) end;

fun conversion sandwich conv ctxt ct =
  let
    val (postproc, ct') = sandwich ctxt ct;
    val thm = conv ctxt (Thm.term_of ct') ct';
    val thm' = postproc ctxt thm;
  in thm' end;

fun computation sandwich lift_postproc eval ctxt t =
  let
    val (postproc, ct') = sandwich ctxt (Thm.cterm_of ctxt t);
    val result = eval ctxt (Thm.term_of ct');
    val result' = lift_postproc
      (Thm.term_of o Thm.rhs_of o postproc ctxt o Thm.reflexive o Thm.cterm_of ctxt)
      result
  in result' end;

end;


(* post- and preprocessing *)

fun normalized_tfrees_sandwich ctxt ct =
  let
    val t = Thm.term_of ct;
    val vs_original =
      fold_term_types (K (fold_atyps (insert (eq_fst op =) o dest_TFree))) t [];
    val vs_normalized = Name.invent_names Name.context Name.aT (map snd vs_original);
    val normalize =
      map_type_tfree (TFree o the o AList.lookup (op =) (vs_original ~~ vs_normalized));
    val normalization =
      map2 (fn (v, sort) => fn (v', _) => (((v', 0), sort), Thm.ctyp_of ctxt (TFree (v, sort))))
        vs_original vs_normalized;
  in
    if eq_list (eq_fst (op =)) (vs_normalized, vs_original)
    then (K I, ct)
    else
     (K (Thm.instantiate (TVars.make normalization, Vars.empty) o Thm.varifyT_global),
      Thm.cterm_of ctxt (map_types normalize t))
  end;

fun no_variables_sandwich ctxt ct =
  let
    val all_vars = fold_aterms (fn t as Free _ => insert (op aconvc) (Thm.cterm_of ctxt t)
      | t as Var _ => insert (op aconvc) (Thm.cterm_of ctxt t)
      | _ => I) (Thm.term_of ct) [];
    fun apply_beta var thm = Thm.combination thm (Thm.reflexive var)
      |> Conv.fconv_rule (Conv.arg_conv (Conv.try_conv (Thm.beta_conversion false)))
      |> Conv.fconv_rule (Conv.arg1_conv (Thm.beta_conversion false));
  in
    if null all_vars
    then (K I, ct)
    else (K (fold apply_beta all_vars), fold_rev Thm.lambda all_vars ct)
  end;

fun simplifier_conv_sandwich ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    val pre = (#pre o the_thmproc) thy;
    val post = (#post o the_thmproc) thy;
    fun pre_conv ctxt' =
      Simplifier.rewrite (put_simpset pre ctxt')
      #> trans_conv_rule (Axclass.unoverload_conv ctxt')
      #> trans_conv_rule (Thm.eta_conversion);
    fun post_conv ctxt'' =
      Axclass.overload_conv ctxt''
      #> trans_conv_rule (Simplifier.rewrite (put_simpset post ctxt''));
  in
    fn ctxt' => timed_conv "preprocessing term" pre_conv ctxt'
      #> pair (timed_conv "postprocessing term" post_conv)
  end;

fun simplifier_sandwich ctxt =
  Sandwich.lift (simplifier_conv_sandwich ctxt);

fun value_sandwich ctxt =
  normalized_tfrees_sandwich
  |> Sandwich.chain no_variables_sandwich
  |> Sandwich.chain (simplifier_sandwich ctxt);

fun print_codeproc ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    val pre = (#pre o the_thmproc) thy;
    val post = (#post o the_thmproc) thy;
    val functrans = (map fst o #functrans o the_thmproc) thy;
  in
    Pretty.writeln_chunks [
      Pretty.block [
        Pretty.str "preprocessing simpset:",
        Pretty.fbrk,
        Simplifier.pretty_simpset true (put_simpset pre ctxt)
      ],
      Pretty.block [
        Pretty.str "postprocessing simpset:",
        Pretty.fbrk,
        Simplifier.pretty_simpset true (put_simpset post ctxt)
      ],
      Pretty.block (
        Pretty.str "function transformers:"
        :: Pretty.fbrk
        :: (Pretty.fbreaks o map Pretty.str) functrans
      )
    ]
  end;

fun simple_functrans f ctxt eqns = case f ctxt (map fst eqns)
 of SOME thms' => SOME (map (rpair (forall snd eqns)) thms')
  | NONE => NONE;


(** sort algebra and code equation graph types **)

type code_algebra = (sort -> sort) * Sorts.algebra;
type code_graph = ((string * sort) list * Code.cert) Graph.T;

fun get_node eqngr const = Graph.get_node eqngr const
  handle Graph.UNDEF _ => error ("No such constant in code equation graph: " ^ quote const);

fun cert eqngr = snd o get_node eqngr;
fun sortargs eqngr = map snd o fst o get_node eqngr;
fun all eqngr = Graph.keys eqngr;

fun pretty ctxt eqngr =
  let
    val thy = Proof_Context.theory_of ctxt;
  in
    AList.make (snd o Graph.get_node eqngr) (Graph.keys eqngr)
    |> (map o apfst) (Code.string_of_const thy)
    |> sort (string_ord o apply2 fst)
    |> (map o apsnd) (Code.pretty_cert thy)
    |> filter_out (null o snd)
    |> map (fn (s, ps) => (Pretty.block o Pretty.fbreaks) (Pretty.str s :: ps))
    |> Pretty.chunks
  end;


(** simplifier tracing **)

structure Trace_Switch = Generic_Data
(
  type T = string list option;
  val empty = SOME [];
  val extend = I;
  fun merge (NONE, _) = NONE
    | merge (_, NONE) = NONE
    | merge (SOME cs1, SOME cs2) = SOME (Library.merge (op =) (cs1, cs2));
);

val trace_none = Trace_Switch.put (SOME []);

val trace_all = Trace_Switch.put NONE;

fun gen_trace_only prep_const raw_cs context =
  let
    val cs = map (prep_const (Context.theory_of context)) raw_cs;
  in Trace_Switch.put (SOME cs) context end;

val trace_only = gen_trace_only (K I);
val trace_only_ext = gen_trace_only Code.read_const;

fun switch_trace c ctxt =
  let
    val d = Trace_Switch.get (Context.Proof ctxt);
    val switch = case d of NONE => true | SOME cs => member (op =) cs c;
    val _ = if switch
      then tracing ("Preprocessing function equations for "
        ^ Code.string_of_const (Proof_Context.theory_of ctxt) c)
      else ();
  in Config.put simp_trace switch ctxt end;


(** the Waisenhaus algorithm **)

(* auxiliary *)

fun is_proper_class thy = can (Axclass.get_info thy);

fun complete_proper_sort thy =
  Sign.complete_sort thy #> filter (is_proper_class thy);

fun inst_params thy tyco =
  map (fn (c, _) => Axclass.param_of_inst thy (c, tyco))
    o maps (#params o Axclass.get_info thy);


(* data structures *)

datatype const = Fun of string | Inst of class * string;

fun const_ord (Fun c1, Fun c2) = fast_string_ord (c1, c2)
  | const_ord (Inst class_tyco1, Inst class_tyco2) =
      prod_ord fast_string_ord fast_string_ord (class_tyco1, class_tyco2)
  | const_ord (Fun _, Inst _) = LESS
  | const_ord (Inst _, Fun _) = GREATER;

type var = const * int;

structure Vargraph =
  Graph(type key = var val ord = prod_ord const_ord int_ord);

datatype styp = Tyco of string * styp list | Var of var | Free;

fun styp_of c_lhs (Type (tyco, tys)) = Tyco (tyco, map (styp_of c_lhs) tys)
  | styp_of c_lhs (TFree (v, _)) = case c_lhs
     of SOME (c, lhs) => Var (Fun c, find_index (fn (v', _) => v = v') lhs)
      | NONE => Free;

type vardeps_data = ((string * styp list) list * class list) Vargraph.T
  * (((string * sort) list * Code.cert) Symtab.table
    * (class * string) list);

val empty_vardeps_data : vardeps_data =
  (Vargraph.empty, (Symtab.empty, []));


(* retrieving equations and instances from the background context *)

fun obtain_eqns ctxt eqngr c =
  case try (Graph.get_node eqngr) c
   of SOME (lhs, cert) => ((lhs, []), cert)
    | NONE => let
        val thy = Proof_Context.theory_of ctxt;
        val functrans = (map (fn (_, (_, f)) => f ctxt)
          o #functrans o the_thmproc) thy;
        val cert = Code.get_cert (switch_trace c ctxt) functrans c;
        val (lhs, rhss) =
          Code.typargs_deps_of_cert thy cert;
      in ((lhs, rhss), cert) end;

fun obtain_instance ctxt arities (inst as (class, tyco)) =
  case AList.lookup (op =) arities inst
   of SOME classess => (classess, ([], []))
    | NONE => let
        val thy = Proof_Context.theory_of ctxt;
        val all_classes = complete_proper_sort thy [class];
        val super_classes = remove (op =) class all_classes;
        val classess =
          map (complete_proper_sort thy)
            (Proof_Context.arity_sorts ctxt tyco [class]);
        val inst_params = inst_params thy tyco all_classes;
      in (classess, (super_classes, inst_params)) end;


(* computing instantiations *)

fun add_classes ctxt arities eqngr c_k new_classes vardeps_data =
  let
    val (styps, old_classes) = Vargraph.get_node (fst vardeps_data) c_k;
    val diff_classes = new_classes |> subtract (op =) old_classes;
  in if null diff_classes then vardeps_data
  else let
    val c_ks = Vargraph.immediate_succs (fst vardeps_data) c_k |> insert (op =) c_k;
  in
    vardeps_data
    |> (apfst o Vargraph.map_node c_k o apsnd) (append diff_classes)
    |> fold (fn styp => fold (ensure_typmatch_inst ctxt arities eqngr styp) new_classes) styps
    |> fold (fn c_k => add_classes ctxt arities eqngr c_k diff_classes) c_ks
  end end
and add_styp ctxt arities eqngr c_k new_tyco_styps vardeps_data =
  let
    val (old_tyco_stypss, classes) = Vargraph.get_node (fst vardeps_data) c_k;
  in if member (op =) old_tyco_stypss new_tyco_styps then vardeps_data
  else
    vardeps_data
    |> (apfst o Vargraph.map_node c_k o apfst) (cons new_tyco_styps)
    |> fold (ensure_typmatch_inst ctxt arities eqngr new_tyco_styps) classes
  end
and add_dep ctxt arities eqngr c_k c_k' vardeps_data =
  let
    val (_, classes) = Vargraph.get_node (fst vardeps_data) c_k;
  in
    vardeps_data
    |> add_classes ctxt arities eqngr c_k' classes
    |> apfst (Vargraph.add_edge (c_k, c_k'))
  end
and ensure_typmatch_inst ctxt arities eqngr (tyco, styps) class vardeps_data =
  if can (Proof_Context.arity_sorts ctxt tyco) [class]
  then vardeps_data
    |> ensure_inst ctxt arities eqngr (class, tyco)
    |> fold_index (fn (k, styp) =>
         ensure_typmatch ctxt arities eqngr styp (Inst (class, tyco), k)) styps
  else vardeps_data (*permissive!*)
and ensure_inst ctxt arities eqngr (inst as (class, tyco)) (vardeps_data as (_, (_, insts))) =
  if member (op =) insts inst then vardeps_data
  else let
    val (classess, (super_classes, inst_params)) =
      obtain_instance ctxt arities inst;
  in
    vardeps_data
    |> (apsnd o apsnd) (insert (op =) inst)
    |> fold_index (fn (k, _) =>
         apfst (Vargraph.new_node ((Inst (class, tyco), k), ([] ,[])))) classess
    |> fold (fn super_class => ensure_inst ctxt arities eqngr (super_class, tyco)) super_classes
    |> fold (ensure_fun ctxt arities eqngr) inst_params
    |> fold_index (fn (k, classes) =>
         add_classes ctxt arities eqngr (Inst (class, tyco), k) classes
         #> fold (fn super_class =>
             add_dep ctxt arities eqngr (Inst (super_class, tyco), k)
             (Inst (class, tyco), k)) super_classes
         #> fold (fn inst_param =>
             add_dep ctxt arities eqngr (Fun inst_param, k)
             (Inst (class, tyco), k)
             ) inst_params
         ) classess
  end
and ensure_typmatch ctxt arities eqngr (Tyco tyco_styps) c_k vardeps_data =
      vardeps_data
      |> add_styp ctxt arities eqngr c_k tyco_styps
  | ensure_typmatch ctxt arities eqngr (Var c_k') c_k vardeps_data =
      vardeps_data
      |> add_dep ctxt arities eqngr c_k c_k'
  | ensure_typmatch ctxt arities eqngr Free c_k vardeps_data =
      vardeps_data
and ensure_rhs ctxt arities eqngr (c', styps) vardeps_data =
  vardeps_data
  |> ensure_fun ctxt arities eqngr c'
  |> fold_index (fn (k, styp) =>
       ensure_typmatch ctxt arities eqngr styp (Fun c', k)) styps
and ensure_fun ctxt arities eqngr c (vardeps_data as (_, (eqntab, _))) =
  if Symtab.defined eqntab c then vardeps_data
  else let
    val ((lhs, rhss), eqns) = obtain_eqns ctxt eqngr c;
    val rhss' = (map o apsnd o map) (styp_of (SOME (c, lhs))) rhss;
  in
    vardeps_data
    |> (apsnd o apfst) (Symtab.update_new (c, (lhs, eqns)))
    |> fold_index (fn (k, _) =>
         apfst (Vargraph.new_node ((Fun c, k), ([] ,[])))) lhs
    |> fold_index (fn (k, (_, sort)) => add_classes ctxt arities eqngr (Fun c, k)
         (complete_proper_sort (Proof_Context.theory_of ctxt) sort)) lhs
    |> fold (ensure_rhs ctxt arities eqngr) rhss'
  end;


(* applying instantiations *)

fun dicts_of ctxt (proj_sort, algebra) (T, sort) =
  let
    val thy = Proof_Context.theory_of ctxt;
    fun class_relation _ (x, _) _ = x;
    fun type_constructor (tyco, _) xs class =
      inst_params thy tyco (Sorts.complete_sort algebra [class])
        @ (maps o maps) fst xs;
    fun type_variable (TFree (_, sort)) = map (pair []) (proj_sort sort);
  in
    flat (Sorts.of_sort_derivation algebra
      { class_relation = K class_relation, type_constructor = type_constructor,
        type_variable = type_variable } (T, proj_sort sort)
       handle Sorts.CLASS_ERROR _ => [] (*permissive!*))
  end;

fun add_arity ctxt vardeps (class, tyco) =
  AList.default (op =) ((class, tyco),
    map_range (fn k => (snd o Vargraph.get_node vardeps) (Inst (class, tyco), k))
      (Sign.arity_number (Proof_Context.theory_of ctxt) tyco));

fun add_cert ctxt vardeps (c, (proto_lhs, proto_cert)) (rhss, eqngr) =
  if can (Graph.get_node eqngr) c then (rhss, eqngr)
  else let
    val thy = Proof_Context.theory_of ctxt;
    val lhs = map_index (fn (k, (v, _)) =>
      (v, snd (Vargraph.get_node vardeps (Fun c, k)))) proto_lhs;
    val cert = proto_cert
      |> Code.constrain_cert thy (map (Sign.minimize_sort thy o snd) lhs)
      |> Code.conclude_cert;
    val (vs, rhss') = Code.typargs_deps_of_cert thy cert;
    val eqngr' = Graph.new_node (c, (vs, cert)) eqngr;
  in (map (pair c) rhss' @ rhss, eqngr') end;

fun extend_arities_eqngr raw_ctxt cs ts (arities, (eqngr : code_graph)) =
  let
    val thy = Proof_Context.theory_of raw_ctxt;
    val {pre, ...} = the_thmproc thy;
    val ctxt = put_simpset pre raw_ctxt;
    val cs_rhss = (fold o fold_aterms) (fn Const (c_ty as (c, _)) =>
      insert (op =) (c, (map (styp_of NONE) o Sign.const_typargs thy) c_ty) | _ => I) ts [];
    val (vardeps, (eqntab, insts)) = empty_vardeps_data
      |> fold (ensure_fun ctxt arities eqngr) cs
      |> fold (ensure_rhs ctxt arities eqngr) cs_rhss;
    val arities' = fold (add_arity ctxt vardeps) insts arities;
    val algebra = Sorts.subalgebra (Context.Theory thy) (is_proper_class thy)
      (AList.lookup (op =) arities') (Sign.classes_of thy);
    val (rhss, eqngr') = Symtab.fold (add_cert ctxt vardeps) eqntab ([], eqngr);
    fun deps_of (c, rhs) = c :: maps (dicts_of ctxt algebra)
      (rhs ~~ sortargs eqngr' c);
    val eqngr'' = fold (fn (c, rhs) => fold
      (curry Graph.add_edge c) (deps_of rhs)) rhss eqngr';
  in (algebra, (arities', eqngr'')) end;


(** store for preprocessed arities and code equations **)

structure Wellsorted = Code_Data
(
  type T = ((string * class) * sort list) list * code_graph;
  val empty = ([], Graph.empty);
);


(** retrieval and evaluation interfaces **)

(*
  naming conventions
  * evaluator "eval" is either
    * conversion "conv"
    * value computation "comp"
  * "evaluation" is a lifting of an evaluator
*)

fun obtain ignore_cache =
  timed "preprocessing equations" #ctxt (fn { ctxt, consts, terms } =>
    apsnd snd (Wellsorted.change_yield
    (if ignore_cache then NONE else SOME (Proof_Context.theory_of ctxt))
    (extend_arities_eqngr ctxt consts terms)))
  #> (fn (algebra, eqngr) => { algebra = algebra, eqngr = eqngr });

fun dynamic_evaluation eval ctxt t =
  let
    val consts = fold_aterms
      (fn Const (c, _) => insert (op =) c | _ => I) t [];
    val { algebra, eqngr } = obtain false { ctxt = ctxt, consts = consts, terms = [t] };
  in eval algebra eqngr t end;

fun static_evaluation ctxt consts eval =
  eval (obtain true { ctxt = ctxt, consts = consts, terms = [] });

fun dynamic_conv ctxt conv =
  Sandwich.conversion (value_sandwich ctxt)
    (dynamic_evaluation conv) ctxt;

fun dynamic_value ctxt lift_postproc evaluator =
  Sandwich.computation (value_sandwich ctxt) lift_postproc
    (dynamic_evaluation evaluator) ctxt;

fun static_conv { ctxt, consts } conv =
  Sandwich.conversion (value_sandwich ctxt)
    (static_evaluation ctxt consts conv);

fun static_value { ctxt, lift_postproc, consts } comp =
  Sandwich.computation (value_sandwich ctxt) lift_postproc
    (static_evaluation ctxt consts comp);


(** setup **)

val _ = Theory.setup (
  let
    fun mk_attribute f = Thm.declaration_attribute (fn thm => Context.mapping (f thm) I);
    fun add_del_attribute_parser process =
      Attrib.add_del (mk_attribute (process Simplifier.add_simp))
        (mk_attribute (process Simplifier.del_simp));
  in
    Attrib.setup \<^binding>\<open>code_unfold\<close> (add_del_attribute_parser process_unfold)
      "preprocessing equations for code generator"
    #> Attrib.setup \<^binding>\<open>code_post\<close> (add_del_attribute_parser process_post)
      "postprocessing equations for code generator"
    #> Attrib.setup \<^binding>\<open>code_abbrev\<close> (add_del_attribute_parser process_abbrev)
      "post- and preprocessing equations for code generator"
    #> Attrib.setup \<^binding>\<open>code_preproc_trace\<close>
      ((Scan.lift (Args.$$$ "off" >> K trace_none)
      || (Scan.lift (Args.$$$ "only" |-- Args.colon |-- Scan.repeat1 Parse.term))
         >> trace_only_ext
      || Scan.succeed trace_all)
      >> (Thm.declaration_attribute o K)) "tracing of the code generator preprocessor"
  end);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_codeproc\<close> "print code preprocessor setup"
    (Scan.succeed (Toplevel.keep (print_codeproc o Toplevel.context_of)));

end; (*struct*)
