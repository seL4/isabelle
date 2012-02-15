(*  Title:      Tools/Code/code_preproc.ML
    Author:     Florian Haftmann, TU Muenchen

Preprocessing code equations into a well-sorted system
in a graph with explicit dependencies.
*)

signature CODE_PREPROC =
sig
  val map_pre: (simpset -> simpset) -> theory -> theory
  val map_post: (simpset -> simpset) -> theory -> theory
  val add_unfold: thm -> theory -> theory
  val add_functrans: string * (theory -> (thm * bool) list -> (thm * bool) list option) -> theory -> theory
  val del_functrans: string -> theory -> theory
  val simple_functrans: (theory -> thm list -> thm list option)
    -> theory -> (thm * bool) list -> (thm * bool) list option
  val preprocess_functrans: theory -> (thm * bool) list -> (thm * bool) list
  val print_codeproc: theory -> unit

  type code_algebra
  type code_graph
  val cert: code_graph -> string -> Code.cert
  val sortargs: code_graph -> string -> sort list
  val all: code_graph -> string list
  val pretty: theory -> code_graph -> Pretty.T
  val obtain: bool -> theory -> string list -> term list -> code_algebra * code_graph
  val dynamic_conv: theory
    -> (code_algebra -> code_graph -> (string * sort) list -> term -> conv) -> conv
  val dynamic_value: theory -> ((term -> term) -> 'a -> 'a)
    -> (code_algebra -> code_graph -> (string * sort) list -> term -> 'a) -> term -> 'a
  val static_conv: theory -> string list
    -> (code_algebra -> code_graph -> (string * sort) list -> term -> conv) -> conv
  val static_value: theory -> ((term -> term) -> 'a -> 'a) -> string list
    -> (code_algebra -> code_graph -> (string * sort) list -> term -> 'a) -> term -> 'a

  val setup: theory -> theory
end

structure Code_Preproc : CODE_PREPROC =
struct

(** preprocessor administration **)

(* theory data *)

datatype thmproc = Thmproc of {
  pre: simpset,
  post: simpset,
  functrans: (string * (serial * (theory -> (thm * bool) list -> (thm * bool) list option))) list
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
val map_pre = map_pre_post o apfst;
val map_post = map_pre_post o apsnd;

val add_unfold = map_pre o Simplifier.add_simp;
val del_unfold = map_pre o Simplifier.del_simp;
val add_post = map_post o Simplifier.add_simp;
val del_post = map_post o Simplifier.del_simp;

fun add_code_abbrev raw_thm thy =
  let
    val thm = Local_Defs.meta_rewrite_rule (Proof_Context.init_global thy) raw_thm;
    val thm_sym = Thm.symmetric thm;
  in
    thy |> map_pre_post (fn (pre, post) =>
      (pre |> Simplifier.add_simp thm_sym, post |> Simplifier.add_simp thm))
  end;

fun add_functrans (name, f) = (map_data o apsnd)
  (AList.update (op =) (name, (serial (), f)));

fun del_functrans name = (map_data o apsnd)
  (delete_force "function transformer" name);


(* post- and preprocessing *)

fun no_variables_conv conv ct =
  let
    val cert = Thm.cterm_of (Thm.theory_of_cterm ct);
    val all_vars = fold_aterms (fn t as Free _ => insert (op aconvc) (cert t)
      | t as Var _ => insert (op aconvc) (cert t)
      | _ => I) (Thm.term_of ct) [];
    fun apply_beta var thm = Thm.combination thm (Thm.reflexive var)
      |> Conv.fconv_rule (Conv.arg_conv (Conv.try_conv (Thm.beta_conversion false)))
      |> Conv.fconv_rule (Conv.arg1_conv (Thm.beta_conversion false));
  in
    ct
    |> fold_rev Thm.lambda all_vars
    |> conv
    |> fold apply_beta all_vars
  end;

fun trans_conv_rule conv thm = Thm.transitive thm ((conv o Thm.rhs_of) thm);

fun eqn_conv conv ct =
  let
    fun lhs_conv ct = if can Thm.dest_comb ct
      then Conv.combination_conv lhs_conv conv ct
      else Conv.all_conv ct;
  in Conv.combination_conv (Conv.arg_conv lhs_conv) conv ct end;

val rewrite_eqn = Conv.fconv_rule o eqn_conv o Simplifier.rewrite;

fun term_of_conv thy conv =
  Thm.cterm_of thy
  #> conv
  #> Thm.prop_of
  #> Logic.dest_equals
  #> snd;

fun term_of_conv_resubst thy conv t =
  let
    val all_vars = fold_aterms (fn t as Free _ => insert (op aconv) t
      | t as Var _ => insert (op aconv) t
      | _ => I) t [];
    val resubst = curry (Term.betapplys o swap) all_vars;
  in (resubst, term_of_conv thy conv (fold_rev lambda all_vars t)) end;


fun preprocess_functrans thy = 
  let
    val functrans = (map (fn (_, (_, f)) => f thy) o #functrans
      o the_thmproc) thy;
  in perhaps (perhaps_loop (perhaps_apply functrans)) end;

fun preprocess thy =
  let
    val ctxt = Proof_Context.init_global thy;
    val pre = (Simplifier.global_context thy o #pre o the_thmproc) thy;
  in
    preprocess_functrans thy
    #> (map o apfst) (singleton (Variable.trade (K (map (rewrite_eqn pre))) ctxt)) 
  end;

fun preprocess_conv thy =
  let
    val pre = (Simplifier.global_context thy o #pre o the_thmproc) thy;
  in
    Simplifier.rewrite pre
    #> trans_conv_rule (AxClass.unoverload_conv thy)
  end;

fun preprocess_term thy = term_of_conv_resubst thy (preprocess_conv thy);

fun postprocess_conv thy =
  let
    val post = (Simplifier.global_context thy o #post o the_thmproc) thy;
  in
    AxClass.overload_conv thy
    #> trans_conv_rule (Simplifier.rewrite post)
  end;

fun postprocess_term thy = term_of_conv thy (postprocess_conv thy);

fun print_codeproc thy =
  let
    val ctxt = Proof_Context.init_global thy;
    val pre = (#pre o the_thmproc) thy;
    val post = (#post o the_thmproc) thy;
    val functrans = (map fst o #functrans o the_thmproc) thy;
  in
    (Pretty.writeln o Pretty.chunks) [
      Pretty.block [
        Pretty.str "preprocessing simpset:",
        Pretty.fbrk,
        Simplifier.pretty_ss ctxt pre
      ],
      Pretty.block [
        Pretty.str "postprocessing simpset:",
        Pretty.fbrk,
        Simplifier.pretty_ss ctxt post
      ],
      Pretty.block (
        Pretty.str "function transformers:"
        :: Pretty.fbrk
        :: (Pretty.fbreaks o map Pretty.str) functrans
      )
    ]
  end;

fun simple_functrans f thy eqns = case f thy (map fst eqns)
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

fun pretty thy eqngr =
  AList.make (snd o Graph.get_node eqngr) (Graph.keys eqngr)
  |> (map o apfst) (Code.string_of_const thy)
  |> sort (string_ord o pairself fst)
  |> map (fn (s, cert) => (Pretty.block o Pretty.fbreaks) (Pretty.str s :: Code.pretty_cert thy cert))
  |> Pretty.chunks;


(** the Waisenhaus algorithm **)

(* auxiliary *)

fun is_proper_class thy = can (AxClass.get_info thy);

fun complete_proper_sort thy =
  Sign.complete_sort thy #> filter (is_proper_class thy);

fun inst_params thy tyco =
  map (fn (c, _) => AxClass.param_of_inst thy (c, tyco))
    o maps (#params o AxClass.get_info thy);


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

fun obtain_eqns thy eqngr c =
  case try (Graph.get_node eqngr) c
   of SOME (lhs, cert) => ((lhs, []), cert)
    | NONE => let
        val cert = Code.get_cert thy (preprocess thy) c;
        val (lhs, rhss) = Code.typargs_deps_of_cert thy cert;
      in ((lhs, rhss), cert) end;

fun obtain_instance thy arities (inst as (class, tyco)) =
  case AList.lookup (op =) arities inst
   of SOME classess => (classess, ([], []))
    | NONE => let
        val all_classes = complete_proper_sort thy [class];
        val super_classes = remove (op =) class all_classes;
        val classess = map (complete_proper_sort thy)
          (Sign.arity_sorts thy tyco [class]);
        val inst_params = inst_params thy tyco all_classes;
      in (classess, (super_classes, inst_params)) end;


(* computing instantiations *)

fun add_classes thy arities eqngr c_k new_classes vardeps_data =
  let
    val (styps, old_classes) = Vargraph.get_node (fst vardeps_data) c_k;
    val diff_classes = new_classes |> subtract (op =) old_classes;
  in if null diff_classes then vardeps_data
  else let
    val c_ks = Vargraph.immediate_succs (fst vardeps_data) c_k |> insert (op =) c_k;
  in
    vardeps_data
    |> (apfst o Vargraph.map_node c_k o apsnd) (append diff_classes)
    |> fold (fn styp => fold (ensure_typmatch_inst thy arities eqngr styp) new_classes) styps
    |> fold (fn c_k => add_classes thy arities eqngr c_k diff_classes) c_ks
  end end
and add_styp thy arities eqngr c_k new_tyco_styps vardeps_data =
  let
    val (old_tyco_stypss, classes) = Vargraph.get_node (fst vardeps_data) c_k;
  in if member (op =) old_tyco_stypss new_tyco_styps then vardeps_data
  else
    vardeps_data
    |> (apfst o Vargraph.map_node c_k o apfst) (cons new_tyco_styps)
    |> fold (ensure_typmatch_inst thy arities eqngr new_tyco_styps) classes
  end
and add_dep thy arities eqngr c_k c_k' vardeps_data =
  let
    val (_, classes) = Vargraph.get_node (fst vardeps_data) c_k;
  in
    vardeps_data
    |> add_classes thy arities eqngr c_k' classes
    |> apfst (Vargraph.add_edge (c_k, c_k'))
  end
and ensure_typmatch_inst thy arities eqngr (tyco, styps) class vardeps_data =
  if can (Sign.arity_sorts thy tyco) [class]
  then vardeps_data
    |> ensure_inst thy arities eqngr (class, tyco)
    |> fold_index (fn (k, styp) =>
         ensure_typmatch thy arities eqngr styp (Inst (class, tyco), k)) styps
  else vardeps_data (*permissive!*)
and ensure_inst thy arities eqngr (inst as (class, tyco)) (vardeps_data as (_, (_, insts))) =
  if member (op =) insts inst then vardeps_data
  else let
    val (classess, (super_classes, inst_params)) =
      obtain_instance thy arities inst;
  in
    vardeps_data
    |> (apsnd o apsnd) (insert (op =) inst)
    |> fold_index (fn (k, _) =>
         apfst (Vargraph.new_node ((Inst (class, tyco), k), ([] ,[])))) classess
    |> fold (fn super_class => ensure_inst thy arities eqngr (super_class, tyco)) super_classes
    |> fold (ensure_fun thy arities eqngr) inst_params
    |> fold_index (fn (k, classes) =>
         add_classes thy arities eqngr (Inst (class, tyco), k) classes
         #> fold (fn super_class =>
             add_dep thy arities eqngr (Inst (super_class, tyco), k)
             (Inst (class, tyco), k)) super_classes
         #> fold (fn inst_param =>
             add_dep thy arities eqngr (Fun inst_param, k)
             (Inst (class, tyco), k)
             ) inst_params
         ) classess
  end
and ensure_typmatch thy arities eqngr (Tyco tyco_styps) c_k vardeps_data =
      vardeps_data
      |> add_styp thy arities eqngr c_k tyco_styps
  | ensure_typmatch thy arities eqngr (Var c_k') c_k vardeps_data =
      vardeps_data
      |> add_dep thy arities eqngr c_k c_k'
  | ensure_typmatch thy arities eqngr Free c_k vardeps_data =
      vardeps_data
and ensure_rhs thy arities eqngr (c', styps) vardeps_data =
  vardeps_data
  |> ensure_fun thy arities eqngr c'
  |> fold_index (fn (k, styp) =>
       ensure_typmatch thy arities eqngr styp (Fun c', k)) styps
and ensure_fun thy arities eqngr c (vardeps_data as (_, (eqntab, _))) =
  if Symtab.defined eqntab c then vardeps_data
  else let
    val ((lhs, rhss), eqns) = obtain_eqns thy eqngr c;
    val rhss' = (map o apsnd o map) (styp_of (SOME (c, lhs))) rhss;
  in
    vardeps_data
    |> (apsnd o apfst) (Symtab.update_new (c, (lhs, eqns)))
    |> fold_index (fn (k, _) =>
         apfst (Vargraph.new_node ((Fun c, k), ([] ,[])))) lhs
    |> fold_index (fn (k, (_, sort)) =>
         add_classes thy arities eqngr (Fun c, k) (complete_proper_sort thy sort)) lhs
    |> fold (ensure_rhs thy arities eqngr) rhss'
  end;


(* applying instantiations *)

fun dicts_of thy (proj_sort, algebra) (T, sort) =
  let
    fun class_relation (x, _) _ = x;
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

fun add_arity thy vardeps (class, tyco) =
  AList.default (op =) ((class, tyco),
    map_range (fn k => (snd o Vargraph.get_node vardeps) (Inst (class, tyco), k))
      (Sign.arity_number thy tyco));

fun add_cert thy vardeps (c, (proto_lhs, proto_cert)) (rhss, eqngr) =
  if can (Graph.get_node eqngr) c then (rhss, eqngr)
  else let
    val lhs = map_index (fn (k, (v, _)) =>
      (v, snd (Vargraph.get_node vardeps (Fun c, k)))) proto_lhs;
    val cert = Code.constrain_cert thy (map (Sign.minimize_sort thy o snd) lhs) proto_cert;
    val (vs, rhss') = Code.typargs_deps_of_cert thy cert;
    val eqngr' = Graph.new_node (c, (vs, cert)) eqngr;
  in (map (pair c) rhss' @ rhss, eqngr') end;

fun extend_arities_eqngr thy cs ts (arities, (eqngr : code_graph)) =
  let
    val cs_rhss = (fold o fold_aterms) (fn Const (c_ty as (c, _)) =>
      insert (op =) (c, (map (styp_of NONE) o Sign.const_typargs thy) c_ty) | _ => I) ts [];
    val (vardeps, (eqntab, insts)) = empty_vardeps_data
      |> fold (ensure_fun thy arities eqngr) cs
      |> fold (ensure_rhs thy arities eqngr) cs_rhss;
    val arities' = fold (add_arity thy vardeps) insts arities;
    val algebra = Sorts.subalgebra (Syntax.init_pretty_global thy) (is_proper_class thy)
      (AList.lookup (op =) arities') (Sign.classes_of thy);
    val (rhss, eqngr') = Symtab.fold (add_cert thy vardeps) eqntab ([], eqngr);
    fun deps_of (c, rhs) = c :: maps (dicts_of thy algebra)
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

fun obtain ignore_cache thy consts ts = apsnd snd
  (Wellsorted.change_yield (if ignore_cache then NONE else SOME thy) (extend_arities_eqngr thy consts ts));

fun dest_cterm ct = let val t = Thm.term_of ct in (Term.add_tfrees t [], t) end;

fun dynamic_conv thy conv = no_variables_conv (fn ct =>
  let
    val thm1 = preprocess_conv thy ct;
    val ct' = Thm.rhs_of thm1;
    val (vs', t') = dest_cterm ct';
    val consts = fold_aterms
      (fn Const (c, _) => insert (op =) c | _ => I) t' [];
    val (algebra', eqngr') = obtain false thy consts [t'];
    val thm2 = conv algebra' eqngr' vs' t' ct';
    val thm3 = postprocess_conv thy (Thm.rhs_of thm2);
  in
    Thm.transitive thm1 (Thm.transitive thm2 thm3) handle THM _ =>
      error ("could not construct evaluation proof:\n"
      ^ (cat_lines o map (Display.string_of_thm_global thy)) [thm1, thm2, thm3])
  end);

fun dynamic_value thy postproc evaluator t =
  let
    val (resubst, t') = preprocess_term thy t;
    val vs' = Term.add_tfrees t' [];
    val consts = fold_aterms
      (fn Const (c, _) => insert (op =) c | _ => I) t' [];
    val (algebra', eqngr') = obtain false thy consts [t'];
  in
    t'
    |> evaluator algebra' eqngr' vs'
    |> postproc (postprocess_term thy o resubst)
  end;

fun static_conv thy consts conv =
  let
    val (algebra, eqngr) = obtain true thy consts [];
    val conv' = conv algebra eqngr;
  in
    no_variables_conv ((preprocess_conv thy)
      then_conv (fn ct => uncurry conv' (dest_cterm ct) ct)
      then_conv (postprocess_conv thy))
  end;

fun static_value thy postproc consts evaluator =
  let
    val (algebra, eqngr) = obtain true thy consts [];
    val evaluator' = evaluator algebra eqngr;
  in 
    preprocess_term thy
    #-> (fn resubst => fn t => t
      |> evaluator' (Term.add_tfrees t [])
      |> postproc (postprocess_term thy o resubst))
  end;


(** setup **)

val setup = 
  let
    fun mk_attribute f = Thm.declaration_attribute (fn thm => Context.mapping (f thm) I);
    fun add_del_attribute_parser add del =
      Attrib.add_del (mk_attribute add) (mk_attribute del);
  in
    Attrib.setup @{binding code_unfold} (add_del_attribute_parser add_unfold del_unfold)
        "preprocessing equations for code generator"
    #> Attrib.setup @{binding code_post} (add_del_attribute_parser add_post del_post)
        "postprocessing equations for code generator"
    #> Attrib.setup @{binding code_abbrev} (Scan.succeed (mk_attribute add_code_abbrev))
        "post- and preprocessing equations for code generator"
  end;

val _ =
  Outer_Syntax.improper_command "print_codeproc" "print code preprocessor setup"
  Keyword.diag (Scan.succeed
      (Toplevel.no_timing o Toplevel.unknown_theory o Toplevel.keep
        (print_codeproc o Toplevel.theory_of)));

end; (*struct*)
