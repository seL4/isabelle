(*  Title:      Tools/Code/code_preproc.ML
    Author:     Florian Haftmann, TU Muenchen

Preprocessing code equations into a well-sorted system
in a graph with explicit dependencies.
*)

signature CODE_PREPROC =
sig
  val map_pre: (Proof.context -> Proof.context) -> theory -> theory
  val map_post: (Proof.context -> Proof.context) -> theory -> theory
  val add_unfold: thm -> theory -> theory
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
  val obtain: bool -> theory -> string list -> term list -> code_algebra * code_graph
  val dynamic_conv: Proof.context
    -> (code_algebra -> code_graph -> (string * sort) list -> term -> conv) -> conv
  val dynamic_value: Proof.context -> ((term -> term) -> 'a -> 'a)
    -> (code_algebra -> code_graph -> (string * sort) list -> term -> 'a) -> term -> 'a
  val static_conv: Proof.context -> string list
    -> (code_algebra -> code_graph -> Proof.context -> (string * sort) list -> term -> conv)
    -> Proof.context -> conv
  val static_value: Proof.context -> ((term -> term) -> 'a -> 'a) -> string list
    -> (code_algebra -> code_graph -> Proof.context -> (string * sort) list -> term -> 'a)
    -> Proof.context -> term -> 'a

  val setup: theory -> theory
end

structure Code_Preproc : CODE_PREPROC =
struct

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

val add_unfold = map_pre o Simplifier.add_simp;
val del_unfold = map_pre o Simplifier.del_simp;
val add_post = map_post o Simplifier.add_simp;
val del_post = map_post o Simplifier.del_simp;

fun add_code_abbrev raw_thm thy =
  let
    val ctxt = Proof_Context.init_global thy;
    val thm = Local_Defs.meta_rewrite_rule ctxt raw_thm;
    val thm_sym = Thm.symmetric thm;
  in
    thy |> map_pre_post (fn (pre, post) =>
      (pre |> simpset_map ctxt (Simplifier.add_simp thm_sym),
       post |> simpset_map ctxt (Simplifier.add_simp thm)))
  end;

fun add_functrans (name, f) = (map_data o apsnd)
  (AList.update (op =) (name, (serial (), f)));

fun del_functrans name = (map_data o apsnd)
  (delete_force "function transformer" name);


(* post- and preprocessing *)

fun no_variables_conv ctxt conv ct =
  let
    val thy = Proof_Context.theory_of ctxt;
    val cert = Thm.cterm_of thy;
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

fun term_of_conv ctxt conv =
  Thm.cterm_of (Proof_Context.theory_of ctxt)
  #> conv ctxt
  #> Thm.prop_of
  #> Logic.dest_equals
  #> snd;

fun term_of_conv_resubst ctxt conv t =
  let
    val all_vars = fold_aterms (fn t as Free _ => insert (op aconv) t
      | t as Var _ => insert (op aconv) t
      | _ => I) t [];
    val resubst = curry (Term.betapplys o swap) all_vars;
  in (resubst, term_of_conv ctxt conv (fold_rev lambda all_vars t)) end;

fun preprocess_conv ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    val ss = (#pre o the_thmproc) thy;
  in fn ctxt' =>
    Simplifier.rewrite (put_simpset ss ctxt')
    #> trans_conv_rule (Axclass.unoverload_conv (Proof_Context.theory_of ctxt'))
  end;

fun preprocess_term ctxt =
  let
    val conv = preprocess_conv ctxt;
  in fn ctxt' => term_of_conv_resubst ctxt' conv end;

fun postprocess_conv ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    val ss = (#post o the_thmproc) thy;
  in fn ctxt' =>
    Axclass.overload_conv (Proof_Context.theory_of ctxt')
    #> trans_conv_rule (Simplifier.rewrite (put_simpset ss ctxt'))
  end;

fun postprocess_term ctxt =
  let
    val conv = postprocess_conv ctxt;
  in fn ctxt' => term_of_conv ctxt' conv end;

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
        Simplifier.pretty_simpset (put_simpset pre ctxt)
      ],
      Pretty.block [
        Pretty.str "postprocessing simpset:",
        Pretty.fbrk,
        Simplifier.pretty_simpset (put_simpset post ctxt)
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
    |> sort (string_ord o pairself fst)
    |> map (fn (s, cert) => (Pretty.block o Pretty.fbreaks) (Pretty.str s :: Code.pretty_cert thy cert))
    |> Pretty.chunks
  end;


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
        val cert = Code.get_cert thy { functrans = functrans, ss = simpset_of ctxt } c; (*FIXME*)
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
        val classess = map (complete_proper_sort thy)
          (Sign.arity_sorts thy tyco [class]);
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
  if can (Sign.arity_sorts (Proof_Context.theory_of ctxt) tyco) [class]
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
    val algebra = Sorts.subalgebra (Context.pretty_global thy) (is_proper_class thy)
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

fun obtain ignore_cache thy consts ts = apsnd snd
  (Wellsorted.change_yield (if ignore_cache then NONE else SOME thy)
    (extend_arities_eqngr (Proof_Context.init_global thy) consts ts));

fun dest_cterm ct = let val t = Thm.term_of ct in (Term.add_tfrees t [], t) end;

fun dynamic_conv ctxt conv = no_variables_conv ctxt (fn ct =>
  let
    val thm1 = preprocess_conv ctxt ctxt ct;
    val ct' = Thm.rhs_of thm1;
    val (vs', t') = dest_cterm ct';
    val consts = fold_aterms
      (fn Const (c, _) => insert (op =) c | _ => I) t' [];
    val (algebra', eqngr') = obtain false (Proof_Context.theory_of ctxt) consts [t'];
    val thm2 = conv algebra' eqngr' vs' t' ct';
    val thm3 = postprocess_conv ctxt ctxt (Thm.rhs_of thm2);
  in
    Thm.transitive thm1 (Thm.transitive thm2 thm3) handle THM _ =>
      error ("could not construct evaluation proof:\n"
      ^ (cat_lines o map (Display.string_of_thm ctxt)) [thm1, thm2, thm3])
  end);

fun dynamic_value ctxt postproc evaluator t =
  let
    val (resubst, t') = preprocess_term ctxt ctxt t;
    val vs' = Term.add_tfrees t' [];
    val consts = fold_aterms
      (fn Const (c, _) => insert (op =) c | _ => I) t' [];
    val (algebra', eqngr') = obtain false (Proof_Context.theory_of ctxt) consts [t'];
  in
    t'
    |> evaluator algebra' eqngr' vs'
    |> postproc (postprocess_term ctxt ctxt o resubst)
  end;

fun static_conv ctxt consts conv =
  let
    val (algebra, eqngr) = obtain true (Proof_Context.theory_of ctxt) consts [];
    val pre_conv = preprocess_conv ctxt;
    val conv' = conv algebra eqngr;
    val post_conv = postprocess_conv ctxt;
  in fn ctxt' => no_variables_conv ctxt' ((pre_conv ctxt')
    then_conv (fn ct => uncurry (conv' ctxt') (dest_cterm ct) ct)
    then_conv (post_conv ctxt'))
  end;

fun static_value ctxt postproc consts evaluator =
  let
    val (algebra, eqngr) = obtain true (Proof_Context.theory_of ctxt) consts [];
    val preproc = preprocess_term ctxt;
    val evaluator' = evaluator algebra eqngr;
    val postproc' = postprocess_term ctxt;
  in fn ctxt' => 
    preproc ctxt'
    #-> (fn resubst => fn t => t
      |> evaluator' ctxt' (Term.add_tfrees t [])
      |> postproc (postproc' ctxt' o resubst))
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
  Outer_Syntax.improper_command @{command_spec "print_codeproc"} "print code preprocessor setup"
    (Scan.succeed (Toplevel.unknown_context o Toplevel.keep (print_codeproc o Toplevel.context_of)));

end; (*struct*)
