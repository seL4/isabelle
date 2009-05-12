(*  Title:      Tools/code/code_preproc.ML
    Author:     Florian Haftmann, TU Muenchen

Preprocessing code equations into a well-sorted system
in a graph with explicit dependencies.
*)

signature CODE_PREPROC =
sig
  val map_pre: (simpset -> simpset) -> theory -> theory
  val map_post: (simpset -> simpset) -> theory -> theory
  val add_inline: thm -> theory -> theory
  val add_functrans: string * (theory -> (thm * bool) list -> (thm * bool) list option) -> theory -> theory
  val del_functrans: string -> theory -> theory
  val simple_functrans: (theory -> thm list -> thm list option)
    -> theory -> (thm * bool) list -> (thm * bool) list option
  val print_codeproc: theory -> unit

  type code_algebra
  type code_graph
  val eqns: code_graph -> string -> (thm * bool) list
  val typ: code_graph -> string -> (string * sort) list * typ
  val all: code_graph -> string list
  val pretty: theory -> code_graph -> Pretty.T
  val obtain: theory -> string list -> term list -> code_algebra * code_graph
  val eval_conv: theory -> (sort -> sort)
    -> (code_algebra -> code_graph -> (string * sort) list -> term -> cterm -> thm) -> cterm -> thm
  val eval: theory -> (sort -> sort) -> ((term -> term) -> 'a -> 'a)
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

fun mk_thmproc ((pre, post), functrans) =
  Thmproc { pre = pre, post = post, functrans = functrans };
fun map_thmproc f (Thmproc { pre, post, functrans }) =
  mk_thmproc (f ((pre, post), functrans));
fun merge_thmproc (Thmproc { pre = pre1, post = post1, functrans = functrans1 },
  Thmproc { pre = pre2, post = post2, functrans = functrans2 }) =
    let
      val pre = Simplifier.merge_ss (pre1, pre2);
      val post = Simplifier.merge_ss (post1, post2);
      val functrans = AList.merge (op =) (eq_fst (op =)) (functrans1, functrans2);
    in mk_thmproc ((pre, post), functrans) end;

structure Code_Preproc_Data = TheoryDataFun
(
  type T = thmproc;
  val empty = mk_thmproc ((Simplifier.empty_ss, Simplifier.empty_ss), []);
  fun copy spec = spec;
  val extend = copy;
  fun merge pp = merge_thmproc;
);

fun the_thmproc thy = case Code_Preproc_Data.get thy
 of Thmproc x => x;

fun delete_force msg key xs =
  if AList.defined (op =) xs key then AList.delete (op =) key xs
  else error ("No such " ^ msg ^ ": " ^ quote key);

fun map_data f thy =
  thy
  |> Code.purge_data
  |> (Code_Preproc_Data.map o map_thmproc) f;

val map_pre = map_data o apfst o apfst;
val map_post = map_data o apfst o apsnd;

val add_inline = map_pre o MetaSimplifier.add_simp;
val del_inline = map_pre o MetaSimplifier.del_simp;
val add_post = map_post o MetaSimplifier.add_simp;
val del_post = map_post o MetaSimplifier.del_simp;
  
fun add_functrans (name, f) = (map_data o apsnd)
  (AList.update (op =) (name, (serial (), f)));

fun del_functrans name = (map_data o apsnd)
  (delete_force "function transformer" name);


(* post- and preprocessing *)

fun apply_functrans thy c _ [] = []
  | apply_functrans thy c [] eqns = eqns
  | apply_functrans thy c functrans eqns = eqns
      |> perhaps (perhaps_loop (perhaps_apply functrans))
      |> Code.assert_eqns_const thy c;

fun rhs_conv conv thm = Thm.transitive thm ((conv o Thm.rhs_of) thm);

fun term_of_conv thy f =
  Thm.cterm_of thy
  #> f
  #> Thm.prop_of
  #> Logic.dest_equals
  #> snd;

fun preprocess thy c eqns =
  let
    val pre = (Simplifier.theory_context thy o #pre o the_thmproc) thy;
    val functrans = (map (fn (_, (_, f)) => f thy) o #functrans
      o the_thmproc) thy;
  in
    eqns
    |> apply_functrans thy c functrans
    |> (map o apfst) (Code_Unit.rewrite_eqn pre)
    |> (map o apfst) (AxClass.unoverload thy)
    |> map (Code.assert_eqn thy)
    |> burrow_fst (Code_Unit.norm_args thy)
    |> burrow_fst (Code_Unit.norm_varnames thy)
  end;

fun preprocess_conv thy ct =
  let
    val pre = (Simplifier.theory_context thy o #pre o the_thmproc) thy;
  in
    ct
    |> Simplifier.rewrite pre
    |> rhs_conv (AxClass.unoverload_conv thy)
  end;

fun postprocess_conv thy ct =
  let
    val post = (Simplifier.theory_context thy o #post o the_thmproc) thy;
  in
    ct
    |> AxClass.overload_conv thy
    |> rhs_conv (Simplifier.rewrite post)
  end;

fun postprocess_term thy = term_of_conv thy (postprocess_conv thy);

fun print_codeproc thy =
  let
    val ctxt = ProofContext.init thy;
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
type code_graph = (((string * sort) list * typ) * (thm * bool) list) Graph.T;

fun eqns eqngr = these o Option.map snd o try (Graph.get_node eqngr);
fun typ eqngr = fst o Graph.get_node eqngr;
fun all eqngr = Graph.keys eqngr;

fun pretty thy eqngr =
  AList.make (snd o Graph.get_node eqngr) (Graph.keys eqngr)
  |> (map o apfst) (Code_Unit.string_of_const thy)
  |> sort (string_ord o pairself fst)
  |> map (fn (s, thms) =>
       (Pretty.block o Pretty.fbreaks) (
         Pretty.str s
         :: map (Display.pretty_thm o fst) thms
       ))
  |> Pretty.chunks;


(** the Waisenhaus algorithm **)

(* auxiliary *)

fun is_proper_class thy = can (AxClass.get_info thy);

fun complete_proper_sort thy =
  Sign.complete_sort thy #> filter (is_proper_class thy);

fun inst_params thy tyco =
  map (fn (c, _) => AxClass.param_of_inst thy (c, tyco))
    o maps (#params o AxClass.get_info thy);

fun consts_of thy eqns = [] |> (fold o fold o fold_aterms)
  (fn Const (c, ty) => insert (op =) (c, Sign.const_typargs thy (c, Logic.unvarifyT ty)) | _ => I)
    (map (op :: o swap o apfst (snd o strip_comb) o Logic.dest_equals o Thm.plain_prop_of o fst) eqns);

fun tyscm_rhss_of thy c eqns =
  let
    val tyscm = case eqns of [] => Code.default_typscheme thy c
      | ((thm, _) :: _) => Code_Unit.typscheme_eqn thy thm;
    val rhss = consts_of thy eqns;
  in (tyscm, rhss) end;


(* data structures *)

datatype const = Fun of string | Inst of class * string;

fun const_ord (Fun c1, Fun c2) = fast_string_ord (c1, c2)
  | const_ord (Inst class_tyco1, Inst class_tyco2) =
      prod_ord fast_string_ord fast_string_ord (class_tyco1, class_tyco2)
  | const_ord (Fun _, Inst _) = LESS
  | const_ord (Inst _, Fun _) = GREATER;

type var = const * int;

structure Vargraph =
  GraphFun(type key = var val ord = prod_ord const_ord int_ord);

datatype styp = Tyco of string * styp list | Var of var | Free;

fun styp_of c_lhs (Type (tyco, tys)) = Tyco (tyco, map (styp_of c_lhs) tys)
  | styp_of c_lhs (TFree (v, _)) = case c_lhs
     of SOME (c, lhs) => Var (Fun c, find_index (fn (v', _) => v = v') lhs)
      | NONE => Free;

type vardeps_data = ((string * styp list) list * class list) Vargraph.T
  * (((string * sort) list * (thm * bool) list) Symtab.table
    * (class * string) list);

val empty_vardeps_data : vardeps_data =
  (Vargraph.empty, (Symtab.empty, []));


(* retrieving equations and instances from the background context *)

fun obtain_eqns thy eqngr c =
  case try (Graph.get_node eqngr) c
   of SOME ((lhs, _), eqns) => ((lhs, []), [])
    | NONE => let
        val eqns = Code.these_eqns thy c
          |> preprocess thy c;
        val ((lhs, _), rhss) = tyscm_rhss_of thy c eqns;
      in ((lhs, rhss), eqns) end;

fun obtain_instance thy arities (inst as (class, tyco)) =
  case AList.lookup (op =) arities inst
   of SOME classess => (classess, ([], []))
    | NONE => let
        val all_classes = complete_proper_sort thy [class];
        val superclasses = remove (op =) class all_classes
        val classess = map (complete_proper_sort thy)
          (Sign.arity_sorts thy tyco [class]);
        val inst_params = inst_params thy tyco all_classes;
      in (classess, (superclasses, inst_params)) end;


(* computing instantiations *)

fun add_classes thy arities eqngr c_k new_classes vardeps_data =
  let
    val (styps, old_classes) = Vargraph.get_node (fst vardeps_data) c_k;
    val diff_classes = new_classes |> subtract (op =) old_classes;
  in if null diff_classes then vardeps_data
  else let
    val c_ks = Vargraph.imm_succs (fst vardeps_data) c_k |> insert (op =) c_k;
  in
    vardeps_data
    |> (apfst o Vargraph.map_node c_k o apsnd) (append diff_classes)
    |> fold (fn styp => fold (ensure_typmatch_inst thy arities eqngr styp) new_classes) styps
    |> fold (fn c_k => add_classes thy arities eqngr c_k diff_classes) c_ks
  end end
and add_styp thy arities eqngr c_k tyco_styps vardeps_data =
  let
    val (old_styps, classes) = Vargraph.get_node (fst vardeps_data) c_k;
  in if member (op =) old_styps tyco_styps then vardeps_data
  else
    vardeps_data
    |> (apfst o Vargraph.map_node c_k o apfst) (cons tyco_styps)
    |> fold (ensure_typmatch_inst thy arities eqngr tyco_styps) classes
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
    val (classess, (superclasses, inst_params)) =
      obtain_instance thy arities inst;
  in
    vardeps_data
    |> (apsnd o apsnd) (insert (op =) inst)
    |> fold_index (fn (k, _) =>
         apfst (Vargraph.new_node ((Inst (class, tyco), k), ([] ,[])))) classess
    |> fold (fn superclass => ensure_inst thy arities eqngr (superclass, tyco)) superclasses
    |> fold (ensure_fun thy arities eqngr) inst_params
    |> fold_index (fn (k, classes) =>
         add_classes thy arities eqngr (Inst (class, tyco), k) classes
         #> fold (fn superclass =>
             add_dep thy arities eqngr (Inst (superclass, tyco), k)
             (Inst (class, tyco), k)) superclasses
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
    fun type_constructor tyco xs class =
      inst_params thy tyco (Sorts.complete_sort algebra [class])
        @ (maps o maps) fst xs;
    fun type_variable (TFree (_, sort)) = map (pair []) (proj_sort sort);
  in
    flat (Sorts.of_sort_derivation (Syntax.pp_global thy) algebra
      { class_relation = class_relation, type_constructor = type_constructor,
        type_variable = type_variable } (T, proj_sort sort)
       handle Sorts.CLASS_ERROR _ => [] (*permissive!*))
  end;

fun add_arity thy vardeps (class, tyco) =
  AList.default (op =)
    ((class, tyco), map (fn k => (snd o Vargraph.get_node vardeps) (Inst (class, tyco), k))
      (0 upto Sign.arity_number thy tyco - 1));

fun add_eqs thy vardeps (c, (proto_lhs, proto_eqns)) (rhss, eqngr) =
  if can (Graph.get_node eqngr) c then (rhss, eqngr)
  else let
    val lhs = map_index (fn (k, (v, _)) =>
      (v, snd (Vargraph.get_node vardeps (Fun c, k)))) proto_lhs;
    val inst_tab = Vartab.empty |> fold (fn (v, sort) =>
      Vartab.update ((v, 0), sort)) lhs;
    val eqns = proto_eqns
      |> (map o apfst) (Code_Unit.inst_thm thy inst_tab);
    val (tyscm, rhss') = tyscm_rhss_of thy c eqns;
    val eqngr' = Graph.new_node (c, (tyscm, eqns)) eqngr;
  in (map (pair c) rhss' @ rhss, eqngr') end;

fun extend_arities_eqngr thy cs ts (arities, eqngr) =
  let
    val cs_rhss = (fold o fold_aterms) (fn Const (c_ty as (c, _)) =>
      insert (op =) (c, (map (styp_of NONE) o Sign.const_typargs thy) c_ty) | _ => I) ts [];
    val (vardeps, (eqntab, insts)) = empty_vardeps_data
      |> fold (ensure_fun thy arities eqngr) cs
      |> fold (ensure_rhs thy arities eqngr) cs_rhss;
    val arities' = fold (add_arity thy vardeps) insts arities;
    val pp = Syntax.pp_global thy;
    val algebra = Sorts.subalgebra pp (is_proper_class thy)
      (AList.lookup (op =) arities') (Sign.classes_of thy);
    val (rhss, eqngr') = Symtab.fold (add_eqs thy vardeps) eqntab ([], eqngr);
    fun deps_of (c, rhs) = c :: maps (dicts_of thy algebra)
      (rhs ~~ (map snd o fst o fst o Graph.get_node eqngr') c);
    val eqngr'' = fold (fn (c, rhs) => fold
      (curry Graph.add_edge c) (deps_of rhs)) rhss eqngr';
  in (algebra, (arities', eqngr'')) end;


(** store for preprocessed arities and code equations **)

structure Wellsorted = CodeDataFun
(
  type T = ((string * class) * sort list) list * code_graph;
  val empty = ([], Graph.empty);
  fun purge thy cs (arities, eqngr) =
    let
      val del_cs = ((Graph.all_preds eqngr
        o filter (can (Graph.get_node eqngr))) cs);
      val del_arities = del_cs
        |> map_filter (AxClass.inst_of_param thy)
        |> maps (fn (c, tyco) =>
             (map (rpair tyco) o Sign.complete_sort thy o the_list
               o AxClass.class_of_param thy) c);
      val arities' = fold (AList.delete (op =)) del_arities arities;
      val eqngr' = Graph.del_nodes del_cs eqngr;
    in (arities', eqngr') end;
);


(** retrieval and evaluation interfaces **)

fun obtain thy cs ts = apsnd snd
  (Wellsorted.change_yield thy (extend_arities_eqngr thy cs ts));

fun prepare_sorts_typ prep_sort
  = map_type_tfree (fn (v, sort) => TFree (v, prep_sort sort));

fun prepare_sorts prep_sort (Const (c, ty)) =
      Const (c, prepare_sorts_typ prep_sort ty)
  | prepare_sorts prep_sort (t1 $ t2) =
      prepare_sorts prep_sort t1 $ prepare_sorts prep_sort t2
  | prepare_sorts prep_sort (Abs (v, ty, t)) =
      Abs (v, prepare_sorts_typ prep_sort ty, prepare_sorts prep_sort t)
  | prepare_sorts _ (t as Bound _) = t;

fun gen_eval thy cterm_of conclude_evaluation prep_sort evaluator proto_ct =
  let
    val pp = Syntax.pp_global thy;
    val ct = cterm_of proto_ct;
    val _ = (Sign.no_frees pp o map_types (K dummyT) o Sign.no_vars pp)
      (Thm.term_of ct);
    val thm = preprocess_conv thy ct;
    val ct' = Thm.rhs_of thm;
    val t' = Thm.term_of ct';
    val vs = Term.add_tfrees t' [];
    val consts = fold_aterms
      (fn Const (c, _) => insert (op =) c | _ => I) t' [];
 
    val t'' = prepare_sorts prep_sort t';
    val (algebra', eqngr') = obtain thy consts [t''];
  in conclude_evaluation (evaluator algebra' eqngr' vs t'' ct') thm end;

fun simple_evaluator evaluator algebra eqngr vs t ct =
  evaluator algebra eqngr vs t;

fun eval_conv thy =
  let
    fun conclude_evaluation thm2 thm1 =
      let
        val thm3 = postprocess_conv thy (Thm.rhs_of thm2);
      in
        Thm.transitive thm1 (Thm.transitive thm2 thm3) handle THM _ =>
          error ("could not construct evaluation proof:\n"
          ^ (cat_lines o map Display.string_of_thm) [thm1, thm2, thm3])
      end;
  in gen_eval thy I conclude_evaluation end;

fun eval thy prep_sort postproc evaluator = gen_eval thy (Thm.cterm_of thy)
  (K o postproc (postprocess_term thy)) prep_sort (simple_evaluator evaluator);


(** setup **)

val setup = 
  let
    fun mk_attribute f = Thm.declaration_attribute (fn thm => Context.mapping (f thm) I);
    fun add_del_attribute (name, (add, del)) =
      Code.add_attribute (name, Args.del |-- Scan.succeed (mk_attribute del)
        || Scan.succeed (mk_attribute add))
  in
    add_del_attribute ("inline", (add_inline, del_inline))
    #> add_del_attribute ("post", (add_post, del_post))
    #> Code.add_attribute ("unfold", Scan.succeed (Thm.declaration_attribute
       (fn thm => Context.mapping (Codegen.add_unfold thm #> add_inline thm) I)))
  end;

val _ =
  OuterSyntax.improper_command "print_codeproc" "print code preprocessor setup"
  OuterKeyword.diag (Scan.succeed
      (Toplevel.no_timing o Toplevel.unknown_theory o Toplevel.keep
        (print_codeproc o Toplevel.theory_of)));

end; (*struct*)
