(*  Title:      Pure/Isar/code.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Abstract executable content of theory.  Management of data dependent on
executable content.  Cache assumes non-concurrent processing of a single theory.
*)

signature CODE =
sig
  val add_eqn: thm -> theory -> theory
  val add_nonlinear_eqn: thm -> theory -> theory
  val add_liberal_eqn: thm -> theory -> theory
  val add_default_eqn: thm -> theory -> theory
  val add_default_eqn_attr: Attrib.src
  val del_eqn: thm -> theory -> theory
  val del_eqns: string -> theory -> theory
  val add_eqnl: string * (thm * bool) list Susp.T -> theory -> theory
  val map_pre: (MetaSimplifier.simpset -> MetaSimplifier.simpset) -> theory -> theory
  val map_post: (MetaSimplifier.simpset -> MetaSimplifier.simpset) -> theory -> theory
  val add_inline: thm -> theory -> theory
  val del_inline: thm -> theory -> theory
  val add_post: thm -> theory -> theory
  val del_post: thm -> theory -> theory
  val add_functrans: string * (theory -> thm list -> thm list option) -> theory -> theory
  val del_functrans: string -> theory -> theory
  val add_datatype: (string * typ) list -> theory -> theory
  val add_datatype_cmd: string list -> theory -> theory
  val type_interpretation:
    (string * ((string * sort) list * (string * typ list) list)
      -> theory -> theory) -> theory -> theory
  val add_case: thm -> theory -> theory
  val add_undefined: string -> theory -> theory
  val purge_data: theory -> theory

  val coregular_algebra: theory -> Sorts.algebra
  val operational_algebra: theory -> (sort -> sort) * Sorts.algebra
  val these_eqns: theory -> string -> (thm * bool) list
  val get_datatype: theory -> string -> ((string * sort) list * (string * typ list) list)
  val get_datatype_of_constr: theory -> string -> string option
  val get_case_data: theory -> string -> (int * string list) option
  val is_undefined: theory -> string -> bool
  val default_typ: theory -> string -> (string * sort) list * typ

  val preprocess_conv: cterm -> thm
  val preprocess_term: theory -> term -> term
  val postprocess_conv: cterm -> thm
  val postprocess_term: theory -> term -> term

  val add_attribute: string * (Args.T list -> attribute * Args.T list) -> theory -> theory

  val print_codesetup: theory -> unit
end;

signature CODE_DATA_ARGS =
sig
  type T
  val empty: T
  val purge: theory -> string list -> T -> T
end;

signature CODE_DATA =
sig
  type T
  val get: theory -> T
  val change: theory -> (T -> T) -> T
  val change_yield: theory -> (T -> 'a * T) -> 'a * T
end;

signature PRIVATE_CODE =
sig
  include CODE
  val declare_data: Object.T -> (theory -> string list -> Object.T -> Object.T)
    -> serial
  val get_data: serial * ('a -> Object.T) * (Object.T -> 'a)
    -> theory -> 'a
  val change_data: serial * ('a -> Object.T) * (Object.T -> 'a)
    -> theory -> ('a -> 'a) -> 'a
  val change_yield_data: serial * ('a -> Object.T) * (Object.T -> 'a)
    -> theory -> ('a -> 'b * 'a) -> 'b * 'a
end;

structure Code : PRIVATE_CODE =
struct

(** code attributes **)

structure CodeAttr = TheoryDataFun (
  type T = (string * (Args.T list -> attribute * Args.T list)) list;
  val empty = [];
  val copy = I;
  val extend = I;
  fun merge _ = AList.merge (op = : string * string -> bool) (K true);
);

fun add_attribute (attr as (name, _)) =
  let
    fun add_parser ("", parser) attrs = attrs @ [("", parser)]
      | add_parser (name, parser) attrs = (name, Args.$$$ name |-- parser) :: attrs;
    fun error "" = error ("Code attribute already declared")
      | error name = error ("Code attribute " ^ name ^ " already declared")
  in CodeAttr.map (fn attrs => if AList.defined (op =) attrs name
    then error name else add_parser attr attrs)
  end;

val _ =
  let
    val code_attr = Attrib.syntax (Scan.peek (fn context =>
      List.foldr op || Scan.fail (map snd (CodeAttr.get (Context.theory_of context)))));
  in
    Context.>> (Context.map_theory
      (Attrib.add_attributes
        [("code", code_attr, "declare theorems for code generation")]))
  end;


(** logical and syntactical specification of executable code **)

(* defining equations with linear flag, default flag and lazy theorems *)

fun pretty_lthms ctxt r = case Susp.peek r
 of SOME thms => map (ProofContext.pretty_thm ctxt o fst) thms
  | NONE => [Pretty.str "[...]"];

fun certificate thy f r =
  case Susp.peek r
   of SOME thms => (Susp.value o burrow_fst (f thy)) thms
    | NONE => let
        val thy_ref = Theory.check_thy thy;
      in Susp.delay (fn () => (burrow_fst (f (Theory.deref thy_ref)) o Susp.force) r) end;

fun add_drop_redundant (thm, linear) thms =
  let
    val thy = Thm.theory_of_thm thm;
    val args_of = snd o strip_comb o fst o Logic.dest_equals o Thm.plain_prop_of;
    val args = args_of thm;
    val incr_idx = Logic.incr_indexes ([], Thm.maxidx_of thm + 1);
    fun matches_args args' = length args <= length args' andalso
      Pattern.matchess thy (args, (map incr_idx o curry Library.take (length args)) args');
    fun drop (thm', linear') = if (linear orelse not linear')
      andalso matches_args (args_of thm') then 
        (warning ("Code generator: dropping redundant defining equation\n" ^ Display.string_of_thm thm'); true)
      else false;
  in (thm, linear) :: filter_out drop thms end;

fun add_thm _ thm (false, thms) = (false, Susp.map_force (add_drop_redundant thm) thms)
  | add_thm true thm (true, thms) = (true, Susp.map_force (fn thms => thms @ [thm]) thms)
  | add_thm false thm (true, thms) = (false, Susp.value [thm]);

fun add_lthms lthms _ = (false, lthms);

fun del_thm thm = (apsnd o Susp.map_force) (remove (eq_fst Thm.eq_thm_prop) (thm, true));

fun merge_defthms ((true, _), defthms2) = defthms2
  | merge_defthms (defthms1 as (false, _), (true, _)) = defthms1
  | merge_defthms ((false, _), defthms2 as (false, _)) = defthms2;


(* syntactic datatypes *)

val eq_string = op = : string * string -> bool;

fun eq_dtyp ((vs1, cs1), (vs2, cs2)) = 
  gen_eq_set (eq_pair eq_string (gen_eq_set eq_string)) (vs1, vs2)
    andalso gen_eq_set (eq_fst eq_string) (cs1, cs2);

fun merge_dtyps (tabs as (tab1, tab2)) =
  let
    fun join _ (cos as (_, cos2)) = if eq_dtyp cos then raise Symtab.SAME else cos2;
  in Symtab.join join tabs end;


(* specification data *)

datatype spec = Spec of {
  eqns: (bool * (thm * bool) list Susp.T) Symtab.table,
  dtyps: ((string * sort) list * (string * typ list) list) Symtab.table,
  cases: (int * string list) Symtab.table * unit Symtab.table
};

fun mk_spec (eqns, (dtyps, cases)) =
  Spec { eqns = eqns, dtyps = dtyps, cases = cases };
fun map_spec f (Spec { eqns = eqns, dtyps = dtyps, cases = cases }) =
  mk_spec (f (eqns, (dtyps, cases)));
fun merge_spec (Spec { eqns = eqns1, dtyps = dtyps1, cases = (cases1, undefs1) },
  Spec { eqns = eqns2, dtyps = dtyps2, cases = (cases2, undefs2) }) =
  let
    val eqns = Symtab.join (K merge_defthms) (eqns1, eqns2);
    val dtyps = merge_dtyps (dtyps1, dtyps2);
    val cases = (Symtab.merge (K true) (cases1, cases2),
      Symtab.merge (K true) (undefs1, undefs2));
  in mk_spec (eqns, (dtyps, cases)) end;


(* pre- and postprocessor *)

datatype thmproc = Thmproc of {
  pre: MetaSimplifier.simpset,
  post: MetaSimplifier.simpset,
  functrans: (string * (serial * (theory -> thm list -> thm list option))) list
};

fun mk_thmproc ((pre, post), functrans) =
  Thmproc { pre = pre, post = post, functrans = functrans };
fun map_thmproc f (Thmproc { pre, post, functrans }) =
  mk_thmproc (f ((pre, post), functrans));
fun merge_thmproc (Thmproc { pre = pre1, post = post1, functrans = functrans1 },
  Thmproc { pre = pre2, post = post2, functrans = functrans2 }) =
    let
      val pre = MetaSimplifier.merge_ss (pre1, pre2);
      val post = MetaSimplifier.merge_ss (post1, post2);
      val functrans = AList.merge (op =) (eq_fst (op =)) (functrans1, functrans2);
    in mk_thmproc ((pre, post), functrans) end;

datatype exec = Exec of {
  thmproc: thmproc,
  spec: spec
};


(* code setup data *)

fun mk_exec (thmproc, spec) =
  Exec { thmproc = thmproc, spec = spec };
fun map_exec f (Exec { thmproc = thmproc, spec = spec }) =
  mk_exec (f (thmproc, spec));
fun merge_exec (Exec { thmproc = thmproc1, spec = spec1 },
  Exec { thmproc = thmproc2, spec = spec2 }) =
  let
    val thmproc = merge_thmproc (thmproc1, thmproc2);
    val spec = merge_spec (spec1, spec2);
  in mk_exec (thmproc, spec) end;
val empty_exec = mk_exec (mk_thmproc ((MetaSimplifier.empty_ss, MetaSimplifier.empty_ss), []),
  mk_spec (Symtab.empty, (Symtab.empty, (Symtab.empty, Symtab.empty))));

fun the_thmproc (Exec { thmproc = Thmproc x, ...}) = x;
fun the_spec (Exec { spec = Spec x, ...}) = x;
val the_eqns = #eqns o the_spec;
val the_dtyps = #dtyps o the_spec;
val the_cases = #cases o the_spec;
val map_thmproc = map_exec o apfst o map_thmproc;
val map_eqns = map_exec o apsnd o map_spec o apfst;
val map_dtyps = map_exec o apsnd o map_spec o apsnd o apfst;
val map_cases = map_exec o apsnd o map_spec o apsnd o apsnd;


(* data slots dependent on executable content *)

(*private copy avoids potential conflict of table exceptions*)
structure Datatab = TableFun(type key = int val ord = int_ord);

local

type kind = {
  empty: Object.T,
  purge: theory -> string list -> Object.T -> Object.T
};

val kinds = ref (Datatab.empty: kind Datatab.table);
val kind_keys = ref ([]: serial list);

fun invoke f k = case Datatab.lookup (! kinds) k
 of SOME kind => f kind
  | NONE => sys_error "Invalid code data identifier";

in

fun declare_data empty purge =
  let
    val k = serial ();
    val kind = {empty = empty, purge = purge};
    val _ = change kinds (Datatab.update (k, kind));
    val _ = change kind_keys (cons k);
  in k end;

fun invoke_init k = invoke (fn kind => #empty kind) k;

fun invoke_purge_all thy cs =
  fold (fn k => Datatab.map_entry k
    (invoke (fn kind => #purge kind thy cs) k)) (! kind_keys);

end; (*local*)


(** theory store **)

local

type data = Object.T Datatab.table;
val empty_data = Datatab.empty : data;

structure CodeData = TheoryDataFun
(
  type T = exec * data ref;
  val empty = (empty_exec, ref empty_data);
  fun copy (exec, data) = (exec, ref (! data));
  val extend = copy;
  fun merge pp ((exec1, data1), (exec2, data2)) =
    (merge_exec (exec1, exec2), ref empty_data);
);

val _ = Context.>> (Context.map_theory CodeData.init);

fun thy_data f thy = f ((snd o CodeData.get) thy);

fun get_ensure_init kind data_ref =
  case Datatab.lookup (! data_ref) kind
   of SOME x => x
    | NONE => let val y = invoke_init kind
        in (change data_ref (Datatab.update (kind, y)); y) end;

in

(* access to executable content *)

val the_exec = fst o CodeData.get;

fun complete_class_params thy cs =
  fold (fn c => case AxClass.inst_of_param thy c
   of NONE => insert (op =) c
    | SOME (c', _) => insert (op =) c' #> insert (op =) c) cs [];

fun map_exec_purge touched f thy =
  CodeData.map (fn (exec, data) => (f exec, ref (case touched
   of SOME cs => invoke_purge_all thy (complete_class_params thy cs) (! data)
    | NONE => empty_data))) thy;

val purge_data = (CodeData.map o apsnd) (K (ref empty_data));


(* access to data dependent on abstract executable content *)

fun get_data (kind, _, dest) = thy_data (get_ensure_init kind #> dest);

fun change_data (kind, mk, dest) =
  let
    fun chnge data_ref f =
      let
        val data = get_ensure_init kind data_ref;
        val data' = f (dest data);
      in (change data_ref (Datatab.update (kind, mk data')); data') end;
  in thy_data chnge end;

fun change_yield_data (kind, mk, dest) =
  let
    fun chnge data_ref f =
      let
        val data = get_ensure_init kind data_ref;
        val (x, data') = f (dest data);
      in (x, (change data_ref (Datatab.update (kind, mk data')); data')) end;
  in thy_data chnge end;

end; (*local*)


(* print executable content *)

fun print_codesetup thy =
  let
    val ctxt = ProofContext.init thy;
    val exec = the_exec thy;
    fun pretty_eqn (s, (_, lthms)) =
      (Pretty.block o Pretty.fbreaks) (
        Pretty.str s :: pretty_lthms ctxt lthms
      );
    fun pretty_dtyp (s, []) =
          Pretty.str s
      | pretty_dtyp (s, cos) =
          (Pretty.block o Pretty.breaks) (
            Pretty.str s
            :: Pretty.str "="
            :: separate (Pretty.str "|") (map (fn (c, []) => Pretty.str (Code_Unit.string_of_const thy c)
                 | (c, tys) =>
                     (Pretty.block o Pretty.breaks)
                        (Pretty.str (Code_Unit.string_of_const thy c)
                          :: Pretty.str "of"
                          :: map (Pretty.quote o Syntax.pretty_typ_global thy) tys)) cos)
          );
    val pre = (#pre o the_thmproc) exec;
    val post = (#post o the_thmproc) exec;
    val functrans = (map fst o #functrans o the_thmproc) exec;
    val eqns = the_eqns exec
      |> Symtab.dest
      |> (map o apfst) (Code_Unit.string_of_const thy)
      |> sort (string_ord o pairself fst);
    val dtyps = the_dtyps exec
      |> Symtab.dest
      |> map (fn (dtco, (vs, cos)) =>
          (Syntax.string_of_typ_global thy (Type (dtco, map TFree vs)), cos))
      |> sort (string_ord o pairself fst)
  in
    (Pretty.writeln o Pretty.chunks) [
      Pretty.block (
        Pretty.str "defining equations:"
        :: Pretty.fbrk
        :: (Pretty.fbreaks o map pretty_eqn) eqns
      ),
      Pretty.block [
        Pretty.str "preprocessing simpset:",
        Pretty.fbrk,
        MetaSimplifier.pretty_ss pre
      ],
      Pretty.block [
        Pretty.str "postprocessing simpset:",
        Pretty.fbrk,
        MetaSimplifier.pretty_ss post
      ],
      Pretty.block (
        Pretty.str "function transformers:"
        :: Pretty.fbrk
        :: (Pretty.fbreaks o map Pretty.str) functrans
      ),
      Pretty.block (
        Pretty.str "datatypes:"
        :: Pretty.fbrk
        :: (Pretty.fbreaks o map pretty_dtyp) dtyps
      )
    ]
  end;



(** theorem transformation and certification **)

fun const_of thy = dest_Const o fst o strip_comb o fst o Logic.dest_equals o Thm.plain_prop_of;

fun const_of_eqn thy = AxClass.unoverload_const thy o const_of thy;

fun common_typ_eqns [] = []
  | common_typ_eqns [thm] = [thm]
  | common_typ_eqns (thms as thm :: _) = (*FIXME is too general*)
      let
        val thy = Thm.theory_of_thm thm;
        fun incr_thm thm max =
          let
            val thm' = incr_indexes max thm;
            val max' = Thm.maxidx_of thm' + 1;
          in (thm', max') end;
        val (thms', maxidx) = fold_map incr_thm thms 0;
        val ty1 :: tys = map (snd o const_of thy) thms';
        fun unify ty env = Sign.typ_unify thy (ty1, ty) env
          handle Type.TUNIFY =>
            error ("Type unificaton failed, while unifying defining equations\n"
            ^ (cat_lines o map Display.string_of_thm) thms
            ^ "\nwith types\n"
            ^ (cat_lines o map (Code_Unit.string_of_typ thy)) (ty1 :: tys));
        val (env, _) = fold unify tys (Vartab.empty, maxidx)
        val instT = Vartab.fold (fn (x_i, (sort, ty)) =>
          cons (Thm.ctyp_of thy (TVar (x_i, sort)), Thm.ctyp_of thy ty)) env [];
      in map (Thm.instantiate (instT, [])) thms' end;

fun certify_const thy const thms =
  let
    fun cert thm = if const = const_of_eqn thy thm
      then thm else error ("Wrong head of defining equation,\nexpected constant "
        ^ Code_Unit.string_of_const thy const ^ "\n" ^ Display.string_of_thm thm)
  in map cert thms end;



(** operational sort algebra and class discipline **)

local

fun aggr_neutr f y [] = y
  | aggr_neutr f y (x::xs) = aggr_neutr f (f y x) xs;

fun aggregate f [] = NONE
  | aggregate f (x::xs) = SOME (aggr_neutr f x xs);

fun inter_sorts algebra =
  aggregate (map2 (curry (Sorts.inter_sort algebra)));

fun specific_constraints thy (class, tyco) =
  let
    val vs = Name.invents Name.context "" (Sign.arity_number thy tyco);
    val classparams = (map fst o these o try (#params o AxClass.get_info thy)) class;
    val eqns = classparams
      |> map_filter (fn c => try (AxClass.param_of_inst thy) (c, tyco))
      |> map (Symtab.lookup ((the_eqns o the_exec) thy))
      |> (map o Option.map) (map fst o Susp.force o snd)
      |> maps these
      |> map (Thm.transfer thy);
    fun sorts_of [Type (_, tys)] = map (snd o dest_TVar) tys
      | sorts_of tys = map (snd o dest_TVar) tys;
    val sorts = map (sorts_of o Sign.const_typargs thy o const_of thy) eqns;
  in sorts end;

fun weakest_constraints thy algebra (class, tyco) =
  let
    val all_superclasses = Sorts.complete_sort algebra [class];
  in case inter_sorts algebra (maps (fn class => specific_constraints thy (class, tyco)) all_superclasses)
   of SOME sorts => sorts
    | NONE => Sorts.mg_domain algebra tyco [class]
  end;

fun strongest_constraints thy algebra (class, tyco) =
  let
    val all_subclasses = class :: Graph.all_preds ((#classes o Sorts.rep_algebra) algebra) [class];
    val inst_subclasses = filter (can (Sorts.mg_domain algebra tyco) o single) all_subclasses;
  in case inter_sorts algebra (maps (fn class => specific_constraints thy (class, tyco)) inst_subclasses)
   of SOME sorts => sorts
    | NONE => replicate
        (Sign.arity_number thy tyco) (Sorts.minimize_sort algebra (Sorts.all_classes algebra))
  end;

fun get_algebra thy (class, tyco) =
  let
    val base_algebra = Sign.classes_of thy;
  in if can (Sorts.mg_domain base_algebra tyco) [class]
    then base_algebra
    else let
      val superclasses = Sorts.super_classes base_algebra class;
      val sorts = inter_sorts base_algebra
          (map_filter (fn class => try (Sorts.mg_domain base_algebra tyco) [class]) superclasses)
        |> the_default (replicate (Sign.arity_number thy tyco) [])
    in
      base_algebra
      |> Sorts.add_arities (Syntax.pp_global thy) (tyco, [(class, sorts)])
    end
  end;

fun gen_classparam_typ constr thy class (c, tyco) = 
  let
    val algebra = get_algebra thy (class, tyco);
    val cs = these (try (#params o AxClass.get_info thy) class);
    val SOME ty = AList.lookup (op =) cs c;
    val sort_args = Name.names (Name.declare Name.aT Name.context) Name.aT
      (constr thy algebra (class, tyco));
    val ty_inst = Type (tyco, map TFree sort_args);
  in Logic.varifyT (map_type_tfree (K ty_inst) ty) end;

fun retrieve_algebra thy operational =
  Sorts.subalgebra (Syntax.pp_global thy) operational
    (weakest_constraints thy (Sign.classes_of thy))
    (Sign.classes_of thy);

in

fun coregular_algebra thy = retrieve_algebra thy (K true) |> snd;
fun operational_algebra thy =
  let
    fun add_iff_operational class =
      can (AxClass.get_info thy) class ? cons class;
    val operational_classes = fold add_iff_operational (Sign.all_classes thy) []
  in retrieve_algebra thy (member (op =) operational_classes) end;

val classparam_weakest_typ = gen_classparam_typ weakest_constraints;
val classparam_strongest_typ = gen_classparam_typ strongest_constraints;

fun assert_eqn_linear (eqn as (thm, linear)) =
  if linear then eqn else Code_Unit.bad_thm
    ("Duplicate variables on left hand side of defining equation:\n"
      ^ Display.string_of_thm thm);

fun assert_eqn_typ (thm, linear) =
  let
    val thy = Thm.theory_of_thm thm;
    fun check_typ_classparam tyco (c, thm) =
          let
            val SOME class = AxClass.class_of_param thy c;
            val (_, ty) = const_of thy thm;
            val ty_decl = classparam_weakest_typ thy class (c, tyco);
            val ty_strongest = classparam_strongest_typ thy class (c, tyco);
            fun constrain thm = 
              let
                val max = Thm.maxidx_of thm + 1;
                val ty_decl' = Logic.incr_tvar max ty_decl;
                val (_, ty') = const_of thy thm;
                val (env, _) = Sign.typ_unify thy (ty_decl', ty') (Vartab.empty, max);
                val instT = Vartab.fold (fn (x_i, (sort, ty)) =>
                  cons (Thm.ctyp_of thy (TVar (x_i, sort)), Thm.ctyp_of thy ty)) env [];
              in Thm.instantiate (instT, []) thm end;
          in if Sign.typ_instance thy (ty_strongest, ty)
            then if Sign.typ_instance thy (ty, ty_decl)
            then thm
            else (warning ("Constraining type\n" ^ Code_Unit.string_of_typ thy ty
              ^ "\nof defining equation\n"
              ^ Display.string_of_thm thm
              ^ "\nto permitted most general type\n"
              ^ Code_Unit.string_of_typ thy ty_decl);
              constrain thm)
            else Code_Unit.bad_thm ("Type\n" ^ Code_Unit.string_of_typ thy ty
              ^ "\nof defining equation\n"
              ^ Display.string_of_thm thm
              ^ "\nis incompatible with permitted least general type\n"
              ^ Code_Unit.string_of_typ thy ty_strongest)
          end;
    fun check_typ_fun (c, thm) =
      let
        val (_, ty) = const_of thy thm;
        val ty_decl = Sign.the_const_type thy c;
      in if Sign.typ_equiv thy (Type.strip_sorts ty_decl, Type.strip_sorts ty)
        then thm
        else Code_Unit.bad_thm ("Type\n" ^ Code_Unit.string_of_typ thy ty
           ^ "\nof defining equation\n"
           ^ Display.string_of_thm thm
           ^ "\nis incompatible with declared function type\n"
           ^ Code_Unit.string_of_typ thy ty_decl)
      end;
    fun check_typ (c, thm) =
      case AxClass.inst_of_param thy c
       of SOME (c, tyco) => check_typ_classparam tyco (c, thm)
        | NONE => check_typ_fun (c, thm);
    val c = const_of_eqn thy thm;
    val thm' = check_typ (c, thm);
  in (thm', linear) end;

fun mk_eqn linear = Code_Unit.error_thm
  (assert_eqn_typ o (if linear then assert_eqn_linear else I) o Code_Unit.mk_eqn);
val mk_liberal_eqn = Code_Unit.warning_thm
  (assert_eqn_typ o assert_eqn_linear o Code_Unit.mk_eqn);
val mk_syntactic_eqn = Code_Unit.warning_thm
  (assert_eqn_typ o Code_Unit.mk_eqn);
val mk_default_eqn = Code_Unit.try_thm
  (assert_eqn_typ o assert_eqn_linear o Code_Unit.mk_eqn);

end; (*local*)


(** interfaces and attributes **)

fun delete_force msg key xs =
  if AList.defined (op =) xs key then AList.delete (op =) key xs
  else error ("No such " ^ msg ^ ": " ^ quote key);

fun get_datatype thy tyco =
  case Symtab.lookup ((the_dtyps o the_exec) thy) tyco
   of SOME spec => spec
    | NONE => Sign.arity_number thy tyco
        |> Name.invents Name.context Name.aT
        |> map (rpair [])
        |> rpair [];

fun get_datatype_of_constr thy c =
  case (snd o strip_type o Sign.the_const_type thy) c
   of Type (tyco, _) => if member (op =)
       ((the_default [] o Option.map (map fst o snd) o Symtab.lookup ((the_dtyps o the_exec) thy)) tyco) c
       then SOME tyco else NONE
    | _ => NONE;

fun get_constr_typ thy c =
  case get_datatype_of_constr thy c
   of SOME tyco => let
          val (vs, cos) = get_datatype thy tyco;
          val SOME tys = AList.lookup (op =) cos c;
          val ty = tys ---> Type (tyco, map TFree vs);
        in SOME (Logic.varifyT ty) end
    | NONE => NONE;

val get_case_data = Symtab.lookup o fst o the_cases o the_exec;

val is_undefined = Symtab.defined o snd o the_cases o the_exec;

fun gen_add_eqn linear strict default thm thy =
  case (if strict then SOME o mk_eqn linear else mk_liberal_eqn) thm
   of SOME (thm, _) =>
        let
          val c = const_of_eqn thy thm;
          val _ = if strict andalso (is_some o AxClass.class_of_param thy) c
            then error ("Rejected polymorphic equation for overloaded constant:\n"
              ^ Display.string_of_thm thm)
            else ();
          val _ = if strict andalso (is_some o get_datatype_of_constr thy) c
            then error ("Rejected equation for datatype constructor:\n"
              ^ Display.string_of_thm thm)
            else ();
        in
          (map_exec_purge (SOME [c]) o map_eqns) (Symtab.map_default
            (c, (true, Susp.value [])) (add_thm default (thm, linear))) thy
        end
    | NONE => thy;

val add_eqn = gen_add_eqn true true false;
val add_liberal_eqn = gen_add_eqn true false false;
val add_default_eqn = gen_add_eqn true false true;
val add_nonlinear_eqn = gen_add_eqn false true false;

fun del_eqn thm thy = case mk_syntactic_eqn thm
 of SOME (thm, _) => let
        val c = const_of_eqn thy thm;
      in map_exec_purge (SOME [c]) (map_eqns
        (Symtab.map_entry c (del_thm thm))) thy
      end
  | NONE => thy;

fun del_eqns c = map_exec_purge (SOME [c])
  (map_eqns (Symtab.map_entry c (K (false, Susp.value []))));

fun add_eqnl (c, lthms) thy =
  let
    val lthms' = certificate thy (fn thy => certify_const thy c) lthms;
      (*FIXME must check compatibility with sort algebra;
        alas, naive checking results in non-termination!*)
  in
    map_exec_purge (SOME [c])
      (map_eqns (Symtab.map_default (c, (true, Susp.value []))
        (add_lthms lthms'))) thy
  end;

val add_default_eqn_attr = Attrib.internal (fn _ => Thm.declaration_attribute
  (fn thm => Context.mapping (add_default_eqn thm) I));

structure TypeInterpretation = InterpretationFun(type T = string * serial val eq = eq_snd (op =) : T * T -> bool);

fun add_datatype raw_cs thy =
  let
    val cs = map (fn c_ty as (_, ty) => (AxClass.unoverload_const thy c_ty, ty)) raw_cs;
    val (tyco, vs_cos) = Code_Unit.constrset_of_consts thy cs;
    val cs' = map fst (snd vs_cos);
    val purge_cs = case Symtab.lookup ((the_dtyps o the_exec) thy) tyco
     of SOME (vs, cos) => if null cos then NONE else SOME (cs' @ map fst cos)
      | NONE => NONE;
  in
    thy
    |> map_exec_purge purge_cs (map_dtyps (Symtab.update (tyco, vs_cos))
        #> map_eqns (fold (Symtab.delete_safe o fst) cs))
    |> TypeInterpretation.data (tyco, serial ())
  end;

fun type_interpretation f =  TypeInterpretation.interpretation
  (fn (tyco, _) => fn thy => f (tyco, get_datatype thy tyco) thy);

fun add_datatype_cmd raw_cs thy =
  let
    val cs = map (Code_Unit.read_bare_const thy) raw_cs;
  in add_datatype cs thy end;

fun add_case thm thy =
  let
    val entry as (c, _) = Code_Unit.case_cert thm;
  in
    (map_exec_purge (SOME [c]) o map_cases o apfst) (Symtab.update entry) thy
  end;

fun add_undefined c thy =
  (map_exec_purge (SOME [c]) o map_cases o apsnd) (Symtab.update (c, ())) thy;

val map_pre = map_exec_purge NONE o map_thmproc o apfst o apfst;
val map_post = map_exec_purge NONE o map_thmproc o apfst o apsnd;

fun add_inline thm thy = (map_pre o MetaSimplifier.add_simp)
  (Code_Unit.error_thm Code_Unit.mk_rew thm) thy;
    (*fully applied in order to get right context for mk_rew!*)

fun del_inline thm thy = (map_pre o MetaSimplifier.del_simp)
  (Code_Unit.error_thm Code_Unit.mk_rew thm) thy;
    (*fully applied in order to get right context for mk_rew!*)

fun add_post thm thy = (map_post o MetaSimplifier.add_simp)
  (Code_Unit.error_thm Code_Unit.mk_rew thm) thy;
    (*fully applied in order to get right context for mk_rew!*)

fun del_post thm thy = (map_post o MetaSimplifier.del_simp)
  (Code_Unit.error_thm Code_Unit.mk_rew thm) thy;
    (*fully applied in order to get right context for mk_rew!*)
  
fun add_functrans (name, f) =
  (map_exec_purge NONE o map_thmproc o apsnd)
    (AList.update (op =) (name, (serial (), f)));

fun del_functrans name =
  (map_exec_purge NONE o map_thmproc o apsnd)
    (delete_force "function transformer" name);

val _ = Context.>> (Context.map_theory
  (let
    fun mk_attribute f = Thm.declaration_attribute (fn thm => Context.mapping (f thm) I);
    fun add_simple_attribute (name, f) =
      add_attribute (name, Scan.succeed (mk_attribute f));
    fun add_del_attribute (name, (add, del)) =
      add_attribute (name, Args.del |-- Scan.succeed (mk_attribute del)
        || Scan.succeed (mk_attribute add))
  in
    TypeInterpretation.init
    #> add_del_attribute ("func", (add_eqn, del_eqn))
    #> add_simple_attribute ("nbe", add_nonlinear_eqn)
    #> add_del_attribute ("inline", (add_inline, del_inline))
    #> add_del_attribute ("post", (add_post, del_post))
  end));


(** post- and preprocessing **)

local

fun apply_functrans thy [] = []
  | apply_functrans thy (thms as (thm, _) :: _) =
      let
        val const = const_of_eqn thy thm;
        val functrans = (map (fn (_, (_, f)) => f thy) o #functrans
          o the_thmproc o the_exec) thy;
        val thms' = perhaps (perhaps_loop (perhaps_apply functrans)) (map fst thms);
        val thms'' = certify_const thy const thms';
      in map Code_Unit.add_linear thms'' end;

fun rhs_conv conv thm =
  let
    val thm' = (conv o Thm.rhs_of) thm;
  in Thm.transitive thm thm' end

fun term_of_conv thy f =
  Thm.cterm_of thy
  #> f
  #> Thm.prop_of
  #> Logic.dest_equals
  #> snd;

in

fun preprocess thy thms =
  let
    val pre = (Simplifier.theory_context thy o #pre o the_thmproc o the_exec) thy;
  in
    thms
    |> apply_functrans thy
    |> (map o apfst) (Code_Unit.rewrite_eqn pre)
    (*FIXME - must check here: rewrite rule, defining equation, proper constant *)
    |> (map o apfst) (AxClass.unoverload thy)
    |> burrow_fst common_typ_eqns
  end;


fun preprocess_conv ct =
  let
    val thy = Thm.theory_of_cterm ct;
    val pre = (Simplifier.theory_context thy o #pre o the_thmproc o the_exec) thy;
  in
    ct
    |> Simplifier.rewrite pre
    |> rhs_conv (AxClass.unoverload_conv thy)
  end;

fun preprocess_term thy = term_of_conv thy preprocess_conv;

fun postprocess_conv ct =
  let
    val thy = Thm.theory_of_cterm ct;
    val post = (Simplifier.theory_context thy o #post o the_thmproc o the_exec) thy;
  in
    ct
    |> AxClass.overload_conv thy
    |> rhs_conv (Simplifier.rewrite post)
  end;

fun postprocess_term thy = term_of_conv thy postprocess_conv;

end; (*local*)

fun default_typ_proto thy c = case AxClass.inst_of_param thy c
 of SOME (c, tyco) => classparam_weakest_typ thy ((the o AxClass.class_of_param thy) c)
      (c, tyco) |> SOME
  | NONE => (case AxClass.class_of_param thy c
     of SOME class => SOME (Term.map_type_tvar
          (K (TVar ((Name.aT, 0), [class]))) (Sign.the_const_type thy c))
      | NONE => get_constr_typ thy c);

local

fun get_eqns thy const =
  Symtab.lookup ((the_eqns o the_exec) thy) const
  |> Option.map (Susp.force o snd)
  |> these
  |> (map o apfst) (Thm.transfer thy);

in

fun these_eqns thy const =
  let
    val drop_refl = filter_out
      (is_equal o Term.fast_term_ord o Logic.dest_equals o Thm.plain_prop_of o fst);
  in
    get_eqns thy const
    |> preprocess thy
    |> drop_refl
  end;

fun default_typ thy c = case default_typ_proto thy c
 of SOME ty => Code_Unit.typscheme thy (c, ty)
  | NONE => (case get_eqns thy c
     of (thm, _) :: _ => snd (Code_Unit.head_eqn (AxClass.unoverload thy thm))
      | [] => Code_Unit.typscheme thy (c, Sign.the_const_type thy c));

end; (*local*)

end; (*struct*)


(** type-safe interfaces for data depedent on executable content **)

functor CodeDataFun(Data: CODE_DATA_ARGS): CODE_DATA =
struct

type T = Data.T;
exception Data of T;
fun dest (Data x) = x

val kind = Code.declare_data (Data Data.empty)
  (fn thy => fn cs => fn Data x => Data (Data.purge thy cs x));

val data_op = (kind, Data, dest);

val get = Code.get_data data_op;
val change = Code.change_data data_op;
fun change_yield thy = Code.change_yield_data data_op thy;

end;

structure Code : CODE = struct open Code; end;
