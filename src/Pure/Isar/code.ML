(*  Title:      Pure/Isar/code.ML
    Author:     Florian Haftmann, TU Muenchen

Abstract executable content of theory.  Management of data dependent on
executable content.  Cache assumes non-concurrent processing of a single theory.
*)

signature CODE =
sig
  val add_eqn: thm -> theory -> theory
  val add_nonlinear_eqn: thm -> theory -> theory
  val add_default_eqn: thm -> theory -> theory
  val add_default_eqn_attribute: attribute
  val add_default_eqn_attrib: Attrib.src
  val del_eqn: thm -> theory -> theory
  val del_eqns: string -> theory -> theory
  val add_eqnl: string * (thm * bool) list lazy -> theory -> theory
  val map_pre: (simpset -> simpset) -> theory -> theory
  val map_post: (simpset -> simpset) -> theory -> theory
  val add_inline: thm -> theory -> theory
  val add_functrans: string * (theory -> (thm * bool) list -> (thm * bool) list option) -> theory -> theory
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
  val these_raw_eqns: theory -> string -> (thm * bool) list
  val get_datatype: theory -> string -> ((string * sort) list * (string * typ list) list)
  val get_datatype_of_constr: theory -> string -> string option
  val get_case_scheme: theory -> string -> (int * (int * string list)) option
  val is_undefined: theory -> string -> bool
  val default_typscheme: theory -> string -> (string * sort) list * typ

  val preprocess_conv: theory -> cterm -> thm
  val preprocess_term: theory -> term -> term
  val postprocess_conv: theory -> cterm -> thm
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
    fun add_parser ("", parser) attrs = attrs |> rev |> AList.update (op =) ("", parser) |> rev
      | add_parser (name, parser) attrs = (name, Args.$$$ name |-- parser) :: attrs;
  in CodeAttr.map (fn attrs => if not (name = "") andalso AList.defined (op =) attrs name
    then error ("Code attribute " ^ name ^ " already declared") else add_parser attr attrs)
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

(* code equations *)

type eqns = bool * (thm * bool) list lazy;
  (*default flag, theorems with linear flag (perhaps lazy)*)

fun pretty_lthms ctxt r = case Lazy.peek r
 of SOME thms => map (ProofContext.pretty_thm ctxt o fst) (Exn.release thms)
  | NONE => [Pretty.str "[...]"];

fun certificate thy f r =
  case Lazy.peek r
   of SOME thms => (Lazy.value o f thy) (Exn.release thms)
    | NONE => let
        val thy_ref = Theory.check_thy thy;
      in Lazy.lazy (fn () => (f (Theory.deref thy_ref) o Lazy.force) r) end;

fun add_drop_redundant thy (thm, linear) thms =
  let
    val args_of = snd o strip_comb o fst o Logic.dest_equals o Thm.plain_prop_of;
    val args = args_of thm;
    val incr_idx = Logic.incr_indexes ([], Thm.maxidx_of thm + 1);
    fun matches_args args' = length args <= length args' andalso
      Pattern.matchess thy (args, (map incr_idx o curry Library.take (length args)) args');
    fun drop (thm', linear') = if (linear orelse not linear')
      andalso matches_args (args_of thm') then 
        (warning ("Code generator: dropping redundant code equation\n" ^ Display.string_of_thm thm'); true)
      else false;
  in (thm, linear) :: filter_out drop thms end;

fun add_thm thy _ thm (false, thms) = (false, Lazy.map_force (add_drop_redundant thy thm) thms)
  | add_thm thy true thm (true, thms) = (true, Lazy.map_force (fn thms => thms @ [thm]) thms)
  | add_thm thy false thm (true, thms) = (false, Lazy.value [thm]);

fun add_lthms lthms _ = (false, lthms);

fun del_thm thm = (apsnd o Lazy.map_force) (remove (eq_fst Thm.eq_thm_prop) (thm, true));


(* specification data *)

datatype spec = Spec of {
  concluded_history: bool,
  eqns: ((bool * eqns) * (serial * eqns) list) Symtab.table
    (*with explicit history*),
  dtyps: ((serial * ((string * sort) list * (string * typ list) list)) list) Symtab.table
    (*with explicit history*),
  cases: (int * string list) Symtab.table * unit Symtab.table
};

fun mk_spec ((concluded_history, eqns), (dtyps, cases)) =
  Spec { concluded_history = concluded_history, eqns = eqns, dtyps = dtyps, cases = cases };
fun map_spec f (Spec { concluded_history = concluded_history, eqns = eqns,
  dtyps = dtyps, cases = cases }) =
  mk_spec (f ((concluded_history, eqns), (dtyps, cases)));
fun merge_spec (Spec { concluded_history = _, eqns = eqns1, dtyps = dtyps1, cases = (cases1, undefs1) },
  Spec { concluded_history = _, eqns = eqns2, dtyps = dtyps2, cases = (cases2, undefs2) }) =
  let
    fun merge_eqns ((_, history1), (_, history2)) =
      let
        val raw_history = AList.merge (op =) (K true) (history1, history2)
        val filtered_history = filter_out (fst o snd) raw_history
        val history = if null filtered_history
          then raw_history else filtered_history;
      in ((false, (snd o hd) history), history) end;
    val eqns = Symtab.join (K merge_eqns) (eqns1, eqns2);
    val dtyps = Symtab.join (K (AList.merge (op =) (K true))) (dtyps1, dtyps2);
    val cases = (Symtab.merge (K true) (cases1, cases2),
      Symtab.merge (K true) (undefs1, undefs2));
  in mk_spec ((false, eqns), (dtyps, cases)) end;


(* pre- and postprocessor *)

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
val empty_exec = mk_exec (mk_thmproc ((Simplifier.empty_ss, Simplifier.empty_ss), []),
  mk_spec ((false, Symtab.empty), (Symtab.empty, (Symtab.empty, Symtab.empty))));

fun the_thmproc (Exec { thmproc = Thmproc x, ...}) = x;
fun the_spec (Exec { spec = Spec x, ...}) = x;
val the_eqns = #eqns o the_spec;
val the_dtyps = #dtyps o the_spec;
val the_cases = #cases o the_spec;
val map_thmproc = map_exec o apfst o map_thmproc;
val map_concluded_history = map_exec o apsnd o map_spec o apfst o apfst;
val map_eqns = map_exec o apsnd o map_spec o apfst o apsnd;
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


(* tackling equation history *)

fun get_eqns thy c =
  Symtab.lookup ((the_eqns o the_exec) thy) c
  |> Option.map (Lazy.force o snd o snd o fst)
  |> these;

fun continue_history thy = if (#concluded_history o the_spec o the_exec) thy
  then thy
    |> (CodeData.map o apfst o map_concluded_history) (K false)
    |> SOME
  else NONE;

fun conclude_history thy = if (#concluded_history o the_spec o the_exec) thy
  then NONE
  else thy
    |> (CodeData.map o apfst)
        ((map_eqns o Symtab.map) (fn ((changed, current), history) =>
          ((false, current),
            if changed then (serial (), current) :: history else history))
        #> map_concluded_history (K true))
    |> SOME;

val _ = Context.>> (Context.map_theory (CodeData.init
  #> Theory.at_begin continue_history
  #> Theory.at_end conclude_history));


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
      |> (map o apsnd) (snd o fst)
      |> sort (string_ord o pairself fst);
    val dtyps = the_dtyps exec
      |> Symtab.dest
      |> map (fn (dtco, (_, (vs, cos)) :: _) =>
          (Syntax.string_of_typ_global thy (Type (dtco, map TFree vs)), cos))
      |> sort (string_ord o pairself fst)
  in
    (Pretty.writeln o Pretty.chunks) [
      Pretty.block (
        Pretty.str "code equations:"
        :: Pretty.fbrk
        :: (Pretty.fbreaks o map pretty_eqn) eqns
      ),
      Pretty.block [
        Pretty.str "preprocessing simpset:",
        Pretty.fbrk,
        Simplifier.pretty_ss pre
      ],
      Pretty.block [
        Pretty.str "postprocessing simpset:",
        Pretty.fbrk,
        Simplifier.pretty_ss post
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

fun common_typ_eqns thy [] = []
  | common_typ_eqns thy [thm] = [thm]
  | common_typ_eqns thy (thms as thm :: _) = (*FIXME is too general*)
      let
        fun incr_thm thm max =
          let
            val thm' = incr_indexes max thm;
            val max' = Thm.maxidx_of thm' + 1;
          in (thm', max') end;
        val (thms', maxidx) = fold_map incr_thm thms 0;
        val ty1 :: tys = map (snd o Code_Unit.const_typ_eqn) thms';
        fun unify ty env = Sign.typ_unify thy (ty1, ty) env
          handle Type.TUNIFY =>
            error ("Type unificaton failed, while unifying code equations\n"
            ^ (cat_lines o map Display.string_of_thm) thms
            ^ "\nwith types\n"
            ^ (cat_lines o map (Code_Unit.string_of_typ thy)) (ty1 :: tys));
        val (env, _) = fold unify tys (Vartab.empty, maxidx)
        val instT = Vartab.fold (fn (x_i, (sort, ty)) =>
          cons (Thm.ctyp_of thy (TVar (x_i, sort)), Thm.ctyp_of thy ty)) env [];
      in map (Thm.instantiate (instT, [])) thms' end;

fun check_linear (eqn as (thm, linear)) =
  if linear then eqn else Code_Unit.bad_thm
    ("Duplicate variables on left hand side of code equation:\n"
      ^ Display.string_of_thm thm);

fun mk_eqn thy linear =
  Code_Unit.error_thm ((if linear then check_linear else I) o Code_Unit.mk_eqn thy);
fun mk_syntactic_eqn thy = Code_Unit.warning_thm (Code_Unit.mk_eqn thy);
fun mk_default_eqn thy = Code_Unit.try_thm (check_linear o Code_Unit.mk_eqn thy);


(** operational sort algebra and class discipline **)

local

fun arity_constraints thy algebra (class, tyco) =
  let
    val base_constraints = Sorts.mg_domain algebra tyco [class];
    val classparam_constraints = Sorts.complete_sort algebra [class]
      |> maps (map fst o these o try (#params o AxClass.get_info thy))
      |> map_filter (fn c => try (AxClass.param_of_inst thy) (c, tyco))
      |> maps (map fst o get_eqns thy)
      |> map (map (snd o dest_TVar) o Sign.const_typargs thy o Code_Unit.const_typ_eqn);
    val inter_sorts = map2 (curry (Sorts.inter_sort algebra));
  in fold inter_sorts classparam_constraints base_constraints end;

fun retrieve_algebra thy operational =
  Sorts.subalgebra (Syntax.pp_global thy) operational
    (arity_constraints thy (Sign.classes_of thy))
    (Sign.classes_of thy);

in

fun coregular_algebra thy = retrieve_algebra thy (K true) |> snd;
fun operational_algebra thy =
  let
    fun add_iff_operational class =
      can (AxClass.get_info thy) class ? cons class;
    val operational_classes = fold add_iff_operational (Sign.all_classes thy) []
  in retrieve_algebra thy (member (op =) operational_classes) end;

end; (*local*)


(** interfaces and attributes **)

fun delete_force msg key xs =
  if AList.defined (op =) xs key then AList.delete (op =) key xs
  else error ("No such " ^ msg ^ ": " ^ quote key);

fun get_datatype thy tyco =
  case these (Symtab.lookup ((the_dtyps o the_exec) thy) tyco)
   of (_, spec) :: _ => spec
    | [] => Sign.arity_number thy tyco
        |> Name.invents Name.context Name.aT
        |> map (rpair [])
        |> rpair [];

fun get_datatype_of_constr thy c =
  case (snd o strip_type o Sign.the_const_type thy) c
   of Type (tyco, _) => if member (op =) ((map fst o snd o get_datatype thy) tyco) c
       then SOME tyco else NONE
    | _ => NONE;

fun recheck_eqn thy = Code_Unit.error_thm
  (Code_Unit.assert_linear (is_some o get_datatype_of_constr thy) o apfst (Code_Unit.assert_eqn thy));

fun recheck_eqns_const thy c eqns =
  let
    fun cert (eqn as (thm, _)) = if c = Code_Unit.const_eqn thm
      then eqn else error ("Wrong head of code equation,\nexpected constant "
        ^ Code_Unit.string_of_const thy c ^ "\n" ^ Display.string_of_thm thm)
  in map (cert o recheck_eqn thy) eqns end;

fun change_eqns delete c f = (map_exec_purge (SOME [c]) o map_eqns
  o (if delete then Symtab.map_entry c else Symtab.map_default (c, ((false, (true, Lazy.value [])), [])))
    o apfst) (fn (_, eqns) => (true, f eqns));

fun gen_add_eqn linear default thm thy =
  case (if default then mk_default_eqn thy else SOME o mk_eqn thy linear) thm
   of SOME (thm, _) =>
        let
          val c = Code_Unit.const_eqn thm;
          val _ = if not default andalso (is_some o AxClass.class_of_param thy) c
            then error ("Rejected polymorphic code equation for overloaded constant:\n"
              ^ Display.string_of_thm thm)
            else ();
          val _ = if not default andalso (is_some o get_datatype_of_constr thy) c
            then error ("Rejected code equation for datatype constructor:\n"
              ^ Display.string_of_thm thm)
            else ();
        in change_eqns false c (add_thm thy default (thm, linear)) thy end
    | NONE => thy;

val add_eqn = gen_add_eqn true false;
val add_default_eqn = gen_add_eqn true true;
val add_nonlinear_eqn = gen_add_eqn false false;

fun add_eqnl (c, lthms) thy =
  let
    val lthms' = certificate thy (fn thy => recheck_eqns_const thy c) lthms;
  in change_eqns false c (add_lthms lthms') thy end;

val add_default_eqn_attribute = Thm.declaration_attribute
  (fn thm => Context.mapping (add_default_eqn thm) I);
val add_default_eqn_attrib = Attrib.internal (K add_default_eqn_attribute);

fun del_eqn thm thy = case mk_syntactic_eqn thy thm
 of SOME (thm, _) => change_eqns true (Code_Unit.const_eqn thm) (del_thm thm) thy
  | NONE => thy;

fun del_eqns c = change_eqns true c (K (false, Lazy.value []));

fun get_case_scheme thy c = case Symtab.lookup ((fst o the_cases o the_exec) thy) c
 of SOME (base_case_scheme as (_, case_pats)) =>
      if forall (is_some o get_datatype_of_constr thy) case_pats
      then SOME (1 + Int.max (1, length case_pats), base_case_scheme)
      else NONE
  | NONE => NONE;

val is_undefined = Symtab.defined o snd o the_cases o the_exec;

structure TypeInterpretation = InterpretationFun(type T = string * serial val eq = eq_snd (op =) : T * T -> bool);

fun add_datatype raw_cs thy =
  let
    val cs = map (fn c_ty as (_, ty) => (AxClass.unoverload_const thy c_ty, ty)) raw_cs;
    val (tyco, vs_cos) = Code_Unit.constrset_of_consts thy cs;
  in
    thy
    |> map_exec_purge NONE
        ((map_dtyps o Symtab.map_default (tyco, [])) (cons (serial (), vs_cos))
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

val add_inline = map_pre o MetaSimplifier.add_simp;
val del_inline = map_pre o MetaSimplifier.del_simp;
val add_post = map_post o MetaSimplifier.add_simp;
val del_post = map_post o MetaSimplifier.del_simp;
  
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
    #> add_del_attribute ("", (add_eqn, del_eqn))
    #> add_simple_attribute ("nbe", add_nonlinear_eqn)
    #> add_del_attribute ("inline", (add_inline, del_inline))
    #> add_del_attribute ("post", (add_post, del_post))
  end));


(** post- and preprocessing **)

local

fun apply_functrans thy c _ [] = []
  | apply_functrans thy c [] eqns = eqns
  | apply_functrans thy c functrans eqns = eqns
      |> perhaps (perhaps_loop (perhaps_apply functrans))
      |> (map o apfst) (AxClass.unoverload thy)
      |> recheck_eqns_const thy c
      |> (map o apfst) (AxClass.overload thy);

fun rhs_conv conv thm = Thm.transitive thm ((conv o Thm.rhs_of) thm);

fun term_of_conv thy f =
  Thm.cterm_of thy
  #> f
  #> Thm.prop_of
  #> Logic.dest_equals
  #> snd;

fun preprocess thy functrans c eqns =
  let
    val pre = (Simplifier.theory_context thy o #pre o the_thmproc o the_exec) thy;
  in
    eqns
    |> (map o apfst) (AxClass.overload thy)
    |> apply_functrans thy c functrans
    |> (map o apfst) (Code_Unit.rewrite_eqn pre)
    |> (map o apfst) (AxClass.unoverload thy)
    |> map (recheck_eqn thy)
    |> burrow_fst (common_typ_eqns thy)
  end;

in

fun preprocess_conv thy ct =
  let
    val pre = (Simplifier.theory_context thy o #pre o the_thmproc o the_exec) thy;
  in
    ct
    |> Simplifier.rewrite pre
    |> rhs_conv (AxClass.unoverload_conv thy)
  end;

fun preprocess_term thy = term_of_conv thy (preprocess_conv thy);

fun postprocess_conv thy ct =
  let
    val post = (Simplifier.theory_context thy o #post o the_thmproc o the_exec) thy;
  in
    ct
    |> AxClass.overload_conv thy
    |> rhs_conv (Simplifier.rewrite post)
  end;

fun postprocess_term thy = term_of_conv thy (postprocess_conv thy);

fun these_raw_eqns thy c =
  get_eqns thy c
  |> (map o apfst) (Thm.transfer thy)
  |> burrow_fst (common_typ_eqns thy);

fun these_eqns thy c =
  let
    val functrans = (map (fn (_, (_, f)) => f thy) o #functrans
      o the_thmproc o the_exec) thy;
  in
    get_eqns thy c
    |> (map o apfst) (Thm.transfer thy)
    |> preprocess thy functrans c
  end;

fun default_typscheme thy c =
  let
    fun the_const_typscheme c = (curry (Code_Unit.typscheme thy) c o snd o dest_Const
      o TermSubst.zero_var_indexes o curry Const "" o Sign.the_const_type thy) c;
    fun strip_sorts (vs, ty) = (map (fn (v, _) => (v, [])) vs, ty);
  in case AxClass.class_of_param thy c
   of SOME class => ([(Name.aT, [class])], snd (the_const_typscheme c))
    | NONE => if is_some (get_datatype_of_constr thy c)
        then strip_sorts (the_const_typscheme c)
        else case get_eqns thy c
         of (thm, _) :: _ => snd (Code_Unit.head_eqn thy (Drule.zero_var_indexes thm))
          | [] => strip_sorts (the_const_typscheme c) end;

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
