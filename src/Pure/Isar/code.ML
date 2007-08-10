(*  Title:      Pure/Isar/code.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Abstract executable content of theory.  Management of data dependent on
executable content.
*)

signature CODE =
sig
  val add_func: bool -> thm -> theory -> theory
  val del_func: thm -> theory -> theory
  val add_funcl: CodeUnit.const * thm list Susp.T -> theory -> theory
  val add_func_attr: bool -> Attrib.src
  val add_inline: thm -> theory -> theory
  val del_inline: thm -> theory -> theory
  val add_inline_proc: string * (theory -> cterm list -> thm list) -> theory -> theory
  val del_inline_proc: string -> theory -> theory
  val add_preproc: string * (theory -> thm list -> thm list) -> theory -> theory
  val del_preproc: string -> theory -> theory
  val add_post: thm -> theory -> theory
  val del_post: thm -> theory -> theory
  val add_datatype: string * ((string * sort) list * (string * typ list) list)
    -> theory -> theory
  val add_datatype_consts: CodeUnit.const list -> theory -> theory
  val add_datatype_consts_cmd: string list -> theory -> theory

  val coregular_algebra: theory -> Sorts.algebra
  val operational_algebra: theory -> (sort -> sort) * Sorts.algebra
  val these_funcs: theory -> CodeUnit.const -> thm list
  val get_datatype: theory -> string -> ((string * sort) list * (string * typ list) list)
  val get_datatype_of_constr: theory -> CodeUnit.const -> string option
  val default_typ: theory -> CodeUnit.const -> typ

  val preprocess_conv: cterm -> thm
  val postprocess_conv: cterm -> thm

  val add_attribute: string * (Args.T list -> attribute * Args.T list) -> theory -> theory

  val print_codesetup: theory -> unit
end;

signature CODE_DATA_ARGS =
sig
  type T
  val empty: T
  val merge: Pretty.pp -> T * T -> T
  val purge: theory option -> CodeUnit.const list option -> T -> T
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
  val declare_data: Object.T -> (Pretty.pp -> Object.T * Object.T -> Object.T)
    -> (theory option -> CodeUnit.const list option -> Object.T -> Object.T) -> serial
  val get_data: serial * ('a -> Object.T) * (Object.T -> 'a)
    -> theory -> 'a
  val change_data: serial * ('a -> Object.T) * (Object.T -> 'a)
    -> theory -> ('a -> 'a) -> 'a
  val change_yield_data: serial * ('a -> Object.T) * (Object.T -> 'a)
    -> theory -> ('a -> 'b * 'a) -> 'b * 'a
end;

structure Code : PRIVATE_CODE =
struct

(** preliminaries **)

structure Consttab = CodeUnit.Consttab;


(* certificate theorems *)

fun string_of_lthms r = case Susp.peek r
 of SOME thms => (map string_of_thm o rev) thms
  | NONE => ["[...]"];

fun pretty_lthms ctxt r = case Susp.peek r
 of SOME thms => map (ProofContext.pretty_thm ctxt) thms
  | NONE => [Pretty.str "[...]"];

fun certificate thy f r =
  case Susp.peek r
   of SOME thms => (Susp.value o f thy) thms
     | NONE => let
          val thy_ref = Theory.check_thy thy;
        in Susp.delay (fn () => (f (Theory.deref thy_ref) o Susp.force) r) end;

fun merge' _ ([], []) = (false, [])
  | merge' _ ([], ys) = (true, ys)
  | merge' eq (xs, ys) = fold_rev
      (fn y => fn (t, xs) => (t orelse not (member eq xs y), insert eq y xs)) ys (false, xs);

fun merge_alist eq_key eq (xys as (xs, ys)) =
  if eq_list (eq_pair eq_key eq) (xs, ys)
  then (false, xs)
  else (true, AList.merge eq_key eq xys);

val merge_thms = merge' Thm.eq_thm_prop;

fun merge_lthms (r1, r2) =
  if Susp.same (r1, r2)
    then (false, r1)
  else case Susp.peek r1
   of SOME [] => (true, r2)
    | _ => case Susp.peek r2
       of SOME [] => (true, r1)
        | _ => (apsnd (Susp.delay o K)) (merge_thms (Susp.force r1, Susp.force r2));


(* pairs of (selected, deleted) defining equations *)

type sdthms = thm list Susp.T * thm list;

fun add_drop_redundant thm (sels, dels) =
  let
    val thy = Thm.theory_of_thm thm;
    val args_of = snd o strip_comb o fst o Logic.dest_equals o Thm.plain_prop_of;
    val args = args_of thm;
    fun matches [] _ = true
      | matches (Var _ :: xs) [] = matches xs []
      | matches (_ :: _) [] = false
      | matches (x :: xs) (y :: ys) = Pattern.matches thy (x, y) andalso matches xs ys;
    fun drop thm' = not (matches args (args_of thm'))
      orelse (warning ("code generator: dropping redundant defining equation\n" ^ string_of_thm thm'); false);
    val (keeps, drops) = List.partition drop sels;
  in (thm :: keeps, dels |> remove Thm.eq_thm_prop thm |> fold (insert Thm.eq_thm_prop) drops) end;

fun add_thm thm (sels, dels) =
  apfst Susp.value (add_drop_redundant thm (Susp.force sels, dels));

fun add_lthms lthms (sels, []) =
      (Susp.delay (fn () => fold add_drop_redundant
        (Susp.force lthms) (Susp.force sels, []) |> fst), [])
        (*FIXME*)
  | add_lthms lthms (sels, dels) =
      fold add_thm (Susp.force lthms) (sels, dels);

fun del_thm thm (sels, dels) =
  (Susp.value (remove Thm.eq_thm_prop thm (Susp.force sels)), thm :: dels);

fun pretty_sdthms ctxt (sels, _) = pretty_lthms ctxt sels;

fun merge_sdthms ((sels1, dels1), (sels2, dels2)) =
  let
    val (dels_t, dels) = merge_thms (dels1, dels2);
  in if dels_t
    then let
      val (_, sels) = merge_thms
        (subtract Thm.eq_thm_prop dels2 (Susp.force sels1), Susp.force sels2);
      val (_, dels) = merge_thms
        (subtract Thm.eq_thm_prop (Susp.force sels2) dels1, dels2);
    in (true, ((Susp.delay o K) sels, dels)) end
    else let
      val (sels_t, sels) = merge_lthms (sels1, sels2);
    in (sels_t, (sels, dels)) end
  end;


(* code attributes *)

structure CodeAttr = TheoryDataFun (
  type T = (string * (Args.T list -> attribute * Args.T list)) list;
  val empty = [];
  val copy = I;
  val extend = I;
  fun merge _ = AList.merge (op =) (K true);
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
    Context.add_setup (Attrib.add_attributes
      [("code", code_attr, "declare theorems for code generation")])
  end;



(** exeuctable content **)

datatype thmproc = Preproc of {
  inlines: thm list,
  inline_procs: (string * (serial * (theory -> cterm list -> thm list))) list,
  preprocs: (string * (serial * (theory -> thm list -> thm list))) list,
  posts: thm list
};

fun mk_thmproc (((inlines, inline_procs), preprocs), posts) =
  Preproc { inlines = inlines, inline_procs = inline_procs, preprocs = preprocs,
    posts = posts };
fun map_thmproc f (Preproc { inlines, inline_procs, preprocs, posts }) =
  mk_thmproc (f (((inlines, inline_procs), preprocs), posts));
fun merge_thmproc (Preproc { inlines = inlines1, inline_procs = inline_procs1,
    preprocs = preprocs1, posts = posts1 },
  Preproc { inlines = inlines2, inline_procs = inline_procs2,
      preprocs = preprocs2, posts= posts2 }) =
    let
      val (touched1, inlines) = merge_thms (inlines1, inlines2);
      val (touched2, inline_procs) = merge_alist (op =) (eq_fst (op =)) (inline_procs1, inline_procs2);
      val (touched3, preprocs) = merge_alist (op =) (eq_fst (op =)) (preprocs1, preprocs2);
      val (_, posts) = merge_thms (posts1, posts2);
    in (touched1 orelse touched2 orelse touched3,
      mk_thmproc (((inlines, inline_procs), preprocs), posts)) end;

fun join_func_thms (tabs as (tab1, tab2)) =
  let
    val cs1 = Consttab.keys tab1;
    val cs2 = Consttab.keys tab2;
    val cs' = filter (member CodeUnit.eq_const cs2) cs1;
    val cs'' = subtract (op =) cs' cs1 @ subtract (op =) cs' cs2;
    val cs''' = ref [] : CodeUnit.const list ref;
    fun merge c x = let val (touched, thms') = merge_sdthms x in
      (if touched then cs''' := cons c (!cs''') else (); thms') end;
  in (cs'' @ !cs''', Consttab.join merge tabs) end;
fun merge_funcs (thms1, thms2) =
  let
    val (consts, thms) = join_func_thms (thms1, thms2);
  in (SOME consts, thms) end;

val eq_string = op = : string * string -> bool;
val eq_co = op = : (string * typ list) * (string * typ list) -> bool;
fun eq_dtyp ((vs1, cs1), (vs2, cs2)) = 
  gen_eq_set (eq_pair eq_string (gen_eq_set eq_string)) (vs1, vs2)
    andalso gen_eq_set eq_co (cs1, cs2);
fun merge_dtyps (tabs as (tab1, tab2)) =
  let
    val tycos1 = Symtab.keys tab1;
    val tycos2 = Symtab.keys tab2;
    val tycos' = filter (member eq_string tycos2) tycos1;
    val new_types = not (gen_eq_set (op =) (tycos1, tycos2));
    val diff_types = not (gen_eq_set (eq_pair (op =) eq_dtyp)
      (AList.make (the o Symtab.lookup tab1) tycos',
       AList.make (the o Symtab.lookup tab2) tycos'));
    fun join _ (cos as (_, cos2)) = if eq_dtyp cos
      then raise Symtab.SAME else cos2;
  in ((new_types, diff_types), Symtab.join join tabs) end;

datatype spec = Spec of {
  funcs: sdthms Consttab.table,
  dtyps: ((string * sort) list * (string * typ list) list) Symtab.table
};

fun mk_spec (funcs, dtyps) =
  Spec { funcs = funcs, dtyps = dtyps };
fun map_spec f (Spec { funcs = funcs, dtyps = dtyps }) =
  mk_spec (f (funcs, dtyps));
fun merge_spec (Spec { funcs = funcs1, dtyps = dtyps1 },
  Spec { funcs = funcs2, dtyps = dtyps2 }) =
  let
    val (touched_cs, funcs) = merge_funcs (funcs1, funcs2);
    val ((new_types, diff_types), dtyps) = merge_dtyps (dtyps1, dtyps2);
    val touched = if new_types orelse diff_types then NONE else touched_cs;
  in (touched, mk_spec (funcs, dtyps)) end;

datatype exec = Exec of {
  thmproc: thmproc,
  spec: spec
};

fun mk_exec (thmproc, spec) =
  Exec { thmproc = thmproc, spec = spec };
fun map_exec f (Exec { thmproc = thmproc, spec = spec }) =
  mk_exec (f (thmproc, spec));
fun merge_exec (Exec { thmproc = thmproc1, spec = spec1 },
  Exec { thmproc = thmproc2, spec = spec2 }) =
  let
    val (touched', thmproc) = merge_thmproc (thmproc1, thmproc2);
    val (touched_cs, spec) = merge_spec (spec1, spec2);
    val touched = if touched' then NONE else touched_cs;
  in (touched, mk_exec (thmproc, spec)) end;
val empty_exec = mk_exec (mk_thmproc ((([], []), []), []),
  mk_spec (Consttab.empty, Symtab.empty));

fun the_thmproc (Exec { thmproc = Preproc x, ...}) = x;
fun the_spec (Exec { spec = Spec x, ...}) = x;
val the_funcs = #funcs o the_spec;
val the_dtyps = #dtyps o the_spec;
val map_thmproc = map_exec o apfst o map_thmproc;
val map_funcs = map_exec o apsnd o map_spec o apfst;
val map_dtyps = map_exec o apsnd o map_spec o apsnd;


(* data slots dependent on executable content *)

(*private copy avoids potential conflict of table exceptions*)
structure Datatab = TableFun(type key = int val ord = int_ord);

local

type kind = {
  empty: Object.T,
  merge: Pretty.pp -> Object.T * Object.T -> Object.T,
  purge: theory option -> CodeUnit.const list option -> Object.T -> Object.T
};

val kinds = ref (Datatab.empty: kind Datatab.table);
val kind_keys = ref ([]: serial list);

fun invoke f k = case Datatab.lookup (! kinds) k
 of SOME kind => f kind
  | NONE => sys_error "Invalid code data identifier";

in

fun declare_data empty merge purge =
  let
    val k = serial ();
    val kind = {empty = empty, merge = merge, purge = purge};
    val _ = change kinds (Datatab.update (k, kind));
    val _ = change kind_keys (cons k);
  in k end;

fun invoke_empty k = invoke (fn kind => #empty kind) k;

fun invoke_merge_all pp = Datatab.join
  (invoke (fn kind => #merge kind pp));

fun invoke_purge_all thy_opt cs =
  fold (fn k => Datatab.map_entry k
    (invoke (fn kind => #purge kind thy_opt cs) k)) (! kind_keys);

end; (*local*)


(* theory store *)

local

type data = Object.T Datatab.table;

structure CodeData = TheoryDataFun
(
  type T = exec * data ref;
  val empty = (empty_exec, ref Datatab.empty : data ref);
  fun copy (exec, data) = (exec, ref (! data));
  val extend = copy;
  fun merge pp ((exec1, data1), (exec2, data2)) =
    let
      val (touched, exec) = merge_exec (exec1, exec2);
      val data1' = invoke_purge_all NONE touched (! data1);
      val data2' = invoke_purge_all NONE touched (! data2);
      val data = invoke_merge_all pp (data1', data2');
    in (exec, ref data) end;
);

val _ = Context.add_setup CodeData.init;

fun ch r f = let val x = f (! r) in (r := x; x) end;
fun thy_data f thy = f ((snd o CodeData.get) thy);

fun get_ensure_init kind data_ref =
  case Datatab.lookup (! data_ref) kind
   of SOME x => x
    | NONE => let val y = invoke_empty kind
        in (change data_ref (Datatab.update (kind, y)); y) end;

in

(* access to executable content *)

val get_exec = fst o CodeData.get;

fun map_exec_purge touched f thy =
  CodeData.map (fn (exec, data) => 
    (f exec, ref (invoke_purge_all (SOME thy) touched (! data)))) thy;


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
    val exec = get_exec thy;
    fun pretty_func (s, lthms) =
      (Pretty.block o Pretty.fbreaks) (
        Pretty.str s :: pretty_sdthms ctxt lthms
      );
    fun pretty_dtyp (s, []) =
          Pretty.str s
      | pretty_dtyp (s, cos) =
          (Pretty.block o Pretty.breaks) (
            Pretty.str s
            :: Pretty.str "="
            :: separate (Pretty.str "|") (map (fn (c, []) => Pretty.str c
                 | (c, tys) =>
                     (Pretty.block o Pretty.breaks)
                        (Pretty.str c :: Pretty.str "of" :: map (Pretty.quote o Sign.pretty_typ thy) tys)) cos)
          );
    val inlines = (#inlines o the_thmproc) exec;
    val inline_procs = (map fst o #inline_procs o the_thmproc) exec;
    val preprocs = (map fst o #preprocs o the_thmproc) exec;
    val funs = the_funcs exec
      |> Consttab.dest
      |> (map o apfst) (CodeUnit.string_of_const thy)
      |> sort (string_ord o pairself fst);
    val dtyps = the_dtyps exec
      |> Symtab.dest
      |> map (fn (dtco, (vs, cos)) => (Sign.string_of_typ thy (Type (dtco, map TFree vs)), cos))
      |> sort (string_ord o pairself fst)
  in
    (Pretty.writeln o Pretty.chunks) [
      Pretty.block (
        Pretty.str "defining equations:"
        :: Pretty.fbrk
        :: (Pretty.fbreaks o map pretty_func) funs
      ),
      Pretty.block (
        Pretty.str "inlining theorems:"
        :: Pretty.fbrk
        :: (Pretty.fbreaks o map (ProofContext.pretty_thm ctxt)) inlines
      ),
      Pretty.block (
        Pretty.str "inlining procedures:"
        :: Pretty.fbrk
        :: (Pretty.fbreaks o map Pretty.str) inline_procs
      ),
      Pretty.block (
        Pretty.str "preprocessors:"
        :: Pretty.fbrk
        :: (Pretty.fbreaks o map Pretty.str) preprocs
      ),
      Pretty.block (
        Pretty.str "datatypes:"
        :: Pretty.fbrk
        :: (Pretty.fbreaks o map pretty_dtyp) dtyps
      )
    ]
  end;



(** theorem transformation and certification **)

fun common_typ_funcs [] = []
  | common_typ_funcs [thm] = [thm]
  | common_typ_funcs (thms as thm :: _) =
      let
        val thy = Thm.theory_of_thm thm;
        fun incr_thm thm max =
          let
            val thm' = incr_indexes max thm;
            val max' = Thm.maxidx_of thm' + 1;
          in (thm', max') end;
        val (thms', maxidx) = fold_map incr_thm thms 0;
        val ty1 :: tys = map (snd o CodeUnit.head_func) thms';
        fun unify ty env = Sign.typ_unify thy (ty1, ty) env
          handle Type.TUNIFY =>
            error ("Type unificaton failed, while unifying defining equations\n"
            ^ (cat_lines o map Display.string_of_thm) thms
            ^ "\nwith types\n"
            ^ (cat_lines o map (CodeUnit.string_of_typ thy)) (ty1 :: tys));
        val (env, _) = fold unify tys (Vartab.empty, maxidx)
        val instT = Vartab.fold (fn (x_i, (sort, ty)) =>
          cons (Thm.ctyp_of thy (TVar (x_i, sort)), Thm.ctyp_of thy ty)) env [];
      in map (Thm.instantiate (instT, [])) thms' end;

fun certify_const thy const thms =
  let
    fun cert thm = if CodeUnit.eq_const (const, fst (CodeUnit.head_func thm))
      then thm else error ("Wrong head of defining equation,\nexpected constant "
        ^ CodeUnit.string_of_const thy const ^ "\n" ^ string_of_thm thm)
  in map cert thms end;



(** operational sort algebra and class discipline **)

local

fun aggr_neutr f y [] = y
  | aggr_neutr f y (x::xs) = aggr_neutr f (f y x) xs;

fun aggregate f [] = NONE
  | aggregate f (x::xs) = SOME (aggr_neutr f x xs);

fun inter_sorts thy =
  let
    val algebra = Sign.classes_of thy;
    val inters = curry (Sorts.inter_sort algebra);
  in aggregate (map2 inters) end;

fun specific_constraints thy (class, tyco) =
  let
    val vs = Name.invents Name.context "" (Sign.arity_number thy tyco);
    val clsops = (these o Option.map snd o try (AxClass.params_of_class thy)) class;
    val funcs = clsops
      |> map (fn (clsop, _) => (clsop, SOME tyco))
      |> map (Consttab.lookup ((the_funcs o get_exec) thy))
      |> (map o Option.map) (Susp.force o fst)
      |> maps these
      |> map (Thm.transfer thy);
    val sorts = map (map (snd o dest_TVar) o snd o dest_Type o the_single
      o Sign.const_typargs thy o (fn ((c, _), ty) => (c, ty)) o CodeUnit.head_func) funcs;
  in sorts end;

fun weakest_constraints thy (class, tyco) =
  let
    val all_superclasses = class :: Graph.all_succs ((#classes o Sorts.rep_algebra o Sign.classes_of) thy) [class];
  in case inter_sorts thy (maps (fn class => specific_constraints thy (class, tyco)) all_superclasses)
   of SOME sorts => sorts
    | NONE => Sign.arity_sorts thy tyco [class]
  end;

fun strongest_constraints thy (class, tyco) =
  let
    val algebra = Sign.classes_of thy;
    val all_subclasses = class :: Graph.all_preds ((#classes o Sorts.rep_algebra) algebra) [class];
    val inst_subclasses = filter (can (Sorts.mg_domain algebra tyco) o single) all_subclasses;
  in case inter_sorts thy (maps (fn class => specific_constraints thy (class, tyco)) inst_subclasses)
   of SOME sorts => sorts
    | NONE => replicate
        (Sign.arity_number thy tyco) (Sign.certify_sort thy (Sign.all_classes thy))
  end;

fun gen_classop_typ constr thy class (c, tyco) = 
  let
    val (var, cs) = try (AxClass.params_of_class thy) class |> the_default ("'a", [])
    val ty = (the o AList.lookup (op =) cs) c;
    val sort_args = Name.names (Name.declare var Name.context) "'a"
      (constr thy (class, tyco));
    val ty_inst = Type (tyco, map TFree sort_args);
  in Logic.varifyT (map_type_tfree (K ty_inst) ty) end;

fun retrieve_algebra thy operational =
  Sorts.subalgebra (Sign.pp thy) operational
    (weakest_constraints thy)
    (Sign.classes_of thy);

in

fun coregular_algebra thy = retrieve_algebra thy (K true) |> snd;
fun operational_algebra thy =
  let
    fun add_iff_operational class =
      can (AxClass.get_definition thy) class ? cons class;
    val operational_classes = fold add_iff_operational (Sign.all_classes thy) []
  in retrieve_algebra thy (member (op =) operational_classes) end;

val classop_weakest_typ = gen_classop_typ weakest_constraints;
val classop_strongest_typ = gen_classop_typ strongest_constraints;

fun assert_func_typ thm =
  let
    val thy = Thm.theory_of_thm thm;
    fun check_typ_classop class (const as (c, SOME tyco), thm) =
          let
            val (_, ty) = CodeUnit.head_func thm;
            val ty_decl = classop_weakest_typ thy class (c, tyco);
            val ty_strongest = classop_strongest_typ thy class (c, tyco);
            fun constrain thm = 
              let
                val max = Thm.maxidx_of thm + 1;
                val ty_decl' = Logic.incr_tvar max ty_decl;
                val (_, ty') = CodeUnit.head_func thm;
                val (env, _) = Sign.typ_unify thy (ty_decl', ty') (Vartab.empty, max);
                val instT = Vartab.fold (fn (x_i, (sort, ty)) =>
                  cons (Thm.ctyp_of thy (TVar (x_i, sort)), Thm.ctyp_of thy ty)) env [];
              in Thm.instantiate (instT, []) thm end;
          in if Sign.typ_instance thy (ty_strongest, ty)
            then if Sign.typ_instance thy (ty, ty_decl)
            then thm
            else (warning ("Constraining type\n" ^ CodeUnit.string_of_typ thy ty
              ^ "\nof defining equation\n"
              ^ string_of_thm thm
              ^ "\nto permitted most general type\n"
              ^ CodeUnit.string_of_typ thy ty_decl);
              constrain thm)
            else CodeUnit.bad_thm ("Type\n" ^ CodeUnit.string_of_typ thy ty
              ^ "\nof defining equation\n"
              ^ string_of_thm thm
              ^ "\nis incompatible with permitted least general type\n"
              ^ CodeUnit.string_of_typ thy ty_strongest)
          end
      | check_typ_classop class ((c, NONE), thm) =
          CodeUnit.bad_thm ("Illegal type for class operation " ^ quote c
           ^ "\nin defining equation\n"
           ^ string_of_thm thm);
    fun check_typ_fun (const as (c, _), thm) =
      let
        val (_, ty) = CodeUnit.head_func thm;
        val ty_decl = Sign.the_const_type thy c;
      in if Sign.typ_equiv thy (Type.strip_sorts ty_decl, Type.strip_sorts ty)
        then thm
        else CodeUnit.bad_thm ("Type\n" ^ CodeUnit.string_of_typ thy ty
           ^ "\nof defining equation\n"
           ^ string_of_thm thm
           ^ "\nis incompatible with declared function type\n"
           ^ CodeUnit.string_of_typ thy ty_decl)
      end;
    fun check_typ (const as (c, _), thm) =
      case AxClass.class_of_param thy c
       of SOME class => check_typ_classop class (const, thm)
        | NONE => check_typ_fun (const, thm);
  in check_typ (fst (CodeUnit.head_func thm), thm) end;

val mk_func = CodeUnit.error_thm
  (assert_func_typ o CodeUnit.mk_func);
val mk_func_liberal = CodeUnit.warning_thm
  (assert_func_typ o CodeUnit.mk_func);

end;



(** interfaces and attributes **)

fun add_func true thm thy =
      let
        val func = mk_func thm;
        val (const, _) = CodeUnit.head_func func;
      in map_exec_purge (SOME [const]) (map_funcs
        (Consttab.map_default
          (const, (Susp.value [], [])) (add_thm func))) thy
      end
  | add_func false thm thy =
      case mk_func_liberal thm
       of SOME func => let
              val (const, _) = CodeUnit.head_func func
            in map_exec_purge (SOME [const]) (map_funcs
              (Consttab.map_default
                (const, (Susp.value [], [])) (add_thm func))) thy
            end
        | NONE => thy;

fun delete_force msg key xs =
  if AList.defined (op =) xs key then AList.delete (op =) key xs
  else error ("No such " ^ msg ^ ": " ^ quote key);

fun del_func thm thy =
  let
    val func = mk_func thm;
    val (const, _) = CodeUnit.head_func func;
  in map_exec_purge (SOME [const]) (map_funcs
    (Consttab.map_entry
      const (del_thm func))) thy
  end;

fun add_funcl (const, lthms) thy =
  let
    val lthms' = certificate thy (fn thy => certify_const thy const) lthms;
      (*FIXME must check compatibility with sort algebra;
        alas, naive checking results in non-termination!*)
  in
    map_exec_purge (SOME [const]) (map_funcs (Consttab.map_default (const, (Susp.value [], []))
      (add_lthms lthms'))) thy
  end;

fun add_func_attr strict = Attrib.internal (fn _ => Thm.declaration_attribute
  (fn thm => Context.mapping (add_func strict thm) I));

local

fun del_datatype tyco thy =
  case Symtab.lookup ((the_dtyps o get_exec) thy) tyco
   of SOME (vs, cos) => let
        val consts = CodeUnit.consts_of_cos thy tyco vs cos;
      in map_exec_purge (if null consts then NONE else SOME consts)
        (map_dtyps (Symtab.delete tyco)) thy end
    | NONE => thy;

in

fun add_datatype (tyco, (vs_cos as (vs, cos))) thy =
  let
    val consts = CodeUnit.consts_of_cos thy tyco vs cos;
  in
    thy
    |> del_datatype tyco
    |> map_exec_purge (SOME consts) (map_dtyps (Symtab.update_new (tyco, vs_cos)))
  end;

fun add_datatype_consts consts thy =
  add_datatype (CodeUnit.cos_of_consts thy consts) thy;

fun add_datatype_consts_cmd raw_cs thy =
  add_datatype_consts (map (CodeUnit.read_const thy) raw_cs) thy

end; (*local*)

fun add_inline thm thy =
  (map_exec_purge NONE o map_thmproc o apfst o apfst o apfst)
    (insert Thm.eq_thm_prop (CodeUnit.error_thm CodeUnit.mk_rew thm)) thy;
        (*fully applied in order to get right context for mk_rew!*)

fun del_inline thm thy =
  (map_exec_purge NONE o map_thmproc o apfst o apfst o apfst)
    (remove Thm.eq_thm_prop (CodeUnit.error_thm CodeUnit.mk_rew thm)) thy;
        (*fully applied in order to get right context for mk_rew!*)

fun add_inline_proc (name, f) =
  (map_exec_purge NONE o map_thmproc o apfst o apfst o apsnd)
    (AList.update (op =) (name, (serial (), f)));

fun del_inline_proc name =
  (map_exec_purge NONE o map_thmproc o apfst o apfst o apsnd)
    (delete_force "inline procedure" name);

fun add_preproc (name, f) =
  (map_exec_purge NONE o map_thmproc o apfst o apsnd)
    (AList.update (op =) (name, (serial (), f)));

fun del_preproc name =
  (map_exec_purge NONE o map_thmproc o apfst o apsnd)
    (delete_force "preprocessor" name);

fun add_post thm thy =
  (map_exec_purge NONE o map_thmproc o apsnd)
    (insert Thm.eq_thm_prop (CodeUnit.error_thm CodeUnit.mk_rew thm)) thy;
        (*fully applied in order to get right context for mk_rew!*)

fun del_post thm thy =
  (map_exec_purge NONE o map_thmproc o apsnd)
    (remove Thm.eq_thm_prop (CodeUnit.error_thm CodeUnit.mk_rew thm)) thy;
        (*fully applied in order to get right context for mk_rew!*)

val _ = Context.add_setup
  (let
    fun mk_attribute f = Thm.declaration_attribute (fn thm => Context.mapping (f thm) I);
    fun add_simple_attribute (name, f) =
      add_attribute (name, Scan.succeed (mk_attribute f));
    fun add_del_attribute (name, (add, del)) =
      add_attribute (name, Args.del |-- Scan.succeed (mk_attribute del)
        || Scan.succeed (mk_attribute add))
  in
    add_del_attribute ("func", (add_func true, del_func))
    #> add_del_attribute ("inline", (add_inline, del_inline))
    #> add_del_attribute ("post", (add_post, del_post))
  end);


(** post- and preprocessing **)

local

fun gen_apply_inline_proc prep post thy f x =
  let
    val cts = prep x;
    val rews = map CodeUnit.assert_rew (f thy cts);
  in post rews x end;

val apply_inline_proc = gen_apply_inline_proc (maps
  ((fn [args, rhs] => rhs :: (snd o Drule.strip_comb) args) o snd o Drule.strip_comb o Thm.cprop_of))
  (fn rews => map (CodeUnit.rewrite_func rews));
val apply_inline_proc_cterm = gen_apply_inline_proc single
  (MetaSimplifier.rewrite false);

fun apply_preproc thy f [] = []
  | apply_preproc thy f (thms as (thm :: _)) =
      let
        val (const, _) = CodeUnit.head_func thm;
        val thms' = f thy thms;
      in certify_const thy const thms' end;

fun rhs_conv conv thm =
  let
    val thm' = (conv o Thm.rhs_of) thm;
  in Thm.transitive thm thm' end

in

fun preprocess thy thms =
  thms
  |> fold (fn (_, (_, f)) => apply_preproc thy f) ((#preprocs o the_thmproc o get_exec) thy)
  |> map (CodeUnit.rewrite_func ((#inlines o the_thmproc o get_exec) thy))
  |> fold (fn (_, (_, f)) => apply_inline_proc thy f) ((#inline_procs o the_thmproc o get_exec) thy)
(*FIXME - must check: rewrite rule, defining equation, proper constant |> map (snd o check_func false thy) *)
  |> common_typ_funcs;

fun preprocess_conv ct =
  let
    val thy = Thm.theory_of_cterm ct;
  in
    ct
    |> MetaSimplifier.rewrite false ((#inlines o the_thmproc o get_exec) thy)
    |> fold (fn (_, (_, f)) => rhs_conv (apply_inline_proc_cterm thy f))
        ((#inline_procs o the_thmproc o get_exec) thy)
  end;

fun postprocess_conv ct =
  let
    val thy = Thm.theory_of_cterm ct;
  in
    ct
    |> MetaSimplifier.rewrite false ((#posts o the_thmproc o get_exec) thy)
  end;

end; (*local*)

fun get_datatype thy tyco =
  case Symtab.lookup ((the_dtyps o get_exec) thy) tyco
   of SOME spec => spec
    | NONE => Sign.arity_number thy tyco
        |> Name.invents Name.context "'a"
        |> map (rpair [])
        |> rpair [];

fun get_datatype_of_constr thy const =
  case CodeUnit.co_of_const' thy const
   of SOME (tyco, (_, co)) => if member eq_co
        (Symtab.lookup (((the_dtyps o get_exec) thy)) tyco
          |> Option.map snd
          |> the_default []) co then SOME tyco else NONE
    | NONE => NONE;

fun get_constr_typ thy const =
  case get_datatype_of_constr thy const
   of SOME tyco => let
        val (vs, cos) = get_datatype thy tyco;
        val (_, (_, (co, tys))) = CodeUnit.co_of_const thy const
      in (tys ---> Type (tyco, map TFree vs))
        |> map_atyps (fn TFree (v, _) => TFree (v, AList.lookup (op =) vs v |> the))
        |> Logic.varifyT
        |> SOME end
    | NONE => NONE;

fun default_typ_proto thy (const as (c, SOME tyco)) = classop_weakest_typ thy
      ((the o AxClass.class_of_param thy) c) (c, tyco) |> SOME
  | default_typ_proto thy (const as (c, NONE)) = case AxClass.class_of_param thy c
       of SOME class => SOME (Term.map_type_tvar
            (K (TVar (("'a", 0), [class]))) (Sign.the_const_type thy c))
        | NONE => get_constr_typ thy const;

local

fun get_funcs thy const =
  Consttab.lookup ((the_funcs o get_exec) thy) const
  |> Option.map (Susp.force o fst)
  |> these
  |> map (Thm.transfer thy);

in

fun these_funcs thy const =
  let
    fun drop_refl thy = filter_out (is_equal o Term.fast_term_ord o Logic.dest_equals
      o ObjectLogic.drop_judgment thy o Thm.plain_prop_of);
  in
    get_funcs thy const
    |> preprocess thy
    |> drop_refl thy
  end;

fun default_typ thy (const as (c, _)) = case default_typ_proto thy const
 of SOME ty => ty
  | NONE => (case get_funcs thy const
     of thm :: _ => snd (CodeUnit.head_func thm)
      | [] => Sign.the_const_type thy c);

end; (*local*)

end; (*struct*)


(** type-safe interfaces for data depedent on executable content **)

functor CodeDataFun(Data: CODE_DATA_ARGS): CODE_DATA =
struct

type T = Data.T;
exception Data of T;
fun dest (Data x) = x

val kind = Code.declare_data (Data Data.empty)
  (fn pp => fn (Data x1, Data x2) => Data (Data.merge pp (x1, x2)))
  (fn thy_opt => fn cs => fn Data x => Data (Data.purge thy_opt cs x));

val data_op = (kind, Data, dest);

val get = Code.get_data data_op;
val change = Code.change_data data_op;
fun change_yield thy = Code.change_yield_data data_op thy;

end;

structure Code : CODE =
struct

open Code;

end;
