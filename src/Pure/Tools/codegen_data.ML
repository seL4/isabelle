(*  Title:      Pure/Tools/codegen_data.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Abstract executable content of theory. Management of data dependent on
executabl content.
*)

signature CODEGEN_DATA =
sig
  val lazy: (unit -> thm list) -> thm list Susp.T
  val eval_always: bool ref

  val add_func: thm -> theory -> theory
  val add_func_legacy: thm -> theory -> theory
  val del_func: thm -> theory -> theory
  val add_funcl: CodegenConsts.const * thm list Susp.T -> theory -> theory
  val add_datatype: string * (((string * sort) list * (string * typ list) list) * thm list Susp.T)
    -> theory -> theory
  val del_datatype: string -> theory -> theory
  val add_inline: thm -> theory -> theory
  val del_inline: thm -> theory -> theory
  val add_inline_proc: (theory -> cterm list -> thm list) -> theory -> theory
  val add_preproc: (theory -> thm list -> thm list) -> theory -> theory
  val these_funcs: theory -> CodegenConsts.const -> thm list
  val get_datatype: theory -> string
    -> ((string * sort) list * (string * typ list) list) option
  val get_datatype_of_constr: theory -> CodegenConsts.const -> string option

  val print_thms: theory -> unit

  val typ_func: theory -> thm -> typ
  val typ_funcs: theory -> CodegenConsts.const * thm list -> typ
  val rewrite_func: thm list -> thm -> thm
  val preprocess_cterm: theory -> cterm -> thm

  val trace: bool ref
end;

signature PRIVATE_CODEGEN_DATA =
sig
  include CODEGEN_DATA
  type data
  structure CodeData: THEORY_DATA
  val declare: string -> Object.T -> (Pretty.pp -> Object.T * Object.T -> Object.T)
    -> (theory option -> CodegenConsts.const list option -> Object.T -> Object.T) -> serial
  val init: serial -> theory -> theory
  val get: serial -> (Object.T -> 'a) -> data -> 'a
  val put: serial -> ('a -> Object.T) -> 'a -> data -> data
end;

structure CodegenData : PRIVATE_CODEGEN_DATA =
struct

(** diagnostics **)

val trace = ref false;
fun tracing f x = (if !trace then Output.tracing (f x) else (); x);



(** lazy theorems, certificate theorems **)

val eval_always = ref false;

fun lazy f = if !eval_always
  then Susp.value (f ())
  else Susp.delay f;

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
          val thy_ref = Theory.self_ref thy;
        in lazy (fn () => (f (Theory.deref thy_ref) o Susp.force) r) end;

fun merge' _ ([], []) = (false, [])
  | merge' _ ([], ys) = (true, ys)
  | merge' eq (xs, ys) = fold_rev
      (fn y => fn (t, xs) => (t orelse not (member eq xs y), insert eq y xs)) ys (false, xs);

fun merge_alist eq_key eq (xys as (xs, ys)) =
  if eq_list (eq_pair eq_key eq) (xs, ys)
  then (false, xs)
  else (true, AList.merge eq_key eq xys);

val merge_thms = merge' eq_thm;

fun merge_lthms (r1, r2) =
  if Susp.same (r1, r2)
    then (false, r1)
  else case Susp.peek r1
   of SOME [] => (true, r2)
    | _ => case Susp.peek r2
       of SOME [] => (true, r1)
        | _ => (apsnd (lazy o K)) (merge_thms (Susp.force r1, Susp.force r2));



(** code theorems **)

(* making rewrite theorems *)

fun bad_thm msg thm =
  error (msg ^ ": " ^ string_of_thm thm);

fun check_rew thy thm =
  let
    val (lhs, rhs) = (Logic.dest_equals o Thm.prop_of) thm;
    fun vars_of t = fold_aterms
     (fn Var (v, _) => insert (op =) v
       | Free _ => bad_thm "Illegal free variable in rewrite theorem" thm
       | _ => I) t [];
    fun tvars_of t = fold_term_types
     (fn _ => fold_atyps (fn TVar (v, _) => insert (op =) v
                          | TFree _ => bad_thm "Illegal free type variable in rewrite theorem" thm)) t [];
    val lhs_vs = vars_of lhs;
    val rhs_vs = vars_of rhs;
    val lhs_tvs = tvars_of lhs;
    val rhs_tvs = tvars_of lhs;
    val _ = if null (subtract (op =) lhs_vs rhs_vs)
      then ()
      else bad_thm "Free variables on right hand side of rewrite theorems" thm
    val _ = if null (subtract (op =) lhs_tvs rhs_tvs)
      then ()
      else bad_thm "Free type variables on right hand side of rewrite theorems" thm
  in thm end;

fun mk_rew thy thm =
  let
    val thms = (#mk o #mk_rews o snd o MetaSimplifier.rep_ss o Simplifier.simpset_of) thy thm;
  in
    map (check_rew thy) thms
  end;


(* making function theorems *)

fun typ_func thy = snd o dest_Const o fst o strip_comb
  o fst o Logic.dest_equals o ObjectLogic.drop_judgment thy o Drule.plain_prop_of;

val strict_functyp = ref true;

fun dest_func thy = apfst dest_Const o strip_comb
  o fst o Logic.dest_equals o ObjectLogic.drop_judgment thy o Drule.plain_prop_of
  o Drule.fconv_rule Drule.beta_eta_conversion;

fun mk_head thy thm =
  ((CodegenConsts.norm_of_typ thy o fst o dest_func thy) thm, thm);

fun check_func thy thm = case try (dest_func thy) thm
 of SOME (c_ty as (c, ty), args) =>
      let
        val _ =
          if has_duplicates (op =)
            ((fold o fold_aterms) (fn Var (v, _) => cons v
              | _ => I
            ) args [])
          then bad_thm "Repeated variables on left hand side of function equation" thm
          else ()
        fun no_abs (Abs _) = bad_thm "Abstraction on left hand side of function equation" thm 
          | no_abs (t1 $ t2) = (no_abs t1; no_abs t2)
          | no_abs _ = ();
        val _ = map no_abs args;
        val is_classop = (is_some o AxClass.class_of_param thy) c;
        val const = CodegenConsts.norm_of_typ thy c_ty;
        val ty_decl = CodegenConsts.disc_typ_of_const thy
          (snd o CodegenConsts.typ_of_inst thy) const;
        val string_of_typ = setmp show_sorts true (Sign.string_of_typ thy);
      in if Sign.typ_equiv thy (ty_decl, ty)
        then SOME (const, thm)
        else (if is_classop
            then if !strict_functyp
              then error
              else warning #> K NONE
          else if Sign.typ_equiv thy (Type.strip_sorts ty_decl, Type.strip_sorts ty)
            then warning #> (K o SOME) (const, thm)
          else if !strict_functyp
            then error
          else warning #> K NONE)
          ("Type\n" ^ string_of_typ ty
           ^ "\nof function theorem\n"
           ^ string_of_thm thm
           ^ "\nis strictly less general than declared function type\n"
           ^ string_of_typ ty_decl)
      end
  | NONE => bad_thm "Not a function equation" thm;

fun check_typ_classop thy thm =
  let
    val (c_ty as (c, ty), _) = dest_func thy thm;  
  in case AxClass.class_of_param thy c
   of SOME class => let
        val const = CodegenConsts.norm_of_typ thy c_ty;
        val ty_decl = CodegenConsts.disc_typ_of_const thy
            (snd o CodegenConsts.typ_of_inst thy) const;
        val string_of_typ = setmp show_sorts true (Sign.string_of_typ thy);
      in if Sign.typ_equiv thy (ty_decl, ty)
        then thm
        else error
          ("Type\n" ^ string_of_typ ty
           ^ "\nof function theorem\n"
           ^ string_of_thm thm
           ^ "\nis strictly less general than declared function type\n"
           ^ string_of_typ ty_decl)
      end
    | NONE => thm
  end;

fun mk_func thy raw_thm =
  mk_rew thy raw_thm
  |> map_filter (check_func thy);

fun get_prim_def_funcs thy c =
  let
    fun constrain thm0 thm = case AxClass.class_of_param thy (fst c)
     of SOME _ =>
          let
            val ty_decl = CodegenConsts.disc_typ_of_classop thy c;
            val max = maxidx_of_typ ty_decl + 1;
            val thm = Thm.incr_indexes max thm;
            val ty = typ_func thy thm;
            val (env, _) = Sign.typ_unify thy (ty_decl, ty) (Vartab.empty, max);
            val instT = Vartab.fold (fn (x_i, (sort, ty)) =>
              cons (Thm.ctyp_of thy (TVar (x_i, sort)), Thm.ctyp_of thy ty)) env [];
          in Thm.instantiate (instT, []) thm end
      | NONE => thm
  in case CodegenConsts.find_def thy c
   of SOME ((_, thm), _) =>
        thm
        |> Thm.transfer thy
        |> try (map snd o mk_func thy)
        |> these
        |> map (constrain thm)
    | NONE => []
  end;


(* pairs of (selected, deleted) function theorems *)

type sdthms = thm list Susp.T * thm list;

fun add_drop_redundant thm thms =
  let
    val thy = Context.check_thy (Thm.theory_of_thm thm);
    val args_of = snd o strip_comb o fst o Logic.dest_equals o Drule.plain_prop_of;
    val args = args_of thm;
    fun matches [] _ = true
      | matches (Var _ :: xs) [] = matches xs []
      | matches (_ :: _) [] = false
      | matches (x :: xs) (y :: ys) = Pattern.matches thy (x, y) andalso matches xs ys;
    fun drop thm' = if matches args (args_of thm')
      then (warning ("Dropping redundant function theorem\n" ^ string_of_thm thm'); false)
      else true
  in thm :: filter drop thms end;

fun add_thm thm (sels, dels) =
  (Susp.value (add_drop_redundant thm (Susp.force sels)), remove eq_thm thm dels);

fun add_lthms lthms (sels, []) =
      (lazy (fn () => fold add_drop_redundant
          (Susp.force lthms) (Susp.force sels)), [])
  | add_lthms lthms (sels, dels) =
      fold add_thm (Susp.force lthms) (sels, dels);

fun del_thm thm (sels, dels) =
  (Susp.value (remove eq_thm thm (Susp.force sels)), thm :: dels);

fun pretty_sdthms ctxt (sels, _) = pretty_lthms ctxt sels;

fun merge_sdthms ((sels1, dels1), (sels2, dels2)) =
  let
    val (dels_t, dels) = merge_thms (dels1, dels2);
  in if dels_t
    then let
      val (_, sels) = merge_thms (Susp.force sels1, subtract eq_thm dels1 (Susp.force sels2))
      val (_, dels) = merge_thms (dels1, subtract eq_thm (Susp.force sels1) dels2)
    in (true, ((lazy o K) sels, dels)) end
    else let
      val (sels_t, sels) = merge_lthms (sels1, sels2)
    in (sels_t, (sels, dels)) end
  end;


(** data structures **)

structure Consttab = CodegenConsts.Consttab;

datatype preproc = Preproc of {
  inlines: thm list,
  inline_procs: (serial * (theory -> cterm list -> thm list)) list,
  preprocs: (serial * (theory -> thm list -> thm list)) list
};

fun mk_preproc ((inlines, inline_procs), preprocs) =
  Preproc { inlines = inlines, inline_procs = inline_procs, preprocs = preprocs };
fun map_preproc f (Preproc { inlines, inline_procs, preprocs }) =
  mk_preproc (f ((inlines, inline_procs), preprocs));
fun merge_preproc (Preproc { inlines = inlines1, inline_procs = inline_procs1, preprocs = preprocs1 },
  Preproc { inlines = inlines2, inline_procs = inline_procs2, preprocs = preprocs2 }) =
    let
      val (touched1, inlines) = merge_thms (inlines1, inlines2);
      val (touched2, inline_procs) = merge_alist (op =) (K true) (inline_procs1, inline_procs2);
      val (touched3, preprocs) = merge_alist (op =) (K true) (preprocs1, preprocs2);
    in (touched1 orelse touched2 orelse touched3,
      mk_preproc ((inlines, inline_procs), preprocs)) end;

fun join_func_thms (tabs as (tab1, tab2)) =
  let
    val cs1 = Consttab.keys tab1;
    val cs2 = Consttab.keys tab2;
    val cs' = filter (member CodegenConsts.eq_const cs2) cs1;
    val cs'' = subtract (op =) cs' cs1 @ subtract (op =) cs' cs2;
    val cs''' = ref [] : CodegenConsts.const list ref;
    fun merge c x = let val (touched, thms') = merge_sdthms x in
      (if touched then cs''' := cons c (!cs''') else (); thms') end;
  in (cs'' @ !cs''', Consttab.join merge tabs) end;
fun merge_funcs (thms1, thms2) =
    let
      val (consts, thms) = join_func_thms (thms1, thms2);
    in (SOME consts, thms) end;

val eq_string = op = : string * string -> bool;
fun eq_dtyp (((vs1, cs1), _), ((vs2, cs2), _)) = 
  gen_eq_set (eq_pair eq_string (gen_eq_set eq_string)) (vs1, vs2)
    andalso gen_eq_set (eq_pair eq_string (eq_list (is_equal o Term.typ_ord))) (cs1, cs2);
fun merge_dtyps (tabs as (tab1, tab2)) =
  let
    val tycos1 = Symtab.keys tab1;
    val tycos2 = Symtab.keys tab2;
    val tycos' = filter (member eq_string tycos2) tycos1;
    val touched = not (gen_eq_set (op =) (tycos1, tycos2) andalso
      gen_eq_set (eq_pair (op =) (eq_dtyp))
      (AList.make (the o Symtab.lookup tab1) tycos',
       AList.make (the o Symtab.lookup tab2) tycos'));
  in (touched, Symtab.merge (K true) tabs) end;

datatype spec = Spec of {
  funcs: sdthms Consttab.table,
  dconstrs: string Consttab.table,
  dtyps: (((string * sort) list * (string * typ list) list) * thm list Susp.T) Symtab.table
};

fun mk_spec ((funcs, dconstrs), dtyps) =
  Spec { funcs = funcs, dconstrs = dconstrs, dtyps = dtyps };
fun map_spec f (Spec { funcs = funcs, dconstrs = dconstrs, dtyps = dtyps }) =
  mk_spec (f ((funcs, dconstrs), dtyps));
fun merge_spec (Spec { funcs = funcs1, dconstrs = dconstrs1, dtyps = dtyps1 },
  Spec { funcs = funcs2, dconstrs = dconstrs2, dtyps = dtyps2 }) =
  let
    val (touched_cs, funcs) = merge_funcs (funcs1, funcs2);
    val dconstrs = Consttab.merge (K true) (dconstrs1, dconstrs2);
    val (touched', dtyps) = merge_dtyps (dtyps1, dtyps2);
    val touched = if touched' then NONE else touched_cs;
  in (touched, mk_spec ((funcs, dconstrs), dtyps)) end;

datatype exec = Exec of {
  preproc: preproc,
  spec: spec
};

fun mk_exec (preproc, spec) =
  Exec { preproc = preproc, spec = spec };
fun map_exec f (Exec { preproc = preproc, spec = spec }) =
  mk_exec (f (preproc, spec));
fun merge_exec (Exec { preproc = preproc1, spec = spec1 },
  Exec { preproc = preproc2, spec = spec2 }) =
  let
    val (touched', preproc) = merge_preproc (preproc1, preproc2);
    val (touched_cs, spec) = merge_spec (spec1, spec2);
    val touched = if touched' then NONE else touched_cs;
  in (touched, mk_exec (preproc, spec)) end;
val empty_exec = mk_exec (mk_preproc (([], []), []),
  mk_spec ((Consttab.empty, Consttab.empty), Symtab.empty));

fun the_preproc (Exec { preproc = Preproc x, ...}) = x;
fun the_spec (Exec { spec = Spec x, ...}) = x;
val the_funcs = #funcs o the_spec;
val the_dcontrs = #dconstrs o the_spec;
val the_dtyps = #dtyps o the_spec;
val map_preproc = map_exec o apfst o map_preproc;
val map_funcs = map_exec o apsnd o map_spec o apfst o apfst;
val map_dconstrs = map_exec o apsnd o map_spec o apfst o apsnd;
val map_dtyps = map_exec o apsnd o map_spec o apsnd;


(** code data structures **)

(*private copy avoids potential conflict of table exceptions*)
structure Datatab = TableFun(type key = int val ord = int_ord);


(* data slots *)

local

type kind = {
  name: string,
  empty: Object.T,
  merge: Pretty.pp -> Object.T * Object.T -> Object.T,
  purge: theory option -> CodegenConsts.const list option -> Object.T -> Object.T
};

val kinds = ref (Datatab.empty: kind Datatab.table);

fun invoke meth_name meth_fn k =
  (case Datatab.lookup (! kinds) k of
    SOME kind => meth_fn kind |> transform_failure (fn exn =>
      EXCEPTION (exn, "Code data method " ^ #name kind ^ "." ^ meth_name ^ " failed"))
  | NONE => sys_error ("Invalid code data identifier " ^ string_of_int k));


in

fun invoke_name k   = invoke "name" (K o #name) k ();
fun invoke_empty k  = invoke "empty" (K o #empty) k ();
fun invoke_merge pp = invoke "merge" (fn kind => #merge kind pp);
fun invoke_purge thy_opt cs = invoke "purge" (fn kind => #purge kind thy_opt cs);

fun declare name empty merge purge =
  let
    val k = serial ();
    val kind = {name = name, empty = empty, merge = merge, purge = purge};
    val _ =
      if Datatab.exists (equal name o #name o #2) (! kinds) then
        warning ("Duplicate declaration of code data " ^ quote name)
      else ();
    val _ = change kinds (Datatab.update (k, kind));
  in k end;

end; (*local*)


(* theory store *)

type data = Object.T Datatab.table;

structure CodeData = TheoryDataFun
(struct
  val name = "Pure/codegen_data";
  type T = exec * data ref;
  val empty = (empty_exec, ref Datatab.empty : data ref);
  fun copy (exec, data) = (exec, ref (! data));
  val extend = copy;
  fun merge pp ((exec1, data1), (exec2, data2)) =
    let
      val (touched, exec) = merge_exec (exec1, exec2);
      val data1' = Datatab.map' (invoke_purge NONE touched) (! data1);
      val data2' = Datatab.map' (invoke_purge NONE touched) (! data2);
      val data = Datatab.join (invoke_merge pp) (data1', data2');
    in (exec, ref data) end;
  fun print thy (exec, _) =
    let
      val ctxt = ProofContext.init thy;
      fun pretty_func (s, lthms) =
        (Pretty.block o Pretty.fbreaks) (
          Pretty.str s :: pretty_sdthms ctxt lthms
        );
      fun pretty_dtyp (s, cos) =
        (Pretty.block o Pretty.breaks) (
          Pretty.str s
          :: Pretty.str "="
          :: Pretty.separate "|" (map (fn (c, []) => Pretty.str c
               | (c, tys) =>
                   Pretty.block
                      (Pretty.str c :: Pretty.brk 1 :: Pretty.str "of" :: Pretty.brk 1
                      :: Pretty.breaks (map (Pretty.quote o Sign.pretty_typ thy) tys))) cos)
        )
      val inlines = (#inlines o the_preproc) exec;
      val funs = the_funcs exec
        |> Consttab.dest
        |> (map o apfst) (CodegenConsts.string_of_const thy)
        |> sort (string_ord o pairself fst);
      val dtyps = the_dtyps exec
        |> Symtab.dest
        |> map (fn (dtco, ((vs, cos), _)) => (Sign.string_of_typ thy (Type (dtco, map TFree vs)), cos))
        |> sort (string_ord o pairself fst)
    in
      (Pretty.writeln o Pretty.block o Pretty.fbreaks) ([
        Pretty.str "code theorems:",
        Pretty.str "function theorems:" ] @
          map pretty_func funs @ [
        Pretty.block (
          Pretty.str "inlined theorems:"
          :: Pretty.fbrk
          :: (Pretty.fbreaks o map (ProofContext.pretty_thm ctxt)) inlines
        ),
        Pretty.block (
          Pretty.str "datatypes:"
          :: Pretty.fbrk
          :: (Pretty.fbreaks o map pretty_dtyp) dtyps
        )]
      )
    end;
end);

fun print_thms thy = CodeData.print thy;

fun init k = CodeData.map
  (fn (exec, data) => (exec, ref (Datatab.update (k, invoke_empty k) (! data))));

fun get k dest data =
  (case Datatab.lookup data k of
    SOME x => (dest x handle Match =>
      error ("Failed to access code data " ^ quote (invoke_name k)))
  | NONE => error ("Uninitialized code data " ^ quote (invoke_name k)));

fun put k mk x = Datatab.update (k, mk x);

fun map_exec_purge touched f thy =
  CodeData.map (fn (exec, data) => 
    (f exec, ref (Datatab.map' (invoke_purge (SOME thy) touched) (! data)))) thy;

val get_exec = fst o CodeData.get;

val _ = Context.add_setup CodeData.init;



(** theorem transformation and certification **)

fun rewrite_func rewrites thm =
  let
    val rewrite = MetaSimplifier.rewrite false rewrites;
    val (ct_eq, [ct_lhs, ct_rhs]) = (Drule.strip_comb o Thm.cprop_of) thm;
    val Const ("==", _) = Thm.term_of ct_eq;
    val (ct_f, ct_args) = Drule.strip_comb ct_lhs;
    val rhs' = rewrite ct_rhs;
    val args' = map rewrite ct_args;
    val lhs' = Thm.symmetric (fold (fn th1 => fn th2 => Thm.combination th2 th1)
      args' (Thm.reflexive ct_f));
  in
    Thm.transitive (Thm.transitive lhs' thm) rhs'
  end handle Bind => raise ERROR "rewrite_func"

fun common_typ_funcs thy [] = []
  | common_typ_funcs thy [thm] = [thm]
  | common_typ_funcs thy thms =
      let
        fun incr_thm thm max =
          let
            val thm' = incr_indexes max thm;
            val max' = Thm.maxidx_of thm' + 1;
          in (thm', max') end;
        val (thms', maxidx) = fold_map incr_thm thms 0;
        val (ty1::tys) = map (typ_func thy) thms';
        fun unify ty env = Sign.typ_unify thy (ty1, ty) env
          handle Type.TUNIFY =>
            error ("Type unificaton failed, while unifying function equations\n"
            ^ (cat_lines o map Display.string_of_thm) thms
            ^ "\nwith types\n"
            ^ (cat_lines o map (Sign.string_of_typ thy)) (ty1 :: tys));
        val (env, _) = fold unify tys (Vartab.empty, maxidx)
        val instT = Vartab.fold (fn (x_i, (sort, ty)) =>
          cons (Thm.ctyp_of thy (TVar (x_i, sort)), Thm.ctyp_of thy ty)) env [];
      in map (Thm.instantiate (instT, [])) thms' end;

fun certify_const thy c c_thms =
  let
    fun cert (c', thm) = if CodegenConsts.eq_const (c, c')
      then thm else bad_thm ("Wrong head of function equation,\nexpected constant "
        ^ CodegenConsts.string_of_const thy c) thm
  in map cert c_thms end;

fun mk_cos tyco vs cos =
  let
    val dty = Type (tyco, map TFree vs);
    fun mk_co (co, tys) = (Const (co, (tys ---> dty)), map I tys);
  in map mk_co cos end;

fun mk_co_args (co, tys) ctxt =
  let
    val names = Name.invents ctxt "a" (length tys);
    val ctxt' = fold Name.declare names ctxt;
    val vs = map2 (fn v => fn ty => Free (fst (v, 0), I ty)) names tys;
  in (vs, ctxt') end;

fun check_freeness thy cos thms =
  let
    val props = AList.make Drule.plain_prop_of thms;
    fun sym_product [] = []
      | sym_product (x::xs) = map (pair x) xs @ sym_product xs;
    val quodlibet =
      let
        val judg = ObjectLogic.fixed_judgment (the_context ()) "x";
        val [free] = fold_aterms (fn v as Free _ => cons v | _ => I) judg [];
        val judg' = Term.subst_free [(free, Bound 0)] judg;
        val prop = Type ("prop", []);
        val prop' = fastype_of judg';
      in
        Const ("all", (prop' --> prop) --> prop) $ Abs ("P", prop', judg')
      end;
    fun check_inj (co, []) =
          NONE
      | check_inj (co, tys) =
          let
            val ((xs, ys), _) = Name.context
              |> mk_co_args (co, tys)
              ||>> mk_co_args (co, tys);
            val prem = Logic.mk_equals
              (list_comb (co, xs), list_comb (co, ys));
            val concl = Logic.mk_conjunction_list
              (map2 (curry Logic.mk_equals) xs ys);
            val t = Logic.mk_implies (prem, concl);
          in case find_first (curry Term.could_unify t o snd) props
           of SOME (thm, _) => SOME thm
            | NONE => error ("Could not prove injectiveness statement\n"
               ^ Sign.string_of_term thy t
               ^ "\nfor constructor "
               ^ CodegenConsts.string_of_const_typ thy (dest_Const co)
               ^ "\nwith theorems\n" ^ cat_lines (map string_of_thm thms))
          end;
    fun check_dist ((co1, tys1), (co2, tys2)) =
          let
            val ((xs1, xs2), _) = Name.context
              |> mk_co_args (co1, tys1)
              ||>> mk_co_args (co2, tys2);
            val prem = Logic.mk_equals
              (list_comb (co1, xs1), list_comb (co2, xs2));
            val t = Logic.mk_implies (prem, quodlibet);
          in case find_first (curry Term.could_unify t o snd) props
           of SOME (thm, _) => thm
            | NONE => error ("Could not prove distinctness statement\n"
               ^ Sign.string_of_term thy t
               ^ "\nfor constructors "
               ^ CodegenConsts.string_of_const_typ thy (dest_Const co1)
               ^ " and "
               ^ CodegenConsts.string_of_const_typ thy (dest_Const co2)
               ^ "\nwith theorems\n" ^ cat_lines (map string_of_thm thms))
          end;
  in (map_filter check_inj cos, map check_dist (sym_product cos)) end;

fun certify_datatype thy dtco cs thms =
  (op @) (check_freeness thy cs thms);



(** interfaces **)

fun add_func thm thy =
  let
    val thms = mk_func thy thm;
    val cs = map fst thms;
  in
    map_exec_purge (SOME cs) (map_funcs 
     (fold (fn (c, thm) => Consttab.map_default
       (c, (Susp.value [], [])) (add_thm thm)) thms)) thy
  end;

fun add_func_legacy thm = setmp strict_functyp false (add_func thm);

fun del_func thm thy =
  let
    val thms = mk_func thy thm;
    val cs = map fst thms;
  in
    map_exec_purge (SOME cs) (map_funcs
     (fold (fn (c, thm) => Consttab.map_entry c
       (del_thm thm)) thms)) thy
  end;

fun add_funcl (c, lthms) thy =
  let
    val c' = CodegenConsts.norm thy c;
    val lthms' = certificate thy (fn thy => certify_const thy c' o maps (mk_func thy)) lthms;
  in
    map_exec_purge (SOME [c]) (map_funcs (Consttab.map_default (c', (Susp.value [], []))
      (add_lthms lthms'))) thy
  end;

fun add_datatype (tyco, (vs_cos as (vs, cos), lthms)) thy =
  let
    val cs = mk_cos tyco vs cos;
    val consts = map (CodegenConsts.norm_of_typ thy o dest_Const o fst) cs;
    val add =
      map_dtyps (Symtab.update_new (tyco,
        (vs_cos, certificate thy (fn thy => certify_datatype thy tyco cs) lthms)))
      #> map_dconstrs (fold (fn c => Consttab.update (c, tyco)) consts)
  in map_exec_purge (SOME consts) add thy end;

fun del_datatype tyco thy =
  let
    val SOME ((vs, cos), _) = Symtab.lookup ((the_dtyps o get_exec) thy) tyco;
    val cs = mk_cos tyco vs cos;
    val consts = map (CodegenConsts.norm_of_typ thy o dest_Const o fst) cs;
    val del =
      map_dtyps (Symtab.delete tyco)
      #> map_dconstrs (fold Consttab.delete consts)
  in map_exec_purge (SOME consts) del thy end;

fun add_inline thm thy =
  (map_exec_purge NONE o map_preproc o apfst o apfst) (fold (insert eq_thm) (mk_rew thy thm)) thy;

fun del_inline thm thy =
  (map_exec_purge NONE o map_preproc o apfst o apfst) (fold (remove eq_thm) (mk_rew thy thm)) thy ;

fun add_inline_proc f =
  (map_exec_purge NONE o map_preproc o apfst o apsnd) (cons (serial (), f));

fun add_preproc f =
  (map_exec_purge NONE o map_preproc o apsnd) (cons (serial (), f));

local

fun gen_apply_inline_proc prep post thy f x =
  let
    val cts = prep x;
    val rews = map (check_rew thy) (f thy cts);
  in post rews x end;

val apply_inline_proc = gen_apply_inline_proc (maps
  ((fn [args, rhs] => rhs :: (snd o Drule.strip_comb) args) o snd o Drule.strip_comb o Thm.cprop_of))
  (fn rews => map (rewrite_func rews));
val apply_inline_proc_cterm = gen_apply_inline_proc single
  (MetaSimplifier.rewrite false);

fun apply_preproc thy f [] = []
  | apply_preproc thy f (thms as (thm :: _)) =
      let
        val thms' = f thy thms;
        val c = (CodegenConsts.norm_of_typ thy o fst o dest_func thy) thm;
      in (certify_const thy c o map (mk_head thy)) thms' end;

fun cmp_thms thy =
  make_ord (fn (thm1, thm2) => not (Sign.typ_instance thy (typ_func thy thm1, typ_func thy thm2)));

fun rhs_conv conv thm =
  let
    val thm' = (conv o snd o Drule.dest_equals o Thm.cprop_of) thm;
  in Thm.transitive thm thm' end

in

fun preprocess thy thms =
  thms
  |> fold (fn (_, f) => apply_preproc thy f) ((#preprocs o the_preproc o get_exec) thy)
  |> map (rewrite_func ((#inlines o the_preproc o get_exec) thy))
  |> fold (fn (_, f) => apply_inline_proc thy f) ((#inline_procs o the_preproc o get_exec) thy)
(*FIXME - must check: rewrite rule, function equation, proper constant |> map (snd o check_func false thy) *)
  |> sort (cmp_thms thy)
  |> common_typ_funcs thy;

fun preprocess_cterm thy ct =
  ct
  |> Thm.reflexive
  |> fold (rhs_conv o MetaSimplifier.rewrite false o single)
    ((#inlines o the_preproc o get_exec) thy)
  |> fold (fn (_, f) => rhs_conv (apply_inline_proc_cterm thy f))
    ((#inline_procs o the_preproc o get_exec) thy)

end; (*local*)

fun these_funcs thy c =
  let
    val funcs_1 =
      Consttab.lookup ((the_funcs o get_exec) thy) c
      |> Option.map (Susp.force o fst)
      |> these
      |> map (Thm.transfer thy);
    val funcs_2 = case funcs_1
     of [] => get_prim_def_funcs thy c
      | xs => xs;
    fun drop_refl thy = filter_out (is_equal o Term.fast_term_ord o Logic.dest_equals
      o ObjectLogic.drop_judgment thy o Drule.plain_prop_of);
  in
    funcs_2
    |> preprocess thy
    |> drop_refl thy
  end;

fun get_datatype thy tyco =
  Symtab.lookup ((the_dtyps o get_exec) thy) tyco
  |> Option.map (fn (spec, thms) => (Susp.force thms; spec));

fun get_datatype_of_constr thy c =
  Consttab.lookup ((the_dcontrs o get_exec) thy) c
  |> (Option.map o tap) (fn dtco => get_datatype thy dtco);

fun typ_funcs thy (c as (name, _), []) = (case AxClass.class_of_param thy name
     of SOME class => CodegenConsts.disc_typ_of_classop thy c
      | NONE => (case Option.map (Susp.force o fst) (Consttab.lookup ((the_funcs o get_exec) thy) c)
         of SOME [eq] => typ_func thy eq
          | _ => Sign.the_const_type thy name))
  | typ_funcs thy (_, eq :: _) = typ_func thy eq;


(** code attributes **)

local
  fun add_simple_attribute (name, f) =
    (Codegen.add_attribute name o (Scan.succeed o Thm.declaration_attribute))
      (fn th => Context.mapping (f th) I);
in
  val _ = map (Context.add_setup o add_simple_attribute) [
    ("func", add_func),
    ("nofunc", del_func),
    ("unfold", (fn thm => Codegen.add_unfold thm #> add_inline thm)),
    ("inline", add_inline),
    ("noinline", del_inline)
  ]
end; (*local*)

end; (*struct*)



(** type-safe interfaces for data depedent on executable content **)

signature CODE_DATA_ARGS =
sig
  val name: string
  type T
  val empty: T
  val merge: Pretty.pp -> T * T -> T
  val purge: theory option -> CodegenConsts.const list option -> T -> T
end;

signature CODE_DATA =
sig
  type T
  val init: theory -> theory
  val get: theory -> T
  val change: theory -> (T -> T) -> T
  val change_yield: theory -> (T -> 'a * T) -> 'a * T
end;

functor CodeDataFun(Data: CODE_DATA_ARGS): CODE_DATA =
struct

type T = Data.T;
exception Data of T;
fun dest (Data x) = x

val kind = CodegenData.declare Data.name (Data Data.empty)
  (fn pp => fn (Data x1, Data x2) => Data (Data.merge pp (x1, x2)))
  (fn thy_opt => fn cs => fn Data x => Data (Data.purge thy_opt cs x));

val init = CodegenData.init kind;
fun get thy = CodegenData.get kind dest ((! o snd o CodegenData.CodeData.get) thy);
fun change thy f =
  let
    val data_ref = (snd o CodegenData.CodeData.get) thy;
    val x = (f o CodegenData.get kind dest o !) data_ref;
    val data = CodegenData.put kind Data x (! data_ref);
  in (data_ref := data; x) end;
fun change_yield thy f =
  let
    val data_ref = (snd o CodegenData.CodeData.get) thy;
    val (y, x) = (f o CodegenData.get kind dest o !) data_ref;
    val data = CodegenData.put kind Data x (! data_ref);
  in (data_ref := data; (y, x)) end;

end;

structure CodegenData : CODEGEN_DATA =
struct

open CodegenData;

end;
