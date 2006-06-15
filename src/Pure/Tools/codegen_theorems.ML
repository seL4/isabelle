(*  Title:      Pure/Tools/codegen_theorems.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Theorems used for code generation.
*)

signature CODEGEN_THEOREMS =
sig
  val add_notify: ((string * typ) list option -> theory -> theory) -> theory -> theory;
  val add_preproc: (theory -> thm list -> thm list) -> theory -> theory;
  val add_fun_extr: (theory -> string * typ -> thm list) -> theory -> theory;
  val add_datatype_extr: (theory -> string
    -> (((string * sort) list * (string * typ list) list) * tactic) option)
    -> theory -> theory;
  val add_fun: thm -> theory -> theory;
  val del_fun: thm -> theory -> theory;
  val add_unfold: thm -> theory -> theory;
  val del_unfold: thm -> theory -> theory;
  val purge_defs: string * typ -> theory -> theory;
  val notify_dirty: theory -> theory;

  val proper_name: string -> string;
  val common_typ: theory -> (thm -> typ) -> thm list -> thm list;
  val preprocess: theory -> thm list -> (typ * thm list) option;

  val get_funs: theory -> string * typ -> (typ * thm list) option;
  val get_datatypes: theory -> string
    -> (((string * sort) list * (string * typ list) list) * thm list) option;

  (*
  type thmtab;
  val get_thmtab: (string * typ) list -> theory -> thmtab * theory;
  val get_cons: thmtab -> string -> string option;
  val get_dtyp: thmtab -> string -> (string * sort) list * (string * typ list) list;
  val get_thms: thmtab -> string * typ -> typ * thm list;
  *)
  
  val print_thms: theory -> unit;

  val init_obj: (thm * thm) * (thm * thm) -> theory -> theory;
  val debug: bool ref;
  val debug_msg: ('a -> string) -> 'a -> 'a;

end;

structure CodegenTheorems: CODEGEN_THEOREMS =
struct

(** preliminaries **)

(* diagnostics *)

val debug = ref false;
fun debug_msg f x = (if !debug then Output.debug (f x) else (); x);


(* auxiliary *)

fun proper_name s =
  let
    fun replace_invalid c =
      if (Char.isAlphaNum o the o Char.fromString) c orelse c = "'"
        andalso not (NameSpace.separator = c)
      then c
      else "_";
    fun contract "_" (acc as "_" :: _) = acc
      | contract c acc = c :: acc;
    fun contract_underscores s =
      implode (fold_rev contract (explode s) []);
    fun ensure_char s =
      if forall (Char.isDigit o the o Char.fromString) (explode s)
        then prefix "x" s
        else s
  in
    s
    |> translate_string replace_invalid
    |> contract_underscores
    |> ensure_char
  end;


fun getf_first [] _ = NONE
  | getf_first (f::fs) x = case f x
     of NONE => getf_first fs x
      | y as SOME x => y;

fun getf_first_list [] x = []
  | getf_first_list (f::fs) x = case f x
     of [] => getf_first_list fs x
      | xs => xs;


(* object logic setup *)

structure CodegenTheoremsSetup = TheoryDataFun
(struct
  val name = "Pure/CodegenTheoremsSetup";
  type T = ((string * thm) * ((string * string) * (string * string))) option;
  val empty = NONE;
  val copy = I;
  val extend = I;
  fun merge pp = merge_opt (eq_pair (eq_pair (op =) eq_thm)
    (eq_pair (eq_pair (op =) (op =)) (eq_pair (op =) (op =)))) : T * T -> T;
  fun print thy data = ();
end);

val _ = Context.add_setup CodegenTheoremsSetup.init;

fun init_obj ((TrueI, FalseE), (conjI, atomize_eq)) thy =
  case CodegenTheoremsSetup.get thy
   of SOME _ => error "code generator already set up for object logic"
    | NONE => 
        let
          fun strip_implies t = (Logic.strip_imp_prems t, Logic.strip_imp_concl t);
          fun dest_TrueI thm =
            Drule.plain_prop_of thm
            |> ObjectLogic.drop_judgment thy
            |> Term.dest_Const
            |> apsnd (
                  Term.dest_Type
                  #> fst
              );
          fun dest_FalseE thm =
            Drule.plain_prop_of thm
            |> Logic.dest_implies
            |> apsnd (
                 ObjectLogic.drop_judgment thy
                 #> Term.dest_Var
               )
            |> fst
            |> ObjectLogic.drop_judgment thy
            |> Term.dest_Const
            |> fst;
          fun dest_conjI thm =
            Drule.plain_prop_of thm
            |> strip_implies
            |> apfst (map (ObjectLogic.drop_judgment thy #> Term.dest_Var))
            |> apsnd (
                 ObjectLogic.drop_judgment thy
                 #> Term.strip_comb
                 #> apsnd (map Term.dest_Var)
                 #> apfst Term.dest_Const
               )
            |> (fn (v1, ((conj, _), v2)) => if v1 = v2 then conj else error "wrong premise")
          fun dest_atomize_eq thm =
            Drule.plain_prop_of thm
            |> Logic.dest_equals
            |> apfst (
                 ObjectLogic.drop_judgment thy
                 #> Term.strip_comb
                 #> apsnd (map Term.dest_Var)
                 #> apfst Term.dest_Const
               )
            |> apsnd (
                 Logic.dest_equals
                 #> apfst Term.dest_Var
                 #> apsnd Term.dest_Var
               )
            |> (fn (((eq, _), v2), (v1a as (_, TVar (_, sort)), v1b)) =>
                 if [v1a, v1b] = v2 andalso sort = Sign.defaultS thy then eq else error "wrong premise")
        in
          ((dest_TrueI TrueI, [dest_FalseE FalseE, dest_conjI conjI, dest_atomize_eq atomize_eq])
          handle _ => error "bad code generator setup")
          |> (fn ((tr, b), [fl, con, eq]) => CodegenTheoremsSetup.put
               (SOME ((b, atomize_eq), ((tr, fl), (con, eq)))) thy)
        end;

fun get_obj thy =
  case CodegenTheoremsSetup.get thy
   of SOME ((b, atomize), x) => ((Type (b, []), atomize) ,x)
    | NONE => error "no object logic setup for code theorems";

fun mk_true thy =
  let
    val ((b, _), ((tr, fl), (con, eq))) = get_obj thy;
  in Const (tr, b) end;

fun mk_false thy =
  let
    val ((b, _), ((tr, fl), (con, eq))) = get_obj thy;
  in Const (fl, b) end;

fun mk_obj_conj thy (x, y) =
  let
    val ((b, _), ((tr, fl), (con, eq))) = get_obj thy;
  in Const (con, b --> b --> b) $ x $ y end;

fun mk_obj_eq thy (x, y) =
  let
    val ((b, _), ((tr, fl), (con, eq))) = get_obj thy;
  in Const (eq, type_of x --> type_of y --> b) $ x $ y end;

fun is_obj_eq thy c =
  let
    val ((b, _), ((tr, fl), (con, eq))) = get_obj thy;
  in c = eq end;

fun mk_func thy ((x, y), rhs) =
  Logic.mk_equals (
    (mk_obj_eq thy (x, y)),
    rhs
  );


(* theorem purification *)

fun err_thm msg thm =
  error (msg ^ ": " ^ string_of_thm thm);

fun abs_norm thy thm =
  let
    fun expvars t =
      let
        val lhs = (fst o Logic.dest_equals) t;
        val tys = (fst o strip_type o type_of) lhs;
        val used = fold_aterms (fn Var ((v, _), _) => insert (op =) v | _ => I) lhs [];
        val vs = Term.invent_names used "x" (length tys);
      in
        map2 (fn v => fn ty => Var ((v, 0), ty)) vs tys
      end;
    fun expand ct thm =
      Thm.combination thm (Thm.reflexive ct);
    fun beta_norm thm =
      thm
      |> prop_of
      |> Logic.dest_equals
      |> fst
      |> cterm_of thy
      |> Thm.beta_conversion true
      |> Thm.symmetric
      |> (fn thm' => Thm.transitive thm' thm);
  in
    thm
    |> fold (expand o cterm_of thy) ((expvars o prop_of) thm)
    |> beta_norm
  end;

fun canonical_tvars thy thm =
  let
    fun mk_inst (v_i as (v, i), (v', sort)) (s as (maxidx, set, acc)) =
      if v = v' orelse member (op =) set v then s
        else let
          val ty = TVar (v_i, sort)
        in
          (maxidx + 1, v :: set,
            (ctyp_of thy ty, ctyp_of thy (TVar ((v', maxidx), sort))) :: acc)
        end;
    val lower_name = (prefix "'" o implode o map (Char.toString o Char.toLower o the o Char.fromString)
      o explode o proper_name o unprefix "'");
    fun tvars_of thm = (fold_types o fold_atyps)
      (fn TVar (v_i as (v, i), sort) => cons (v_i, (lower_name v, sort))
        | _ => I) (prop_of thm) [];
    val maxidx = Thm.maxidx_of thm + 1;
    val (_, _, inst) = fold mk_inst (tvars_of thm) (maxidx + 1, [], []);
  in Thm.instantiate (inst, []) thm end;

fun canonical_vars thy thm =
  let
    fun mk_inst (v_i as (v, i), (v', ty)) (s as (maxidx, set, acc)) =
      if v = v' orelse member (op =) set v then s
        else let
          val t = if i = ~1 then Free (v, ty) else Var (v_i, ty)
        in 
          (maxidx + 1,  v :: set,
            (cterm_of thy t, cterm_of thy (Var ((v', maxidx), ty))) :: acc)
        end;
    val lower_name = (implode o map (Char.toString o Char.toLower o the o Char.fromString)
      o explode o proper_name);
    fun vars_of thm = fold_aterms
      (fn Var (v_i as (v, i), ty) => cons (v_i, (lower_name v, ty))
        | _ => I) (prop_of thm) [];
    val maxidx = Thm.maxidx_of thm + 1;
    val (_, _, inst) = fold mk_inst (vars_of thm) (maxidx + 1, [], []);
  in Thm.instantiate ([], inst) thm end;

fun drop_redundant thy eqs =
  let
    val matches = curry (Pattern.matches thy o
      pairself (fst o Logic.dest_equals o prop_of))
    fun drop eqs [] = eqs
      | drop eqs (eq::eqs') =
          drop (eq::eqs) (filter_out (matches eq) eqs')
  in drop [] eqs end;

fun make_eq thy = 
  let
    val ((_, atomize), _) = get_obj thy;
  in rewrite_rule [atomize] end;

fun dest_eq thy thm =
  case try (make_eq thy #> Drule.plain_prop_of
   #> ObjectLogic.drop_judgment thy #> Logic.dest_equals) thm
   of SOME eq => (eq, thm)
    | NONE => err_thm "not an equation" thm;

fun dest_fun thy thm =
  let
    fun dest_fun' ((lhs, _), thm) =
      case try (dest_Const o fst o strip_comb) lhs
       of SOME (c, ty) => (c, (ty, thm))
        | NONE => err_thm "not a function equation" thm;
  in
    thm
    |> dest_eq thy
    |> dest_fun'
  end;



(** theory data **)

(* data structures *)

fun merge' eq (xys as (xs, ys)) =
  if eq_list eq (xs, ys) then (false, xs) else (true, merge eq xys);

fun alist_merge' eq_key eq (xys as (xs, ys)) =
  if eq_list (eq_pair eq_key eq) (xs, ys) then (false, xs) else (true, AList.merge eq_key eq xys);

fun list_symtab_join' eq (xyt as (xt, yt)) =
  let
    val xc = Symtab.keys xt;
    val yc = Symtab.keys yt;
    val zc = filter (member (op =) yc) xc;
    val wc = subtract (op =) zc xc @ subtract (op =) zc yc;
    fun same_thms c = if eq_list eq_thm ((the o Symtab.lookup xt) c, (the o Symtab.lookup yt) c)
      then NONE else SOME c;
  in (wc @ map_filter same_thms zc, Symtab.join (K (merge eq)) xyt) end;

datatype notify = Notify of (serial * ((string * typ) list option -> theory -> theory)) list;

val mk_notify = Notify;
fun map_notify f (Notify notify) = mk_notify (f notify);
fun merge_notify pp (Notify notify1, Notify notify2) =
  mk_notify (AList.merge (op =) (K true) (notify1, notify2));

datatype preproc = Preproc of {
  preprocs: (serial * (theory -> thm list -> thm list)) list,
  unfolds: thm list
};

fun mk_preproc (preprocs, unfolds) =
  Preproc { preprocs = preprocs, unfolds = unfolds };
fun map_preproc f (Preproc { preprocs, unfolds }) =
  mk_preproc (f (preprocs, unfolds));
fun merge_preproc _ (Preproc { preprocs = preprocs1, unfolds = unfolds1 },
  Preproc { preprocs = preprocs2, unfolds = unfolds2 }) =
    let
      val (dirty1, preprocs) = alist_merge' (op =) (K true) (preprocs1, preprocs2);
      val (dirty2, unfolds) = merge' eq_thm (unfolds1, unfolds2);
    in (dirty1 orelse dirty2, mk_preproc (preprocs, unfolds)) end;

datatype extrs = Extrs of {
  funs: (serial * (theory -> string * typ -> thm list)) list,
  datatypes: (serial * (theory -> string -> (((string * sort) list * (string * typ list) list) * tactic) option)) list
};

fun mk_extrs (funs, datatypes) =
  Extrs { funs = funs, datatypes = datatypes };
fun map_extrs f (Extrs { funs, datatypes }) =
  mk_extrs (f (funs, datatypes));
fun merge_extrs _ (Extrs { funs = funs1, datatypes = datatypes1 },
  Extrs { funs = funs2, datatypes = datatypes2 }) =
    let
      val (dirty1, funs) = alist_merge' (op =) (K true) (funs1, funs2);
      val (dirty2, datatypes) = alist_merge' (op =) (K true) (datatypes1, datatypes2);
    in (dirty1 orelse dirty2, mk_extrs (funs, datatypes)) end;

datatype funthms = Funthms of {
  dirty: string list,
  funs: thm list Symtab.table
};

fun mk_funthms (dirty, funs) =
  Funthms { dirty = dirty, funs = funs };
fun map_funthms f (Funthms { dirty, funs }) =
  mk_funthms (f (dirty, funs));
fun merge_funthms _ (Funthms { dirty = dirty1, funs = funs1 },
  Funthms { dirty = dirty2, funs = funs2 }) =
    let
      val (dirty3, funs) = list_symtab_join' eq_thm (funs1, funs2);
    in mk_funthms (merge (op =) (merge (op =) (dirty1, dirty2), dirty3), funs) end;

datatype T = T of {
  dirty: bool,
  notify: notify,
  preproc: preproc,
  extrs: extrs,
  funthms: funthms
};

fun mk_T ((dirty, notify), (preproc, (extrs, funthms))) =
  T { dirty = dirty, notify = notify, preproc = preproc, extrs = extrs, funthms = funthms };
fun map_T f (T { dirty, notify, preproc, extrs, funthms }) =
  mk_T (f ((dirty, notify), (preproc, (extrs, funthms))));
fun merge_T pp (T { dirty = dirty1, notify = notify1, preproc = preproc1, extrs = extrs1, funthms = funthms1 },
  T { dirty = dirty2, notify = notify2, preproc = preproc2, extrs = extrs2, funthms = funthms2 }) =
    let
      val (dirty3, preproc) = merge_preproc pp (preproc1, preproc2);
      val (dirty4, extrs) = merge_extrs pp (extrs1, extrs2);
    in
      mk_T ((dirty1 orelse dirty2 orelse dirty3 orelse dirty4, merge_notify pp (notify1, notify2)),
        (preproc, (extrs, merge_funthms pp (funthms1, funthms2))))
    end;


(* setup *)

structure CodegenTheoremsData = TheoryDataFun
(struct
  val name = "Pure/CodegenTheoremsData";
  type T = T;
  val empty = mk_T ((false, mk_notify []), (mk_preproc ([], []),
    (mk_extrs ([], []), mk_funthms ([], Symtab.empty))));
  val copy = I;
  val extend = I;
  val merge = merge_T;
  fun print (thy : theory) (data : T) =
    let
      val pretty_thm = ProofContext.pretty_thm (ProofContext.init thy);
      val funthms = (fn T { funthms, ... } => funthms) data;
      val funs = (Symtab.dest o (fn Funthms { funs, ... } => funs)) funthms;
      val preproc = (fn T { preproc, ... } => preproc) data;
      val unfolds = (fn Preproc { unfolds, ... } => unfolds) preproc;
    in
      (Pretty.writeln o Pretty.block o Pretty.fbreaks) ([
        Pretty.str "code generation theorems:",
        Pretty.str "function theorems:" ] @
        (*Pretty.fbreaks ( *)
          map (fn (c, thms) => 
            (Pretty.block o Pretty.fbreaks) (
              Pretty.str c :: map pretty_thm (rev thms)
            )
          ) funs
        (*) *) @ [
        Pretty.fbrk,
        Pretty.block (
          Pretty.str "unfolding theorems:"
          :: Pretty.fbrk
          :: (Pretty.fbreaks o map pretty_thm) unfolds
      )])
    end;
end);

val _ = Context.add_setup CodegenTheoremsData.init;
val print_thms = CodegenTheoremsData.print;


(* accessors *)

local
  val the_preproc = (fn T { preproc = Preproc preproc, ... } => preproc) o CodegenTheoremsData.get;
  val the_extrs = (fn T { extrs = Extrs extrs, ... } => extrs) o CodegenTheoremsData.get;
  val the_funthms = (fn T { funthms = Funthms funthms, ... } => funthms) o CodegenTheoremsData.get;
in
  val is_dirty = (fn T { dirty = dirty, ... } => dirty) o CodegenTheoremsData.get;
  val the_dirty_consts = (fn { dirty = dirty, ... } => dirty) o the_funthms;
  val the_notify = (fn T { notify = Notify notify, ... } => map snd notify) o CodegenTheoremsData.get;
  val the_preprocs = (fn { preprocs, ... } => map snd preprocs) o the_preproc;
  val the_unfolds = (fn { unfolds, ... } => unfolds) o the_preproc;
  val the_funs_extrs = (fn { funs, ... } => map snd funs) o the_extrs;
  val the_datatypes_extrs = (fn { datatypes, ... } => map snd datatypes) o the_extrs;
  val the_funs = (fn { funs, ... } => funs) o the_funthms;
end (*local*);

val map_data = CodegenTheoremsData.map o map_T;

(* notifiers *)

fun all_typs thy c =
  map (pair c) (Sign.the_const_type thy c :: (map (#lhs) o Theory.definitions_of thy) c);

fun add_notify f =
  map_data (fn ((dirty, notify), x) =>
    ((dirty, notify |> map_notify (cons (serial (), f))), x));

fun get_reset_dirty thy =
  let
    val dirty = is_dirty thy;
    val dirty_const = if dirty then [] else the_dirty_consts thy;
  in
    thy
    |> map_data (fn ((_, notify), (procs, (extrs, funthms))) =>
         ((false, notify), (procs, (extrs, funthms |> map_funthms (fn (_, funs) => ([], funs))))))
    |> pair (dirty, dirty_const)
  end;

fun notify_all c thy =
  thy
  |> get_reset_dirty
  |-> (fn (true, _) => fold (fn f => f NONE) (the_notify thy)
        | (false, cs) => let val cs' = case c of NONE => cs | SOME c => insert (op =) c cs
            in fold (fn f => f (SOME (maps (all_typs thy) cs'))) (the_notify thy) end);

fun notify_dirty thy =
  thy
  |> get_reset_dirty
  |-> (fn (true, _) => fold (fn f => f NONE) (the_notify thy)
        | (false, cs) => fold (fn f => f (SOME (maps (all_typs thy) cs))) (the_notify thy));


(* modifiers *)

fun add_preproc f =
  map_data (fn (x, (preproc, y)) =>
    (x, (preproc |> map_preproc (fn (preprocs, unfolds) => ((serial (), f) :: preprocs, unfolds)), y)))
  #> notify_all NONE;

fun add_fun_extr f =
  map_data (fn (x, (preproc, (extrs, funthms))) =>
    (x, (preproc, (extrs |> map_extrs (fn (funs, datatypes) =>
      ((serial (), f) :: funs, datatypes)), funthms))))
  #> notify_all NONE;

fun add_datatype_extr f =
  map_data (fn (x, (preproc, (extrs, funthms))) =>
    (x, (preproc, (extrs |> map_extrs (fn (funs, datatypes) =>
      (funs, (serial (), f) :: datatypes)), funthms))))
  #> notify_all NONE;

fun add_fun thm thy =
  case dest_fun thy thm
   of (c, _) =>
    thy
    |> map_data (fn (x, (preproc, (extrs, funthms))) =>
        (x, (preproc, (extrs, funthms |> map_funthms (fn (dirty, funs) =>
          (dirty, funs |> Symtab.default (c, []) |> Symtab.map_entry c (cons thm)))))))
    |> notify_all (SOME c);

fun del_fun thm thy =
  case dest_fun thy thm
   of (c, _) =>
    thy
    |> map_data (fn (x, (preproc, (extrs, funthms))) =>
        (x, (preproc, (extrs, funthms |> map_funthms (fn (dirty, funs) =>
          (dirty, funs |> Symtab.map_entry c (remove eq_thm thm)))))))
    |> notify_all (SOME c);

fun add_unfold thm thy =
  thy
  |> tap (fn thy => dest_eq thy thm)
  |> map_data (fn (x, (preproc, y)) =>
       (x, (preproc |> map_preproc (fn (preprocs, unfolds) =>
         (preprocs, thm :: unfolds)), y)))
  |> notify_all NONE;

fun del_unfold thm = 
  map_data (fn (x, (preproc, y)) =>
       (x, (preproc |> map_preproc (fn (preprocs, unfolds) =>
         (preprocs, remove eq_thm thm unfolds)), y)))
  #> notify_all NONE;

fun purge_defs (c, ty) thy =
  thy
  |> map_data (fn (x, (preproc, (extrs, funthms))) =>
      (x, (preproc, (extrs, funthms |> map_funthms (fn (dirty, funs) =>
        (dirty, funs |> Symtab.map_entry c
            (filter (fn thm => Sign.typ_instance thy
              ((fst o snd o dest_fun thy) thm, ty)))))))))
  |> notify_all (SOME c);



(** theorem handling **)

(* preprocessing *)

fun common_typ thy _ [] = []
  | common_typ thy _ [thm] = [thm]
  | common_typ thy extract_typ thms =
      let
        fun incr_thm thm max =
          let
            val thm' = incr_indexes max thm;
            val max' = (maxidx_of_typ o type_of o Drule.plain_prop_of) thm' + 1;
          in (thm', max') end;
        val (thms', maxidx) = fold_map incr_thm thms 0;
        val (ty1::tys) = map extract_typ thms;
        fun unify ty = Sign.typ_unify thy (ty1, ty);
        val (env, _) = fold unify tys (Vartab.empty, maxidx)
        val instT = Vartab.fold (fn (x_i, (sort, ty)) =>
          cons (Thm.ctyp_of thy (TVar (x_i, sort)), Thm.ctyp_of thy ty)) env [];
      in map (Thm.instantiate (instT, [])) thms end;

fun preprocess thy thms =
  let
    fun burrow_thms f [] = []
      | burrow_thms f thms = 
          thms
          |> Conjunction.intr_list
          |> f
          |> Conjunction.elim_list;
    fun extr_typ thm = case dest_fun thy thm
     of (_, (ty, _)) => ty;
    fun tap_typ [] = NONE
     | tap_typ (thms as (thm::_)) = SOME (extr_typ thm, thms);
    fun cmp_thms (thm1, thm2) =
      not (Sign.typ_instance thy (extr_typ thm1, extr_typ thm2));
    fun rewrite_rhs conv thm = (case (Drule.strip_comb o cprop_of) thm
     of (ct', [ct1, ct2]) => (case term_of ct'
         of Const ("==", _) =>
              Thm.equal_elim (combination (combination (reflexive ct') (reflexive ct1)) (conv ct2)) thm
          | _ => raise ERROR "rewrite_rhs")
      | _ => raise ERROR "rewrite_rhs");
    fun unvarify thms =
      #1 (Variable.import true thms (ProofContext.init thy));
    val unfold_thms = Tactic.rewrite true (map (make_eq thy) (the_unfolds thy));
  in
    thms
    |> map (make_eq thy)
    |> map (Thm.transfer thy)
    |> fold (fn f => f thy) (the_preprocs thy)
    |> map (rewrite_rhs unfold_thms)
    |> debug_msg (fn _ => "[cg_thm] sorting")
    |> debug_msg (commas o map string_of_thm)
    |> sort (make_ord cmp_thms)
    |> debug_msg (fn _ => "[cg_thm] common_typ")
    |> debug_msg (commas o map string_of_thm)
    |> common_typ thy extr_typ
    |> debug_msg (fn _ => "[cg_thm] abs_norm")
    |> debug_msg (commas o map string_of_thm)
    |> map (abs_norm thy)
    |> burrow_thms (
        debug_msg (fn _ => "[cg_thm] canonical tvars")
        #> debug_msg (string_of_thm)
        #> canonical_tvars thy
        #> debug_msg (fn _ => "[cg_thm] canonical vars")
        #> debug_msg (string_of_thm)
        #> canonical_vars thy
        #> debug_msg (fn _ => "[cg_thm] zero indices")
        #> debug_msg (string_of_thm)
        #> Drule.zero_var_indexes
       )
    |> drop_redundant thy
    |> unvarify
    |> tap_typ
  end;


(* retrieval *)

fun get_funs thy (c, ty) =
  let
    val _ = debug_msg (fn _ => "[cg_thm] const (1) " ^ c ^ " :: " ^ Sign.string_of_typ thy ty) ()
    val filter_typ = map_filter (fn (_, (ty', thm)) =>
      if Sign.typ_instance thy (ty, ty')
      then SOME thm else debug_msg (fn _ => "[cg_thm] dropping " ^ string_of_thm thm) NONE);
    fun get_funs (c, ty) =
      (these o Symtab.lookup (the_funs thy)) c
      |> debug_msg (fn _ => "[cg_thm] trying funs")
      |> map (dest_fun thy)
      |> filter_typ;
    fun get_extr (c, ty) =
      getf_first_list (map (fn f => f thy) (the_funs_extrs thy)) (c, ty)
      |> debug_msg (fn _ => "[cg_thm] trying extr")
      |> map (dest_fun thy)
      |> filter_typ;
    fun get_spec (c, ty) =
      Theory.definitions_of thy c
      |> debug_msg (fn _ => "[cg_thm] trying spec")
      (* FIXME avoid dynamic name space lookup!? (via Thm.get_axiom_i etc.??) *)
      |> maps (PureThy.get_thms thy o Name o #name)
      |> map_filter (try (dest_fun thy))
      |> filter_typ;
  in
    getf_first_list [get_funs, get_extr, get_spec] (c, ty)
    |> debug_msg (fn _ => "[cg_thm] const (2) " ^ c ^ " :: " ^ Sign.string_of_typ thy ty)
    |> preprocess thy
  end;

fun get_datatypes thy dtco =
  let
    val _ = debug_msg (fn _ => "[cg_thm] datatype " ^ dtco) ()
    val truh = mk_true thy;
    val fals = mk_false thy;
    fun mk_lhs vs ((co1, tys1), (co2, tys2)) =
      let
        val dty = Type (dtco, map TFree vs);
        val (xs1, xs2) = chop (length tys1) (Term.invent_names [] "x" (length tys1 + length tys2));
        val frees1 = map2 (fn x => fn ty => Free (x, ty)) xs1 tys1;
        val frees2 = map2 (fn x => fn ty => Free (x, ty)) xs2 tys2;
        fun zip_co co xs tys = list_comb (Const (co,
          tys ---> dty), map2 (fn x => fn ty => Free (x, ty)) xs tys);
      in
        ((frees1, frees2), (zip_co co1 xs1 tys1, zip_co co2 xs2 tys2))
      end;
    fun mk_rhs [] [] = truh
      | mk_rhs xs ys = foldr1 (mk_obj_conj thy) (map2 (curry (mk_obj_eq thy)) xs ys);
    fun mk_eq vs (args as ((co1, _), (co2, _))) (inj, dist) =
      if co1 = co2
        then let
          val ((fs1, fs2), lhs) = mk_lhs vs args;
          val rhs = mk_rhs fs1 fs2;
        in (mk_func thy (lhs, rhs) :: inj, dist) end
        else let
          val (_, lhs) = mk_lhs vs args;
        in (inj, mk_func thy (lhs, fals) :: dist) end;
    fun mk_eqs (vs, cos) =
      let val cos' = rev cos 
      in (op @) (fold (mk_eq vs) (product cos' cos') ([], [])) end;
    fun mk_eq_thms tac vs_cos =
      map (fn t => Goal.prove thy [] []
        (ObjectLogic.ensure_propT thy t) (K tac) |> standard) (mk_eqs vs_cos);
  in
    case getf_first (map (fn f => f thy) (the_datatypes_extrs thy)) dtco
     of NONE => NONE
      | SOME (vs_cos, tac) => SOME (vs_cos, mk_eq_thms tac vs_cos)
  end;

fun get_eq thy (c, ty) =
  if is_obj_eq thy c
  then case strip_type ty
   of (Type (tyco, _) :: _, _) =>
     (case get_datatypes thy tyco
       of SOME (_, thms) => thms
        | _ => [])
    | _ => []
  else [];

type thmtab = ((thm list Typtab.table Symtab.table
  * string Symtab.table)
  * ((string * sort) list * (string * typ list) list) Symtab.table);

(*
fun mk_thmtab thy cs =
  let
    fun add_c (c, ty) gr =
    (*
      Das ist noch viel komplizierter: Zyklen
      und die aktuellen Instantiierungen muss man auch noch mitschleppen
      man sieht: man braucht zusätzlich ein Mapping
        c ~> [ty] (Symtab)
      wobei dort immer die bislang allgemeinsten... ???
    *)
    (*
      thm holen für bestimmten typ
      typ dann behalten
      typ normalisieren
      damit haben wir den key
      hier den check machen, ob schon prozessiert wurde
      NEIN:
        ablegen
        consts der rechten Seiten
        in die Rekursion gehen für alles
      JA:
        fertig
    *)
  in fold add_c cs Constgraph.empty end;

fun get_thmtab cs thy =
  thy
  |> get_reset_dirty
  |-> (fn _ => I)
  |> `mk_thmtab;
*)


(** code attributes and setup **)

local
  fun add_simple_attribute (name, f) =
    (Codegen.add_attribute name o (Scan.succeed o Thm.declaration_attribute))
      (Context.map_theory o f);
in
  val _ = map (Context.add_setup o add_simple_attribute) [
    ("fun", add_fun),
    ("unfold", (fn thm => Codegen.add_unfold thm #> add_unfold thm)),
    ("unfolt", add_unfold),
    ("nofold", del_unfold)
  ]
end; (*local*)

val _ = Context.add_setup (add_fun_extr get_eq);

end; (*struct*)
