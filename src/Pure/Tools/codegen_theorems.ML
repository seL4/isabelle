(*  Title:      Pure/Tools/codegen_theorems.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Theorems used for code generation.
*)

signature CODEGEN_THEOREMS =
sig
  val add_notify: (string option -> theory -> theory) -> theory -> theory;
  val add_preproc: (theory -> thm list -> thm list) -> theory -> theory;
  val add_fun_extr: (theory -> string * typ -> thm list) -> theory -> theory;
  val add_datatype_extr: (theory -> string
     -> (((string * sort) list * (string * typ list) list) * tactic) option)
    -> theory -> theory;
  val add_fun: thm -> theory -> theory;
  val add_pred: thm -> theory -> theory;
  val add_unfold: thm -> theory -> theory;
  val del_def: thm -> theory -> theory;
  val del_unfold: thm -> theory -> theory;
  val purge_defs: string * typ -> theory -> theory;

  val common_typ: theory -> (thm -> typ) -> thm list -> thm list;
  val preprocess: theory -> (thm -> typ) option -> thm list -> thm list;
  val preprocess_fun: theory -> thm list -> (typ * thm list) option;
  val preprocess_term: theory -> term -> term;
  val get_funs: theory -> string * typ -> (typ * thm list) option;
  val get_datatypes: theory -> string
    -> (((string * sort) list * (string * typ list) list) * thm list) option;

  val debug: bool ref;
  val debug_msg: ('a -> string) -> 'a -> 'a;

  val print_thms: theory -> unit;
  val init_obj: theory -> string -> string * (thm list -> tactic) -> string * (thm list -> tactic)
    -> string * (thm list -> tactic) -> string * (thm list -> tactic) -> unit;
end;

structure CodegenTheorems: CODEGEN_THEOREMS =
struct

(** auxiliary **)

val debug = ref false;
fun debug_msg f x = (if !debug then Output.debug (f x) else (); x);


(** object logic **)

val obj_bool_ref : string option ref = ref NONE;
val obj_true_ref : string option ref = ref NONE;
val obj_false_ref : string option ref = ref NONE;
val obj_and_ref : string option ref = ref NONE;
val obj_eq_ref : string option ref = ref NONE;
val obj_eq_elim_ref : thm option ref = ref NONE;
fun idem c = (the o !) c;

fun mk_tf sel =
  let
    val bool_typ = Type (idem obj_bool_ref, []);
    val name = idem
      (if sel then obj_true_ref else obj_false_ref);
  in
    Const (name, bool_typ)
  end handle Option => error "no object logic setup for code theorems";

fun mk_obj_conj (x, y) =
  let
    val bool_typ = Type (idem obj_bool_ref, []);
  in
    Const (idem obj_and_ref, bool_typ --> bool_typ --> bool_typ) $ x $ y
  end handle Option => error "no object logic setup for code theorems";

fun mk_obj_eq (x, y) =
  let
    val bool_typ = Type (idem obj_bool_ref, []);
  in
    Const (idem obj_eq_ref, type_of x --> type_of y --> bool_typ) $ x $ y
  end handle Option => error "no object logic setup for code theorems";

fun is_obj_eq c =
  c = idem obj_eq_ref
    handle Option => error "no object logic setup for code theorems";

fun mk_bool_eq ((x, y), rhs) =
  let
    val bool_typ = Type (idem obj_bool_ref, []);
  in
    Logic.mk_equals (
      (mk_obj_eq (x, y)),
      rhs
    )
  end handle Option => error "no object logic setup for code theorems";

fun elim_obj_eq thm = rewrite_rule [idem obj_eq_elim_ref] thm
  handle Option => error "no object logic setup for code theorems";

fun init_obj thy bohl (truh, truh_tac) (fals, fals_tac) (ant, ant_tac) (eq, eq_tac) =
  let
    val _ = if (is_some o !) obj_bool_ref
      then error "already set" else ()
    val bool_typ = Type (bohl, []);
    val free_typ  = TFree ("'a", Sign.defaultS thy);
    val var_x = Free ("x", free_typ);
    val var_y = Free ("y", free_typ);
    val prop_P = Free ("P", bool_typ);
    val prop_Q = Free ("Q", bool_typ);
    val _ = Goal.prove thy [] []
      (ObjectLogic.ensure_propT thy (Const (truh, bool_typ))) truh_tac;
    val _ = Goal.prove thy ["P"] [ObjectLogic.ensure_propT thy (Const (fals, bool_typ))]
      (ObjectLogic.ensure_propT thy prop_P) fals_tac;
    val _ = Goal.prove thy ["P", "Q"] [ObjectLogic.ensure_propT thy prop_P, ObjectLogic.ensure_propT thy prop_Q]
      (ObjectLogic.ensure_propT thy (Const (ant, bool_typ --> bool_typ --> bool_typ) $ prop_P $ prop_Q)) ant_tac;
    val atomize_eq = Goal.prove thy ["x", "y"] []
      (Logic.mk_equals (
        Logic.mk_equals (var_x, var_y),
        ObjectLogic.ensure_propT thy
          (Const (eq, free_typ --> free_typ --> bool_typ) $ var_x $ var_y))) eq_tac;
  in
    obj_bool_ref := SOME bohl;
    obj_true_ref := SOME truh;
    obj_false_ref := SOME fals;
    obj_and_ref := SOME ant;
    obj_eq_ref := SOME eq;
    obj_eq_elim_ref := SOME (Thm.symmetric atomize_eq)
  end;


(** auxiliary **)

fun destr_fun thy thm =
  case try (
    prop_of
    #> ObjectLogic.drop_judgment thy
    #> Logic.dest_equals
    #> fst
    #> strip_comb
    #> fst
    #> dest_Const
  ) (elim_obj_eq thm)
   of SOME c_ty => SOME (c_ty, thm)
    | NONE => NONE;

fun dest_fun thy thm =
  case destr_fun thy thm
   of SOME x => x
    | NONE => error ("not a function equation: " ^ string_of_thm thm);

fun dest_pred thm =
  case try (fst o dest_Const o fst o strip_comb o snd o Logic.dest_implies o prop_of) thm
   of SOME c => SOME (c, thm)
    | NONE => NONE;

fun getf_first [] _ = NONE
  | getf_first (f::fs) x = case f x
     of NONE => getf_first fs x
      | y as SOME x => y;

fun getf_first_list [] x = []
  | getf_first_list (f::fs) x = case f x
     of [] => getf_first_list fs x
      | xs => xs;
      

(** theory data **)

datatype procs = Procs of {
  preprocs: (serial * (theory -> thm list -> thm list)) list,
  notify: (serial * (string option -> theory -> theory)) list
};

fun mk_procs (preprocs, notify) = Procs { preprocs = preprocs, notify = notify };
fun map_procs f (Procs { preprocs, notify }) = mk_procs (f (preprocs, notify));
fun merge_procs _ (Procs { preprocs = preprocs1, notify = notify1 },
  Procs { preprocs = preprocs2, notify = notify2 }) =
    mk_procs (AList.merge (op =) (K true) (preprocs1, preprocs2),
      AList.merge (op =) (K true) (notify1, notify2));

datatype extrs = Extrs of {
  funs: (serial * (theory -> string * typ -> thm list)) list,
  datatypes: (serial * (theory -> string -> (((string * sort) list * (string * typ list) list) * tactic) option)) list
};

fun mk_extrs (funs, datatypes) = Extrs { funs = funs, datatypes = datatypes };
fun map_extrs f (Extrs { funs, datatypes }) = mk_extrs (f (funs, datatypes));
fun merge_extrs _ (Extrs { funs = funs1, datatypes = datatypes1 },
  Extrs { funs = funs2, datatypes = datatypes2 }) =
    mk_extrs (AList.merge (op =) (K true) (funs1, funs2),
      AList.merge (op =) (K true) (datatypes1, datatypes2));

datatype codethms = Codethms of {
  funs: thm list Symtab.table,
  preds: thm list Symtab.table,
  unfolds: thm list
};

fun mk_codethms ((funs, preds), unfolds) =
  Codethms { funs = funs, preds = preds, unfolds = unfolds };
fun map_codethms f (Codethms { funs, preds, unfolds }) =
  mk_codethms (f ((funs, preds), unfolds));
fun merge_codethms _ (Codethms { funs = funs1, preds = preds1, unfolds = unfolds1 },
  Codethms { funs = funs2, preds = preds2, unfolds = unfolds2 }) =
    mk_codethms ((Symtab.join (K (uncurry (fold (insert eq_thm)))) (funs1, funs2),
        Symtab.join (K (uncurry (fold (insert eq_thm)))) (preds1, preds2)),
          fold (insert eq_thm) unfolds1 unfolds2);

datatype codecache = Codecache of {
  funs: thm list Symtab.table,
  datatypes: (string * typ list) list Symtab.table
};

fun mk_codecache (funs, datatypes) = Codecache { funs = funs, datatypes = datatypes };
fun map_codecache f (Extrs { funs, datatypes }) = Codecache (f (funs, datatypes));
fun merge_codecache _ (Codecache { funs = funs1, datatypes = datatypes1 },
  Extrs { funs = funs2, datatypes = datatypes2 }) =
    mk_codecache (Symtab.empty, Symtab.empty);

datatype T = T of {
  procs: procs,
  extrs: extrs,
  codethms: codethms
};

fun mk_T (procs, (extrs, codethms)) = T { procs = procs, extrs = extrs, codethms = codethms };
fun map_T f (T { procs, extrs, codethms }) = mk_T (f (procs, (extrs, codethms)));
fun merge_T pp (T { procs = procs1, extrs = extrs1, codethms = codethms1 },
  T { procs = procs2, extrs = extrs2, codethms = codethms2 }) =
    mk_T (merge_procs pp (procs1, procs2), (merge_extrs pp (extrs1, extrs2), merge_codethms pp (codethms1, codethms2)));

structure CodegenTheorems = TheoryDataFun
(struct
  val name = "Pure/CodegenTheorems";
  type T = T;
  val empty = mk_T (mk_procs ([], []),
    (mk_extrs ([], []), mk_codethms ((Symtab.empty, Symtab.empty), [])));
  val copy = I;
  val extend = I;
  val merge = merge_T;
  fun print (thy : theory) (data : T) =
    let
      val codethms = (fn T { codethms, ... } => codethms) data;
      val funs = (Symtab.dest o (fn Codethms { funs, ... } => funs)) codethms;
      val preds = (Symtab.dest o (fn Codethms { preds, ... } => preds)) codethms;
      val unfolds = (fn Codethms { unfolds, ... } => unfolds) codethms;
    in
      (Pretty.writeln o Pretty.block o Pretty.fbreaks) ([
        Pretty.str "code generation theorems:",
        Pretty.str "function theorems:" ] @
        Pretty.fbreaks (
          map (fn (c, thms) => 
            (Pretty.block o Pretty.fbreaks) (
              Pretty.str c :: map Display.pretty_thm thms
            )
          ) funs
        ) @ [
        Pretty.str "predicate theorems:" ] @
        Pretty.fbreaks (
          map (fn (c, thms) => 
            (Pretty.block o Pretty.fbreaks) (
              Pretty.str c :: map Display.pretty_thm thms
            )
          ) preds
        ) @ [
        Pretty.str "unfolding theorems:",
        (Pretty.block o Pretty.fbreaks o map Display.pretty_thm) unfolds
      ])
    end;
end);

val _ = Context.add_setup CodegenTheorems.init;
val print_thms = CodegenTheorems.print;

local
  val the_procs = (fn T { procs = Procs procs, ... } => procs) o CodegenTheorems.get
  val the_extrs = (fn T { extrs = Extrs extrs, ... } => extrs) o CodegenTheorems.get
  val the_codethms = (fn T { codethms = Codethms codethms, ... } => codethms) o CodegenTheorems.get
in
  val the_preprocs = (fn { preprocs, ... } => map snd preprocs) o the_procs;
  val the_notify = (fn { notify, ... } => map snd notify) o the_procs;
  val the_funs_extrs = (fn { funs, ... } => map snd funs) o the_extrs;
  val the_datatypes_extrs = (fn { datatypes, ... } => map snd datatypes) o the_extrs;
  val the_funs = (fn { funs, ... } => funs) o the_codethms;
  val the_preds = (fn { preds, ... } => preds) o the_codethms;
  val the_unfolds = (fn { unfolds, ... } => unfolds) o the_codethms;
end (*local*);

fun add_notify f =
  CodegenTheorems.map (map_T (fn (procs, codethms) =>
    (procs |> map_procs (fn (preprocs, notify) =>
      (preprocs, (serial (), f) :: notify)), codethms)));

fun notify_all c thy =
  fold (fn f => f c) (the_notify thy) thy;

fun add_preproc f =
  CodegenTheorems.map (map_T (fn (procs, codethms) =>
    (procs |> map_procs (fn (preprocs, notify) =>
      ((serial (), f) :: preprocs, notify)), codethms)))
  #> notify_all NONE;

fun add_fun_extr f =
  CodegenTheorems.map (map_T (fn (procs, (extrs, codethms)) =>
    (procs, (extrs |> map_extrs (fn (funs, datatypes) =>
      ((serial (), f) :: funs, datatypes)), codethms))))
  #> notify_all NONE;

fun add_datatype_extr f =
  CodegenTheorems.map (map_T (fn (procs, (extrs, codethms)) =>
    (procs, (extrs |> map_extrs (fn (funs, datatypes) =>
      (funs, (serial (), f) :: datatypes)), codethms))))
  #> notify_all NONE;

fun add_fun thm thy =
  case destr_fun thy thm
   of SOME ((c, _), _) =>
        thy
        |> CodegenTheorems.map (map_T (fn (procs, (extrs, codethms)) =>
           (procs, (extrs, codethms |> map_codethms (fn ((funs, preds), unfolds) =>
            ((funs |> Symtab.default (c, []) |> Symtab.map_entry c (fn thms => thms @ [thm]), preds), unfolds))))))
        |> notify_all (SOME c)
    | NONE => tap (fn _ => warning ("not a function equation: " ^ string_of_thm thm)) thy;

fun add_pred thm thy =
  case dest_pred thm
   of SOME (c, _) =>
        thy
        |> CodegenTheorems.map (map_T (fn (procs, (extrs, codethms)) =>
          (procs, (extrs, codethms |> map_codethms (fn ((funs, preds), unfolds) =>
            ((funs, preds |> Symtab.default (c, []) |> Symtab.map_entry c (fn thms => thms @ [thm])), unfolds))))))
        |> notify_all (SOME c)
    | NONE => tap (fn _ => warning ("not a predicate clause: " ^ string_of_thm thm)) thy;

fun add_unfold thm =
  CodegenTheorems.map (map_T (fn (procs, (extrs, codethms)) =>
    (procs, (extrs, codethms |> map_codethms (fn (defs, unfolds) =>
      (defs, thm :: unfolds))))))
  #> notify_all NONE;

fun del_def thm thy =
  case destr_fun thy thm
   of SOME ((c, _), thm) =>
        thy
        |> CodegenTheorems.map (map_T (fn (procs, (extrs, codethms)) =>
           (procs, (extrs, codethms |> map_codethms (fn ((funs, preds), unfolds) =>
            ((funs |> Symtab.map_entry c (remove eq_thm thm), preds), unfolds))))))
        |> notify_all (SOME c)
    | NONE => case dest_pred thm
   of SOME (c, thm) =>
        thy
        |> CodegenTheorems.map (map_T (fn (procs, (extrs, codethms)) =>
           (procs, (extrs, codethms |> map_codethms (fn ((funs, preds), unfolds) =>
            ((funs, preds |> Symtab.map_entry c (remove eq_thm thm)), unfolds))))))
        |> notify_all (SOME c)
    | NONE => error ("no code theorem to delete");

fun del_unfold thm = 
  CodegenTheorems.map (map_T (fn (procs, (extrs, codethms)) =>
    (procs, (extrs, codethms |> map_codethms (fn (defs, unfolds) =>
      (defs, remove eq_thm thm unfolds))))))
  #> notify_all NONE;

fun purge_defs (c, ty) thy =
  thy
  |> CodegenTheorems.map (map_T (fn (procs, (extrs, codethms)) =>
      (procs, (extrs, codethms |> map_codethms (fn ((funs, preds), unfolds) =>
        ((funs |> Symtab.map_entry c
            (filter (fn thm => Sign.typ_instance thy ((snd o fst o dest_fun thy) thm, ty))),
          preds |> Symtab.update (c, [])), unfolds))))))
  |> notify_all (SOME c);


(** preprocessing **)

fun common_typ thy _ [] = []
  | common_typ thy _ [thm] = [thm]
  | common_typ thy extract_typ thms =
      let
        fun incr_thm thm max =
          let
            val thm' = incr_indexes max thm;
            val max' = (maxidx_of_typ o type_of o prop_of) thm' + 1;
          in (thm', max') end;
        val (thms', maxidx) = fold_map incr_thm thms 0;
        val (ty1::tys) = map extract_typ thms;
        fun unify ty = Type.unify (Sign.tsig_of thy) (ty1, ty);
        val (env, _) = fold unify tys (Vartab.empty, maxidx)
        val instT = Vartab.fold (fn (x_i, (sort, ty)) =>
          cons (Thm.ctyp_of thy (TVar (x_i, sort)), Thm.ctyp_of thy ty)) env [];
      in map (Thm.instantiate (instT, [])) thms end;

fun preprocess thy extract_typ thms =
  thms
  |> map (Thm.transfer thy)
  |> fold (fn f => f thy) (the_preprocs thy)
  |> map (rewrite_rule (the_unfolds thy))
  |> (if is_some extract_typ then common_typ thy (the extract_typ) else I)
  |> Drule.conj_intr_list
  |> Drule.zero_var_indexes
  |> Drule.conj_elim_list
  |> map Drule.unvarifyT
  |> map Drule.unvarify;

fun preprocess_fun thy thms =
  let
    fun tap_typ [] = NONE
      | tap_typ (thms as (thm::_)) = SOME ((snd o fst o dest_fun thy) thm, thms)
  in
    thms
    |> map elim_obj_eq
    |> preprocess thy (SOME (snd o fst o dest_fun thy))
    |> tap_typ
  end;

fun preprocess_term thy t =
  let
    val x = Free (variant (add_term_names (t, [])) "a", fastype_of t);
    (*fake definition*)
    val eq = setmp quick_and_dirty true (SkipProof.make_thm thy)
      (Logic.mk_equals (x, t));
    fun err () = error "preprocess_term: bad preprocessor"
  in case map prop_of (preprocess thy NONE [eq]) of
      [Const ("==", _) $ x' $ t'] => if x = x' then t' else err ()
    | _ => err ()
  end;


(** retrieval **)

fun get_funs thy (c, ty) =
  let
    val filter_typ = Library.mapfilter (fn ((_, ty'), thm) =>
      if Sign.typ_instance thy (ty', ty)
        orelse Sign.typ_instance thy (ty, ty')
      then SOME thm else debug_msg (fn _ => "dropping " ^ string_of_thm thm) NONE);
    val thms_funs = 
      (these o Symtab.lookup (the_funs thy)) c
      |> map (dest_fun thy)
      |> filter_typ;
    val thms = case thms_funs
     of [] =>
          Defs.specifications_of (Theory.defs_of thy) c
          |> map (PureThy.get_thms thy o Name o fst o snd)
          |> Library.flat
          |> append (getf_first_list (map (fn f => f thy) (the_funs_extrs thy)) (c, ty))
          |> map (dest_fun thy)
          |> filter_typ
      | thms => thms
  in
    thms
    |> preprocess_fun thy
  end;

fun get_datatypes thy dtco =
  let
    val truh = mk_tf true;
    val fals = mk_tf false;
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
      | mk_rhs xs ys = foldr1 mk_obj_conj (map2 (curry mk_obj_eq) xs ys);
    fun mk_eq vs (args as ((co1, _), (co2, _))) (inj, dist) =
      if co1 = co2
        then let
          val ((fs1, fs2), lhs) = mk_lhs vs args;
          val rhs = mk_rhs fs1 fs2;
        in (mk_bool_eq (lhs, rhs) :: inj, dist) end
        else let
          val (_, lhs) = mk_lhs vs args;
        in (inj, mk_bool_eq (lhs, fals) :: dist) end;
    fun mk_eqs (vs, cos) =
      let val cos' = rev cos 
      in (op @) (fold (mk_eq vs) (product cos' cos') ([], [])) end;
    fun mk_eq_thms tac vs_cos =
      map (fn t => (Goal.prove thy [] []
        (ObjectLogic.ensure_propT thy t) (K tac))) (mk_eqs vs_cos);
  in
    case getf_first (map (fn f => f thy) (the_datatypes_extrs thy)) dtco
     of NONE => NONE
      | SOME (vs_cos, tac) => SOME (vs_cos, mk_eq_thms tac vs_cos)
  end;

fun get_eq thy (c, ty) =
  if is_obj_eq c
  then case get_datatypes thy ((fst o dest_Type o hd o fst o strip_type) ty)
   of SOME (_, thms) => thms
    | _ => []
  else [];


(** code attributes and setup **)

local
  fun add_simple_attribute (name, f) =
    (Codegen.add_attribute name o (Scan.succeed o Thm.declaration_attribute))
      (Context.map_theory o f);
in
  val _ = map (Context.add_setup o add_simple_attribute) [
    ("fun", add_fun),
    ("pred", add_pred),
    ("unfold", (fn thm => Codegen.add_unfold thm #> add_unfold thm)),
    ("unfolt", add_unfold),
    ("nofold", del_unfold)
  ]
end; (*local*)

val _ = Context.add_setup (add_fun_extr get_eq);

end; (*struct*)
