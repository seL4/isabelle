(*  Title:      Pure/axclass.ML
    Author:     Markus Wenzel, TU Muenchen

Type classes defined as predicates, associated with a record of
parameters.
*)

signature AX_CLASS =
sig
  val define_class: binding * class list -> string list ->
    (Thm.binding * term list) list -> theory -> class * theory
  val add_classrel: thm -> theory -> theory
  val add_arity: thm -> theory -> theory
  val prove_classrel: class * class -> tactic -> theory -> theory
  val prove_arity: string * sort list * sort -> tactic -> theory -> theory
  type info = {def: thm, intro: thm, axioms: thm list, params: (string * typ) list}
  val get_info: theory -> class -> info
  val class_intros: theory -> thm list
  val class_of_param: theory -> string -> class option
  val cert_classrel: theory -> class * class -> class * class
  val read_classrel: theory -> xstring * xstring -> class * class
  val axiomatize_class: binding * class list -> theory -> theory
  val axiomatize_class_cmd: binding * xstring list -> theory -> theory
  val axiomatize_classrel: (class * class) list -> theory -> theory
  val axiomatize_classrel_cmd: (xstring * xstring) list -> theory -> theory
  val axiomatize_arity: arity -> theory -> theory
  val axiomatize_arity_cmd: xstring * string list * string -> theory -> theory
  val instance_name: string * class -> string
  val declare_overloaded: string * typ -> theory -> term * theory
  val define_overloaded: binding -> string * term -> theory -> thm * theory
  val unoverload: theory -> thm -> thm
  val overload: theory -> thm -> thm
  val unoverload_conv: theory -> conv
  val overload_conv: theory -> conv
  val unoverload_const: theory -> string * typ -> string
  val lookup_inst_param: Consts.T -> ((string * string) * 'a) list -> string * typ -> 'a option
  val param_of_inst: theory -> string * string -> string
  val inst_of_param: theory -> string -> (string * string) option
  val thynames_of_arity: theory -> class * string -> string list
end;

structure AxClass: AX_CLASS =
struct

(** theory data **)

(* class parameters (canonical order) *)

type param = string * class;

fun add_param pp ((x, c): param) params =
  (case AList.lookup (op =) params x of
    NONE => (x, c) :: params
  | SOME c' => error ("Duplicate class parameter " ^ quote x ^
      " for " ^ Pretty.string_of_sort pp [c] ^
      (if c = c' then "" else " and " ^ Pretty.string_of_sort pp [c'])));

fun merge_params _ ([], qs) = qs
  | merge_params pp (ps, qs) =
      fold_rev (fn q => if member (op =) ps q then I else add_param pp q) qs ps;


(* axclass info *)

type info =
 {def: thm,
  intro: thm,
  axioms: thm list,
  params: (string * typ) list};

type axclasses = info Symtab.table * param list;

fun make_axclass ((def, intro, axioms), params): info =
  {def = def, intro = intro, axioms = axioms, params = params};

fun merge_axclasses pp ((tab1, params1), (tab2, params2)) : axclasses =
  (Symtab.merge (K true) (tab1, tab2), merge_params pp (params1, params2));


(* instances *)

val classrel_prefix = "classrel_";
val arity_prefix = "arity_";

type instances =
  (thm * proof) Symreltab.table *  (*classrel theorems*)
  ((class * sort list) * ((thm * string) * proof)) list Symtab.table;  (*arity theorems with theory name*)

(*transitive closure of classrels and arity completion is done in Theory.at_begin hook*)
fun merge_instances ((classrel1, arities1): instances, (classrel2, arities2)) =
 (Symreltab.join (K fst) (classrel1, classrel2),
  Symtab.join (K (merge (eq_fst op =))) (arities1, arities2));


(* instance parameters *)

type inst_params =
  (string * thm) Symtab.table Symtab.table
    (*constant name ~> type constructor ~> (constant name, equation)*)
  * (string * string) Symtab.table; (*constant name ~> (constant name, type constructor)*)

fun merge_inst_params ((const_param1, param_const1), (const_param2, param_const2)) =
  (Symtab.join  (K (Symtab.merge (K true))) (const_param1, const_param2),
    Symtab.merge (K true) (param_const1, param_const2));


(* setup data *)

structure Data = Theory_Data_PP
(
  type T = axclasses * ((instances * inst_params) * (class * class) list);
  val empty = ((Symtab.empty, []), (((Symreltab.empty, Symtab.empty), (Symtab.empty, Symtab.empty)), []));
  val extend = I;
  fun merge pp ((axclasses1, ((instances1, inst_params1), diff_merge_classrels1)),
    (axclasses2, ((instances2, inst_params2), diff_merge_classrels2))) =
    let
      val (classrels1, classrels2) = pairself (Symreltab.keys o fst) (instances1, instances2);
      val diff_merge_classrels =
        subtract (op =) classrels1 classrels2 @
        subtract (op =) classrels2 classrels1 @
        diff_merge_classrels1 @ diff_merge_classrels2;
    in
      (merge_axclasses pp (axclasses1, axclasses2),
        ((merge_instances (instances1, instances2), merge_inst_params (inst_params1, inst_params2)),
          diff_merge_classrels))
    end;
);


(* maintain axclasses *)

val get_axclasses = #1 o Data.get;
val map_axclasses = Data.map o apfst;

fun get_info thy c =
  (case Symtab.lookup (#1 (get_axclasses thy)) c of
    SOME info => info
  | NONE => error ("No such axclass: " ^ quote c));

fun class_intros thy =
  let
    fun add_intro c = (case try (get_info thy) c of SOME {intro, ...} => cons intro | _ => I);
    val classes = Sign.all_classes thy;
  in map (Thm.class_triv thy) classes @ fold add_intro classes [] end;

fun all_params_of thy S =
  let val params = #2 (get_axclasses thy);
  in fold (fn (x, c) => if Sign.subsort thy (S, [c]) then cons x else I) params [] end;

fun class_of_param thy = AList.lookup (op =) (#2 (get_axclasses thy));


(* maintain instances *)

fun instance_name (a, c) = Long_Name.base_name c ^ "_" ^ Long_Name.base_name a;

val get_instances = #1 o #1 o #2 o Data.get;
val map_instances = Data.map o apsnd o apfst o apfst;

val get_diff_merge_classrels = #2 o #2 o Data.get;
val clear_diff_merge_classrels = Data.map (apsnd (apsnd (K [])));


fun the_classrel thy (c1, c2) =
  (case Symreltab.lookup (#1 (get_instances thy)) (c1, c2) of
    SOME classrel => classrel
  | NONE => error ("Unproven class relation " ^
      Syntax.string_of_classrel (ProofContext.init thy) [c1, c2]));

fun the_classrel_thm thy = Thm.transfer thy o fst o the_classrel thy;
fun the_classrel_prf thy = snd o the_classrel thy;

fun put_trancl_classrel ((c1, c2), th) thy =
  let
    val cert = Thm.cterm_of thy;
    val certT = Thm.ctyp_of thy;

    val classrels = fst (get_instances thy);
    val classes = #classes (Sorts.rep_algebra (Sign.classes_of thy));

    fun reflcl_classrel (c1', c2') =
      if c1' = c2'
      then Thm.trivial (cert (Logic.mk_of_class (TVar ((Name.aT, 0), []), c1')))
      else the_classrel_thm thy (c1', c2');
    fun gen_classrel (c1_pred, c2_succ) =
      let
        val th' = ((reflcl_classrel (c1_pred, c1) RS th) RS reflcl_classrel (c2, c2_succ))
          |> Drule.instantiate' [SOME (certT (TVar ((Name.aT, 0), [])))] []
          |> Thm.close_derivation;
        val prf' = th' |> Thm.proof_of;
      in ((c1_pred, c2_succ), (th', prf')) end;

    val new_classrels =
      Library.map_product pair (c1 :: Graph.imm_preds classes c1) (c2 :: Graph.imm_succs classes c2)
      |> filter_out (Symreltab.defined classrels)
      |> map gen_classrel;
    val needed = not (null new_classrels);
  in
    (needed,
     if needed then
       thy |> map_instances (fn (classrels, arities) =>
         (classrels |> fold Symreltab.update new_classrels, arities))
     else thy)
  end;

fun complete_classrels thy =
  let
    val diff_merge_classrels = get_diff_merge_classrels thy;
    val classrels = fst (get_instances thy);
    val (needed, thy') = (false, thy) |>
      fold (fn c12 => fn (needed, thy) =>
          put_trancl_classrel (c12, Symreltab.lookup classrels c12 |> the |> fst) thy
          |>> (fn b => needed orelse b))
        diff_merge_classrels;
  in
    if null diff_merge_classrels then NONE
    else thy' |> clear_diff_merge_classrels |> SOME
  end;


fun the_arity thy a (c, Ss) =
  (case AList.lookup (op =) (Symtab.lookup_list (#2 (get_instances thy)) a) (c, Ss) of
    SOME arity => arity
  | NONE => error ("Unproven type arity " ^
      Syntax.string_of_arity (ProofContext.init thy) (a, Ss, [c])));

fun the_arity_thm thy a c_Ss = the_arity thy a c_Ss |> fst |> fst |> Thm.transfer thy;
fun the_arity_prf thy a c_Ss = the_arity thy a c_Ss |> snd;

fun thynames_of_arity thy (c, a) =
  Symtab.lookup_list (#2 (get_instances thy)) a
  |> map_filter (fn ((c', _), ((_, name),_)) => if c = c' then SOME name else NONE)
  |> rev;

fun insert_arity_completions thy (t, ((c, Ss), ((th, thy_name), _))) arities =
  let
    val algebra = Sign.classes_of thy;
    val super_class_completions =
      Sign.super_classes thy c
      |> filter_out (fn c1 => exists (fn ((c2, Ss2), _) => c1 = c2
          andalso Sorts.sorts_le algebra (Ss2, Ss)) (Symtab.lookup_list arities t));
    val names_and_Ss = Name.names Name.context Name.aT (map (K []) Ss);
    val completions = super_class_completions |> map (fn c1 =>
      let
        val th1 = (th RS the_classrel_thm thy (c, c1))
          |> Drule.instantiate' (map (SOME o ctyp_of thy o TVar o apfst (rpair 0)) names_and_Ss) []
          |> Thm.close_derivation;
        val prf1 = Thm.proof_of th1;
      in (((th1, thy_name), prf1), c1) end);
    val arities' = fold (fn (th_thy_prf1, c1) => Symtab.cons_list (t, ((c1, Ss), th_thy_prf1)))
      completions arities;
  in (null completions, arities') end;

fun put_arity ((t, Ss, c), th) thy =
  let
    val arity' = (t, ((c, Ss), ((th, Context.theory_name thy), Thm.proof_of th)));
  in
    thy
    |> map_instances (fn (classrel, arities) => (classrel,
      arities
      |> Symtab.insert_list (eq_fst op =) arity'
      |> insert_arity_completions thy arity'
      |> snd))
  end;

fun complete_arities thy =
  let
    val arities = snd (get_instances thy);
    val (finished, arities') = arities
      |> fold_map (insert_arity_completions thy) (Symtab.dest_list arities);
  in
    if forall I finished then NONE
    else SOME (thy |> map_instances (fn (classrel, _) => (classrel, arities')))
  end;

val _ = Context.>> (Context.map_theory
  (Theory.at_begin complete_classrels #> Theory.at_begin complete_arities))


(* maintain instance parameters *)

val get_inst_params = #2 o #1 o #2 o Data.get;
val map_inst_params = Data.map o apsnd o apfst o apsnd;

fun get_inst_param thy (c, tyco) =
  (case Symtab.lookup (the_default Symtab.empty (Symtab.lookup (#1 (get_inst_params thy)) c)) tyco of
    SOME c' => c'
  | NONE => error ("No instance parameter for constant " ^ quote c ^ " on type " ^ quote tyco));

fun add_inst_param (c, tyco) inst =
  (map_inst_params o apfst o Symtab.map_default (c, Symtab.empty)) (Symtab.update_new (tyco, inst))
  #> (map_inst_params o apsnd) (Symtab.update_new (fst inst, (c, tyco)));

val inst_of_param = Symtab.lookup o snd o get_inst_params;
val param_of_inst = fst oo get_inst_param;

fun inst_thms thy =
  (Symtab.fold (Symtab.fold (cons o snd o snd) o snd) o fst) (get_inst_params thy) [];

fun get_inst_tyco consts = try (fst o dest_Type o the_single o Consts.typargs consts);

fun unoverload thy = MetaSimplifier.simplify true (inst_thms thy);
fun overload thy = MetaSimplifier.simplify true (map Thm.symmetric (inst_thms thy));

fun unoverload_conv thy = MetaSimplifier.rewrite true (inst_thms thy);
fun overload_conv thy = MetaSimplifier.rewrite true (map Thm.symmetric (inst_thms thy));

fun lookup_inst_param consts params (c, T) =
  (case get_inst_tyco consts (c, T) of
    SOME tyco => AList.lookup (op =) params (c, tyco)
  | NONE => NONE);

fun unoverload_const thy (c_ty as (c, _)) =
  if is_some (class_of_param thy c) then
    (case get_inst_tyco (Sign.consts_of thy) c_ty of
      SOME tyco => try (param_of_inst thy) (c, tyco) |> the_default c
    | NONE => c)
  else c;



(** instances **)

(* class relations *)

fun cert_classrel thy raw_rel =
  let
    val string_of_sort = Syntax.string_of_sort_global thy;
    val (c1, c2) = pairself (Sign.certify_class thy) raw_rel;
    val _ = Sign.primitive_classrel (c1, c2) (Theory.copy thy);
    val _ =
      (case subtract (op =) (all_params_of thy [c1]) (all_params_of thy [c2]) of
        [] => ()
      | xs => raise TYPE ("Class " ^ string_of_sort [c1] ^ " lacks parameter(s) " ^
          commas_quote xs ^ " of " ^ string_of_sort [c2], [], []));
  in (c1, c2) end;

fun read_classrel thy raw_rel =
  cert_classrel thy (pairself (ProofContext.read_class (ProofContext.init thy)) raw_rel)
    handle TYPE (msg, _, _) => error msg;

val shyps_topped = forall null o #shyps o Thm.rep_thm;


(* declaration and definition of instances of overloaded constants *)

fun inst_tyco_of thy (c, T) =
  (case get_inst_tyco (Sign.consts_of thy) (c, T) of
    SOME tyco => tyco
  | NONE => error ("Illegal type for instantiation of class parameter: " ^
      quote (c ^ " :: " ^ Syntax.string_of_typ_global thy T)));

fun declare_overloaded (c, T) thy =
  let
    val class =
      (case class_of_param thy c of
        SOME class => class
      | NONE => error ("Not a class parameter: " ^ quote c));
    val tyco = inst_tyco_of thy (c, T);
    val name_inst = instance_name (tyco, class) ^ "_inst";
    val c' = Long_Name.base_name c ^ "_" ^ Long_Name.base_name tyco;
    val T' = Type.strip_sorts T;
  in
    thy
    |> Sign.qualified_path true (Binding.name name_inst)
    |> Sign.declare_const ((Binding.name c', T'), NoSyn)
    |-> (fn const' as Const (c'', _) =>
      Thm.add_def false true
        (Binding.name (Thm.def_name c'), Logic.mk_equals (Const (c, T'), const'))
      #>> apsnd Thm.varifyT_global
      #-> (fn (_, thm) => add_inst_param (c, tyco) (c'', thm)
        #> PureThy.add_thm ((Binding.conceal (Binding.name c'), thm), [])
        #> snd
        #> pair (Const (c, T))))
    ||> Sign.restore_naming thy
  end;

fun define_overloaded b (c, t) thy =
  let
    val T = Term.fastype_of t;
    val tyco = inst_tyco_of thy (c, T);
    val (c', eq) = get_inst_param thy (c, tyco);
    val prop = Logic.mk_equals (Const (c', T), t);
    val b' = Thm.def_binding_optional
      (Binding.name (Long_Name.base_name c ^ "_" ^ Long_Name.base_name tyco)) b;
  in
    thy
    |> Thm.add_def false false (b', prop)
    |>> (fn (_, thm) =>  Drule.transitive_thm OF [eq, thm])
  end;


(* primitive rules *)

fun add_classrel raw_th thy =
  let
    val th = Thm.strip_shyps (Thm.transfer thy raw_th);
    val prop = Thm.plain_prop_of th;
    fun err () = raise THM ("add_classrel: malformed class relation", 0, [th]);
    val rel = Logic.dest_classrel prop handle TERM _ => err ();
    val (c1, c2) = cert_classrel thy rel handle TYPE _ => err ();
    val th' = th
      |> Drule.instantiate' [SOME (ctyp_of thy (TVar ((Name.aT, 0), [c1])))] []
      |> Drule.unconstrainTs;
    val _ = shyps_topped th' orelse raise Fail "add_classrel: nontop shyps after unconstrain";
  in
    thy
    |> Sign.primitive_classrel (c1, c2)
    |> (snd oo put_trancl_classrel) ((c1, c2), th')
    |> perhaps complete_arities
  end;

fun add_arity raw_th thy =
  let
    val th = Thm.strip_shyps (Thm.transfer thy raw_th);
    val prop = Thm.plain_prop_of th;
    fun err () = raise THM ("add_arity: malformed type arity", 0, [th]);
    val (t, Ss, c) = Logic.dest_arity prop handle TERM _ => err ();
    val names = Name.names Name.context Name.aT Ss;
    val T = Type (t, map TFree names);
    val missing_params = Sign.complete_sort thy [c]
      |> maps (these o Option.map #params o try (get_info thy))
      |> filter_out (fn (const, _) => can (get_inst_param thy) (const, t))
      |> (map o apsnd o map_atyps) (K T);
    val _ = map (Sign.certify_sort thy) Ss = Ss orelse err ();
    val th' = th
      |> Drule.instantiate' (map (SOME o ctyp_of thy o TVar o apfst (rpair 0)) names) []
      |> Drule.unconstrainTs;
    val _ = shyps_topped th' orelse raise Fail "add_arity: nontop shyps after unconstrain";
  in
    thy
    |> fold (snd oo declare_overloaded) missing_params
    |> Sign.primitive_arity (t, Ss, [c])
    |> put_arity ((t, Ss, c), th')
  end;


(* tactical proofs *)

fun prove_classrel raw_rel tac thy =
  let
    val ctxt = ProofContext.init thy;
    val (c1, c2) = cert_classrel thy raw_rel;
    val th = Goal.prove ctxt [] [] (Logic.mk_classrel (c1, c2)) (K tac) handle ERROR msg =>
      cat_error msg ("The error(s) above occurred while trying to prove class relation " ^
        quote (Syntax.string_of_classrel ctxt [c1, c2]));
  in
    thy
    |> PureThy.add_thms [((Binding.name
        (prefix classrel_prefix (Logic.name_classrel (c1, c2))), th), [])]
    |-> (fn [th'] => add_classrel th')
  end;

fun prove_arity raw_arity tac thy =
  let
    val ctxt = ProofContext.init thy;
    val arity = ProofContext.cert_arity ctxt raw_arity;
    val names = map (prefix arity_prefix) (Logic.name_arities arity);
    val props = Logic.mk_arities arity;
    val ths = Goal.prove_multi ctxt [] [] props
      (fn _ => Goal.precise_conjunction_tac (length props) 1 THEN tac) handle ERROR msg =>
        cat_error msg ("The error(s) above occurred while trying to prove type arity " ^
          quote (Syntax.string_of_arity ctxt arity));
  in
    thy
    |> PureThy.add_thms (map (rpair []) (map Binding.name names ~~ ths))
    |-> fold add_arity
  end;



(** class definitions **)

fun split_defined n eq =
  let
    val intro =
      (eq RS Drule.equal_elim_rule2)
      |> Conjunction.curry_balanced n
      |> n = 0 ? Thm.eq_assumption 1;
    val dests =
      if n = 0 then []
      else
        (eq RS Drule.equal_elim_rule1)
        |> Balanced_Tree.dest (fn th =>
          (th RS Conjunction.conjunctionD1, th RS Conjunction.conjunctionD2)) n;
  in (intro, dests) end;

fun define_class (bclass, raw_super) raw_params raw_specs thy =
  let
    val ctxt = ProofContext.init thy;
    val pp = Syntax.pp ctxt;


    (* class *)

    val bconst = Binding.map_name Logic.const_of_class bclass;
    val class = Sign.full_name thy bclass;
    val super = Sign.minimize_sort thy (Sign.certify_sort thy raw_super);

    fun check_constraint (a, S) =
      if Sign.subsort thy (super, S) then ()
      else error ("Sort constraint of type variable " ^
        setmp_CRITICAL show_sorts true (Pretty.string_of_typ pp) (TFree (a, S)) ^
        " needs to be weaker than " ^ Pretty.string_of_sort pp super);


    (* params *)

    val params = raw_params |> map (fn p =>
      let
        val T = Sign.the_const_type thy p;
        val _ =
          (case Term.add_tvarsT T [] of
            [((a, _), S)] => check_constraint (a, S)
          | _ => error ("Exactly one type variable expected in class parameter " ^ quote p));
        val T' = Term.map_type_tvar (fn _ => TFree (Name.aT, [class])) T;
      in (p, T') end);


    (* axioms *)

    fun prep_axiom t =
      (case Term.add_tfrees t [] of
        [(a, S)] => check_constraint (a, S)
      | [] => ()
      | _ => error ("Multiple type variables in class axiom:\n" ^ Pretty.string_of_term pp t);
      t
      |> Term.map_types (Term.map_atyps (fn TFree _ => Term.aT [] | U => U))
      |> Logic.close_form);

    val axiomss = map (map (prep_axiom o Sign.cert_prop thy) o snd) raw_specs;
    val name_atts = map fst raw_specs;


    (* definition *)

    val conjs = Logic.mk_of_sort (Term.aT [], super) @ flat axiomss;
    val class_eq =
      Logic.mk_equals (Logic.mk_of_class (Term.aT [], class), Logic.mk_conjunction_balanced conjs);

    val ([def], def_thy) =
      thy
      |> Sign.primitive_class (bclass, super)
      |> PureThy.add_defs false [((Thm.def_binding bconst, class_eq), [])];
    val (raw_intro, (raw_classrel, raw_axioms)) =
      split_defined (length conjs) def ||> chop (length super);


    (* facts *)

    val class_triv = Thm.class_triv def_thy class;
    val ([(_, [intro]), (_, classrel), (_, axioms)], facts_thy) =
      def_thy
      |> Sign.qualified_path true bconst
      |> PureThy.note_thmss ""
        [((Binding.name "intro", []), [([Drule.export_without_context raw_intro], [])]),
         ((Binding.name "super", []), [(map Drule.export_without_context raw_classrel, [])]),
         ((Binding.name "axioms", []),
           [(map (fn th => Drule.export_without_context (class_triv RS th)) raw_axioms, [])])]
      ||> Sign.restore_naming def_thy;


    (* result *)

    val axclass = make_axclass ((def, intro, axioms), params);
    val result_thy =
      facts_thy
      |> fold (snd oo put_trancl_classrel) (map (pair class) super ~~ classrel)
      |> Sign.qualified_path false bconst
      |> PureThy.note_thmss "" (name_atts ~~ map Thm.simple_fact (unflat axiomss axioms)) |> snd
      |> Sign.restore_naming facts_thy
      |> map_axclasses (fn (axclasses, parameters) =>
        (Symtab.update (class, axclass) axclasses,
          fold (fn (x, _) => add_param pp (x, class)) params parameters));

  in (class, result_thy) end;



(** axiomatizations **)

local

(* old-style axioms *)

fun add_axiom (b, prop) =
  Thm.add_axiom (b, prop) #->
  (fn (_, thm) => PureThy.add_thm ((b, Drule.export_without_context thm), []));

fun axiomatize prep mk name add raw_args thy =
  let
    val args = prep thy raw_args;
    val specs = mk args;
    val names = name args;
  in
    thy
    |> fold_map add_axiom (map Binding.name names ~~ specs)
    |-> fold add
  end;

fun ax_classrel prep =
  axiomatize (map o prep) (map Logic.mk_classrel)
    (map (prefix classrel_prefix o Logic.name_classrel)) add_classrel;

fun ax_arity prep =
  axiomatize (prep o ProofContext.init) Logic.mk_arities
    (map (prefix arity_prefix) o Logic.name_arities) add_arity;

fun class_const c =
  (Logic.const_of_class c, Term.itselfT (Term.aT []) --> propT);

fun ax_class prep_class prep_classrel (bclass, raw_super) thy =
  let
    val class = Sign.full_name thy bclass;
    val super = map (prep_class thy) raw_super |> Sign.minimize_sort thy;
  in
    thy
    |> Sign.primitive_class (bclass, super)
    |> ax_classrel prep_classrel (map (fn c => (class, c)) super)
    |> Theory.add_deps "" (class_const class) (map class_const super)
  end;

in

val axiomatize_class = ax_class Sign.certify_class cert_classrel;
val axiomatize_class_cmd = ax_class (ProofContext.read_class o ProofContext.init) read_classrel;
val axiomatize_classrel = ax_classrel cert_classrel;
val axiomatize_classrel_cmd = ax_classrel read_classrel;
val axiomatize_arity = ax_arity ProofContext.cert_arity;
val axiomatize_arity_cmd = ax_arity ProofContext.read_arity;

end;

end;
