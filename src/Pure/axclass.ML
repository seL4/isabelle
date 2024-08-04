(*  Title:      Pure/axclass.ML
    Author:     Markus Wenzel, TU Muenchen

Type classes defined as predicates, associated with a record of
parameters.  Proven class relations and type arities.
*)

signature AXCLASS =
sig
  type info = {def: thm, intro: thm, axioms: thm list, params: (string * typ) list}
  val get_info: theory -> class -> info
  val class_of_param: theory -> string -> class option
  val instance_name: string * class -> string
  val param_of_inst: theory -> string * string -> string
  val inst_of_param: theory -> string -> (string * string) option
  val unoverload: Proof.context -> thm -> thm
  val overload: Proof.context -> thm -> thm
  val unoverload_conv: Proof.context -> conv
  val overload_conv: Proof.context -> conv
  val lookup_inst_param: Consts.T -> ((string * string) * 'a) list -> string * typ -> 'a option
  val unoverload_const: theory -> string * typ -> string
  val cert_classrel: theory -> class * class -> class * class
  val read_classrel: theory -> xstring * xstring -> class * class
  val declare_overloaded: string * typ -> theory -> term * theory
  val define_overloaded: binding -> string * term -> theory -> thm * theory
  val add_classrel: thm -> theory -> theory
  val add_arity: thm -> theory -> theory
  val prove_classrel: class * class -> (Proof.context -> tactic) -> theory -> theory
  val prove_arity: string * sort list * sort -> (Proof.context -> tactic) -> theory -> theory
  val define_class: binding * class list -> string list ->
    (Thm.binding * term list) list -> theory -> class * theory
  val classrel_axiomatization: (class * class) list -> theory -> theory
  val arity_axiomatization: arity -> theory -> theory
  val class_axiomatization: binding * class list -> theory -> theory
end;

structure Axclass: AXCLASS =
struct

(** theory data **)

(* axclass info *)

type info =
 {def: thm,
  intro: thm,
  axioms: thm list,
  params: (string * typ) list};

fun make_axclass (def, intro, axioms, params): info =
  {def = def, intro = intro, axioms = axioms, params = params};


(* class parameters (canonical order) *)

type param = string * class;

fun add_param ctxt ((x, c): param) params =
  (case AList.lookup (op =) params x of
    NONE => (x, c) :: params
  | SOME c' =>
      error ("Duplicate class parameter " ^ quote x ^ " for " ^ Syntax.string_of_sort ctxt [c] ^
        (if c = c' then "" else " and " ^ Syntax.string_of_sort ctxt [c'])));


(* setup data *)

datatype data = Data of
 {axclasses: info Symtab.table,
  params: param list,
    (*arity theorems with theory name*)
  inst_params:
    (string * thm) Symtab.table Symtab.table *
      (*constant name ~> type constructor ~> (constant name, equation)*)
    (string * string) Symtab.table (*constant name ~> (constant name, type constructor)*)};

fun rep_data (Data args) = args;

fun make_data (axclasses, params, inst_params) =
  Data {axclasses = axclasses, params = params, inst_params = inst_params};

structure Data = Theory_Data'
(
  type T = data;
  val empty = make_data (Symtab.empty, [], (Symtab.empty, Symtab.empty));
  fun merge args =
    let
      val ctxt0 = Syntax.init_pretty_global (#1 (hd args));

      fun merge_params (params1, params2) =
        if null params1 then params2
        else
          fold_rev (fn p => if member (op =) params1 p then I else add_param ctxt0 p)
            params2 params1;

      fun merge_inst_params (inst_params1, inst_params2) =
        (Symtab.join (K (Symtab.merge (K true))) (#1 inst_params1, #1 inst_params2),
          Symtab.merge (K true) (#2 inst_params1, #2 inst_params2));

      val axclasses' = Library.foldl1 (Symtab.merge (K true)) (map (#axclasses o rep_data o #2) args);
      val params' = Library.foldl1 merge_params (map (#params o rep_data o #2) args);
      val inst_params' = Library.foldl1 merge_inst_params (map (#inst_params o rep_data o #2) args);
    in make_data (axclasses', params', inst_params') end;
);

fun map_data f =
  Data.map (fn Data {axclasses, params, inst_params} =>
    make_data (f (axclasses, params, inst_params)));

fun map_axclasses f =
  map_data (fn (axclasses, params, inst_params) =>
    (f axclasses, params, inst_params));

fun map_params f =
  map_data (fn (axclasses, params, inst_params) =>
    (axclasses, f params, inst_params));

fun map_inst_params f =
  map_data (fn (axclasses, params, inst_params) =>
    (axclasses, params, f inst_params));

val rep_theory_data = Data.get #> rep_data;

val axclasses_of = #axclasses o rep_theory_data;
val params_of = #params o rep_theory_data;
val inst_params_of = #inst_params o rep_theory_data;


(* axclasses with parameters *)

fun get_info thy c =
  (case Symtab.lookup (axclasses_of thy) c of
    SOME {def, intro, axioms, params} =>
      {def = Thm.transfer thy def,
       intro = Thm.transfer thy intro,
       axioms = map (Thm.transfer thy) axioms,
       params = params}
  | NONE => error ("No such axclass: " ^ quote c));

fun all_params_of thy S =
  let val params = params_of thy;
  in fold (fn (x, c) => if Sign.subsort thy (S, [c]) then cons x else I) params [] end;

fun class_of_param thy = AList.lookup (op =) (params_of thy);


(* maintain instance parameters *)

fun get_inst_param thy (c, tyco) =
  (case Symtab.lookup (the_default Symtab.empty (Symtab.lookup (#1 (inst_params_of thy)) c)) tyco of
    SOME (a, th) => (a, Thm.transfer thy th)
  | NONE => error ("No instance parameter for constant " ^ quote c ^ " on type " ^ quote tyco));

fun add_inst_param (c, tyco) (a, th) =
  (map_inst_params o apfst o Symtab.map_default (c, Symtab.empty))
    (Symtab.update_new (tyco, (a, Thm.trim_context th)))
  #> (map_inst_params o apsnd) (Symtab.update_new (a, (c, tyco)));

val inst_of_param = Symtab.lookup o #2 o inst_params_of;
val param_of_inst = #1 oo get_inst_param;

fun inst_thms ctxt =
  Symtab.fold
    (Symtab.fold (cons o #2 o #2) o #2) (#1 (inst_params_of (Proof_Context.theory_of ctxt))) []
  |> map (Thm.transfer' ctxt);

fun get_inst_tyco consts = try (dest_Type_name o the_single o Consts.typargs consts);

fun unoverload ctxt = rewrite_rule ctxt (inst_thms ctxt);
fun overload ctxt = rewrite_rule ctxt (map Thm.symmetric (inst_thms ctxt));

fun unoverload_conv ctxt = Raw_Simplifier.rewrite ctxt true (inst_thms ctxt);
fun overload_conv ctxt = Raw_Simplifier.rewrite ctxt true (map Thm.symmetric (inst_thms ctxt));

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

val classrel_prefix = "classrel_";
val arity_prefix = "arity_";

fun instance_name (a, c) = Long_Name.base_name c ^ "_" ^ Long_Name.base_name a;


(* class relations *)

fun cert_classrel thy raw_rel =
  let
    val string_of_sort = Syntax.string_of_sort_global thy;
    val (c1, c2) = apply2 (Sign.certify_class thy) raw_rel;
    val _ = Sign.primitive_classrel (c1, c2) thy;
    val _ =
      (case subtract (op =) (all_params_of thy [c1]) (all_params_of thy [c2]) of
        [] => ()
      | xs => raise TYPE ("Class " ^ string_of_sort [c1] ^ " lacks parameter(s) " ^
          commas_quote xs ^ " of " ^ string_of_sort [c2], [], []));
  in (c1, c2) end;

fun read_classrel thy raw_rel =
  cert_classrel thy (apply2 (Proof_Context.read_class (Proof_Context.init_global thy)) raw_rel)
    handle TYPE (msg, _, _) => error msg;


(* declaration and definition of instances of overloaded constants *)

fun inst_tyco_of thy (c, T) =
  get_inst_tyco (Sign.consts_of thy) (c, T)
  |> \<^if_none>\<open>
    error ("Illegal type for instantiation of class parameter: " ^
      quote (c ^ " :: " ^ Syntax.string_of_typ_global thy T))\<close>;

fun declare_overloaded (c, T) thy =
  let
    val class = class_of_param thy c |> \<^if_none>\<open>error ("Not a class parameter: " ^ quote c)\<close>;
    val tyco = inst_tyco_of thy (c, T);
    val name_inst = instance_name (tyco, class) ^ "_inst";
    val c' = instance_name (tyco, c);
    val T' = Term.strip_sortsT T;
  in
    thy
    |> Sign.qualified_path true (Binding.name name_inst)
    |> Sign.declare_const_global ((Binding.name c', T'), NoSyn)
    |-> (fn const' as Const (c'', _) =>
      Thm.add_def_global false true
        (Binding.name (Thm.def_name c'), Logic.mk_equals (Const (c, T'), const'))
      #>> apsnd Thm.varifyT_global
      #-> (fn (_, thm) => add_inst_param (c, tyco) (c'', thm)
        #> Global_Theory.add_thm ((Binding.concealed (Binding.name c'), thm), [])
        #> #2
        #> pair (Const (c, T))))
    ||> Sign.restore_naming thy
  end;

fun define_overloaded b (c, t) thy =
  let
    val T = Term.fastype_of t;
    val tyco = inst_tyco_of thy (c, T);
    val (c', eq) = get_inst_param thy (c, tyco);
    val prop = Logic.mk_equals (Const (c', T), t);
    val b' = Thm.def_binding_optional (Binding.name (instance_name (tyco, c))) b;
  in
    thy
    |> Thm.add_def_global false false (b', prop)
    |>> (fn (_, thm) => Drule.transitive_thm OF [eq, thm])
  end;


(* primitive rules *)

fun add_classrel raw_th thy =
  let
    val th = Thm.strip_shyps (Thm.transfer thy raw_th);
    val prop = Thm.plain_prop_of th;
    fun err () = raise THM ("add_classrel: malformed class relation", 0, [th]);
    val rel = Logic.dest_classrel prop handle TERM _ => err ();
    val (c1, c2) = cert_classrel thy rel handle TYPE _ => err ();
    val binding =
      Binding.concealed (Binding.name (prefix classrel_prefix (Logic.name_classrel (c1, c2))));
  in thy |> Global_Theory.store_thm (binding, th) |-> Thm.add_classrel end;

fun add_arity raw_th thy =
  let
    val th = Thm.strip_shyps (Thm.transfer thy raw_th);
    val prop = Thm.plain_prop_of th;
    fun err () = raise THM ("add_arity: malformed type arity", 0, [th]);
    val arity as (t, Ss, c) = Logic.dest_arity prop handle TERM _ => err ();

    val binding =
      Binding.concealed (Binding.name (prefix arity_prefix (Logic.name_arity arity)));

    val args = Name.invent_names Name.context Name.aT Ss;
    val missing_params =
      Sign.complete_sort thy [c]
      |> maps (these o Option.map #params o try (get_info thy))
      |> filter_out (fn (const, _) => can (get_inst_param thy) (const, t))
      |> (map o apsnd o map_atyps) (K (Type (t, map TFree args)));
  in
    thy
    |> Global_Theory.store_thm (binding, th)
    |-> Thm.add_arity
    |> fold (#2 oo declare_overloaded) missing_params
  end;


(* tactical proofs *)

fun prove_classrel raw_rel tac thy =
  let
    val ctxt = Proof_Context.init_global thy;
    val (c1, c2) = cert_classrel thy raw_rel;
    val th =
      Goal.prove ctxt [] [] (Logic.mk_classrel (c1, c2)) (fn {context, ...} => tac context)
        handle ERROR msg =>
          cat_error msg ("The error(s) above occurred while trying to prove class relation " ^
            quote (Syntax.string_of_classrel ctxt [c1, c2]));
  in
    thy |> add_classrel th
  end;

fun prove_arity raw_arity tac thy =
  let
    val ctxt = Proof_Context.init_global thy;
    val arity = Proof_Context.cert_arity ctxt raw_arity;
    val props = Logic.mk_arities arity;
    val ths =
      Goal.prove_common ctxt NONE [] [] props
      (fn {context, ...} => Goal.precise_conjunction_tac (length props) 1 THEN tac context)
        handle ERROR msg =>
          cat_error msg ("The error(s) above occurred while trying to prove type arity " ^
            quote (Syntax.string_of_arity ctxt arity));
  in
    thy |> fold add_arity ths
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
    val ctxt = Syntax.init_pretty_global thy;


    (* class *)

    val bconst = Binding.map_name Logic.const_of_class bclass;
    val class = Sign.full_name thy bclass;
    val super = Sign.minimize_sort thy (Sign.certify_sort thy raw_super);

    fun check_constraint (a, S) =
      if Sign.subsort thy (super, S) then ()
      else error ("Sort constraint of type variable " ^
        Syntax.string_of_typ (Config.put show_sorts true ctxt) (TFree (a, S)) ^
        " needs to be weaker than " ^ Syntax.string_of_sort ctxt super);


    (* params *)

    val params = raw_params |> map (fn p =>
      let
        val T = Sign.the_const_type thy p;
        val _ =
          (case Term.add_tvarsT T [] of
            [((a, _), S)] => check_constraint (a, S)
          | _ => error ("Exactly one type variable expected in class parameter " ^ quote p));
        val T' = Term.map_type_tvar (K (Term.aT [class])) T;
      in (p, T') end);


    (* axioms *)

    fun prep_axiom t =
      (case Term.add_tfrees t [] of
        [(a, S)] => check_constraint (a, S)
      | [] => ()
      | _ => error ("Multiple type variables in class axiom:\n" ^ Syntax.string_of_term ctxt t);
      t
      |> (Term.map_types o Term.map_atyps_same) (fn TFree _ => Term.aT [] | _ => raise Same.SAME)
      |> Logic.close_form);

    val axiomss = map (map (prep_axiom o Sign.cert_prop thy) o snd) raw_specs;
    val name_atts = map fst raw_specs;


    (* definition *)

    val conjs = Logic.mk_of_sort (Term.aT [], super) @ flat axiomss;
    val class_eq =
      Logic.mk_equals (Logic.mk_of_class (Term.aT [], class), Logic.mk_conjunction_balanced conjs);

    val (def, def_thy) =
      thy
      |> Sign.primitive_class (bclass, super)
      |> Global_Theory.add_def (Thm.def_binding bconst, class_eq);
    val (raw_intro, (raw_classrel, raw_axioms)) =
      split_defined (length conjs) def ||> chop (length super);


    (* facts *)

    val class_triv = Thm.class_triv def_thy class;
    val ([(_, [intro]), (_, classrel), (_, axioms)], facts_thy) =
      def_thy
      |> Sign.qualified_path true bconst
      |> Global_Theory.note_thmss ""
        [((Binding.name "intro", []), [([Drule.export_without_context raw_intro], [])]),
         ((Binding.name "super", []), [(map Drule.export_without_context raw_classrel, [])]),
         ((Binding.name "axioms", []),
           [(map (fn th => Drule.export_without_context (class_triv RS th)) raw_axioms, [])])]
      ||> Sign.restore_naming def_thy;


    (* result *)

    val axclass =
      make_axclass
        (Thm.trim_context def, Thm.trim_context intro, map Thm.trim_context axioms, params);

    val result_thy =
      facts_thy
      |> fold (fn th => Thm.add_classrel (class_triv RS th)) classrel
      |> Sign.qualified_path false bconst
      |> Global_Theory.note_thmss "" (name_atts ~~ map Thm.simple_fact (unflat axiomss axioms))
      |> #2
      |> Sign.restore_naming facts_thy
      |> map_axclasses (Symtab.update (class, axclass))
      |> map_params (fold (fn (x, _) => add_param ctxt (x, class)) params);

  in (class, result_thy) end;



(** axiomatizations **)

local

(*old-style axioms*)
fun add_axioms prep mk name add raw_args thy =
  let
    val args = prep thy raw_args;
    val specs = mk args;
    val names = name args;
  in
    thy
    |> fold_map Thm.add_axiom_global (map Binding.name names ~~ specs)
    |-> fold (add o Drule.export_without_context o snd)
  end;

fun class_const_dep c =
  ((Defs.Const, Logic.const_of_class c), [Term.aT []]);

in

val classrel_axiomatization =
  add_axioms (map o cert_classrel) (map Logic.mk_classrel)
    (map (prefix classrel_prefix o Logic.name_classrel)) add_classrel;

val arity_axiomatization =
  add_axioms (Proof_Context.cert_arity o Proof_Context.init_global) Logic.mk_arities
    (map (prefix arity_prefix) o Logic.name_arities) add_arity;

fun class_axiomatization (bclass, raw_super) thy =
  let
    val class = Sign.full_name thy bclass;
    val super = map (Sign.certify_class thy) raw_super |> Sign.minimize_sort thy;
  in
    thy
    |> Sign.primitive_class (bclass, super)
    |> classrel_axiomatization (map (fn c => (class, c)) super)
    |> Theory.add_deps_global "" (class_const_dep class) (map class_const_dep super)
  end;

end;

end;
