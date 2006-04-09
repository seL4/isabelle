(*  Title:      HOL/Tools/typedef_package.ML
    ID:         $Id$
    Author:     Markus Wenzel and Stefan Berghofer, TU Muenchen

Gordon/HOL-style type definitions.
*)

signature TYPEDEF_PACKAGE =
sig
  val quiet_mode: bool ref
  val add_typedecls: (bstring * string list * mixfix) list -> theory -> theory
  val add_typedef: bool -> string option -> bstring * string list * mixfix ->
    string -> (bstring * bstring) option -> tactic -> theory ->
    {type_definition: thm, set_def: thm option, Rep: thm, Rep_inverse: thm,
      Abs_inverse: thm, Rep_inject: thm, Abs_inject: thm, Rep_cases: thm, Abs_cases: thm,
      Rep_induct: thm, Abs_induct: thm} * theory
  val add_typedef_i: bool -> string option -> bstring * string list * mixfix ->
    term -> (bstring * bstring) option -> tactic -> theory ->
    {type_definition: thm, set_def: thm option, Rep: thm, Rep_inverse: thm,
      Abs_inverse: thm, Rep_inject: thm, Abs_inject: thm, Rep_cases: thm, Abs_cases: thm,
      Rep_induct: thm, Abs_induct: thm} * theory
  val typedef: (bool * string) * (bstring * string list * mixfix) * string
    * (string * string) option -> theory -> Proof.state
  val typedef_i: (bool * string) * (bstring * string list * mixfix) * term
    * (string * string) option -> theory -> Proof.state
  val setup: theory -> theory
  structure TypedefData : THEORY_DATA
end;

structure TypedefPackage: TYPEDEF_PACKAGE =
struct


(** theory context references **)

val type_definitionN = "Typedef.type_definition";

val Rep = thm "type_definition.Rep";
val Rep_inverse = thm "type_definition.Rep_inverse";
val Abs_inverse = thm "type_definition.Abs_inverse";
val Rep_inject = thm "type_definition.Rep_inject";
val Abs_inject = thm "type_definition.Abs_inject";
val Rep_cases = thm "type_definition.Rep_cases";
val Abs_cases = thm "type_definition.Abs_cases";
val Rep_induct = thm "type_definition.Rep_induct";
val Abs_induct = thm "type_definition.Abs_induct";



(** type declarations **)

fun add_typedecls decls thy =
  let
    fun arity_of (raw_name, args, mx) =
      (Sign.full_name thy (Syntax.type_name raw_name mx),
        replicate (length args) HOLogic.typeS, HOLogic.typeS);
  in
    thy
    |> Theory.add_typedecls decls
    |> can (Theory.assert_super HOL.thy) ? Theory.add_arities_i (map arity_of decls)
  end;



(** type definitions **)

(* messages *)

val quiet_mode = ref false;
fun message s = if ! quiet_mode then () else writeln s;


(* theory data *)

structure TypedefData = TheoryDataFun
(struct
  val name = "HOL/typedef";
  type T = ((typ * typ * string * string) * (thm option * thm * thm)) Symtab.table;
  val empty = Symtab.empty;
  val copy = I;
  val extend = I;
  fun merge _ (tabs: T * T) = Symtab.merge (op =) tabs;
  fun print _ _ = ();
end);

fun put_typedef newT oldT Abs_name Rep_name def inject inverse =
  TypedefData.map (Symtab.update_new (fst (dest_Type newT),
    ((newT, oldT, Abs_name, Rep_name), (def, inject, inverse))));


(* prepare_typedef *)

fun read_term thy used s =
  #1 (Thm.read_def_cterm (thy, K NONE, K NONE) used true (s, HOLogic.typeT));

fun cert_term thy _ t = Thm.cterm_of thy t handle TERM (msg, _) => error msg;

fun err_in_typedef msg name =
  cat_error msg ("The error(s) above occurred in typedef " ^ quote name);

fun prepare_typedef prep_term def name (t, vs, mx) raw_set opt_morphs thy =
  let
    val _ = Theory.requires thy "Typedef" "typedefs";
    val full = Sign.full_name thy;

    (*rhs*)
    val full_name = full name;
    val cset = prep_term thy vs raw_set;
    val {T = setT, t = set, ...} = Thm.rep_cterm cset;
    val rhs_tfrees = Term.add_tfrees set [];
    val rhs_tfreesT = Term.add_tfreesT setT [];
    val oldT = HOLogic.dest_setT setT handle TYPE _ =>
      error ("Not a set type: " ^ quote (Sign.string_of_typ thy setT));
    fun mk_nonempty A =
      HOLogic.mk_Trueprop (HOLogic.mk_exists ("x", oldT, HOLogic.mk_mem (Free ("x", oldT), A)));
    val goal = mk_nonempty set;
    val goal_pat = mk_nonempty (Var (if_none (Syntax.read_variable name) (name, 0), setT));

    (*lhs*)
    val defS = Sign.defaultS thy;
    val lhs_tfrees = map (fn v => (v, if_none (AList.lookup (op =) rhs_tfrees v) defS)) vs;
    val args_setT = lhs_tfrees
      |> filter (member (op =) rhs_tfrees andf (not o member (op =) rhs_tfreesT))
      |> map TFree;

    val tname = Syntax.type_name t mx;
    val full_tname = full tname;
    val newT = Type (full_tname, map TFree lhs_tfrees);

    val (Rep_name, Abs_name) = if_none opt_morphs ("Rep_" ^ name, "Abs_" ^ name);
    val setT' = map Term.itselfT args_setT ---> setT;
    val setC = Term.list_comb (Const (full_name, setT'), map Logic.mk_type args_setT);
    val RepC = Const (full Rep_name, newT --> oldT);
    val AbsC = Const (full Abs_name, oldT --> newT);
    val x_new = Free ("x", newT);
    val y_old = Free ("y", oldT);

    val set' = if def then setC else set;

    val typedef_name = "type_definition_" ^ name;
    val typedefC =
      Const (type_definitionN, (newT --> oldT) --> (oldT --> newT) --> setT --> HOLogic.boolT);
    val typedef_prop =
      Logic.mk_implies (goal, HOLogic.mk_Trueprop (typedefC $ RepC $ AbsC $ set'));

    fun add_def def def' thy =
      if def
      then
        thy
        |> PureThy.add_defs_i false [Thm.no_attributes def']
        |-> (fn [def'] => pair (SOME def'))
      else
        (NONE, thy);

    fun typedef_result nonempty context =
      Context.the_theory context
      |> add_typedecls [(t, vs, mx)]
      |> Theory.add_consts_i
       ((if def then [(name, setT', NoSyn)] else []) @
        [(Rep_name, newT --> oldT, NoSyn),
         (Abs_name, oldT --> newT, NoSyn)])
      |> add_def def (Logic.mk_defpair (setC, set))
      ||>> PureThy.add_axioms_i [((typedef_name, typedef_prop),
          [apsnd (fn cond_axm => Drule.standard (nonempty RS cond_axm))])]
      ||> Theory.add_finals_i false [RepC, AbsC]
      |-> (fn (set_def, [type_definition]) => fn theory' =>
        let
          fun make th = Drule.standard (th OF [type_definition]);
          val abs_inject = make Abs_inject;
          val abs_inverse = make Abs_inverse;
          val ([Rep, Rep_inverse, Abs_inverse, Rep_inject, Abs_inject,
              Rep_cases, Abs_cases, Rep_induct, Abs_induct], theory'') =
            theory'
            |> Theory.add_path name
            |> PureThy.add_thms
              ([((Rep_name, make Rep), []),
                ((Rep_name ^ "_inverse", make Rep_inverse), []),
                ((Abs_name ^ "_inverse", abs_inverse), []),
                ((Rep_name ^ "_inject", make Rep_inject), []),
                ((Abs_name ^ "_inject", abs_inject), []),
                ((Rep_name ^ "_cases", make Rep_cases),
                  [RuleCases.case_names [Rep_name], InductAttrib.cases_set full_name]),
                ((Abs_name ^ "_cases", make Abs_cases),
                  [RuleCases.case_names [Abs_name], InductAttrib.cases_type full_tname]),
                ((Rep_name ^ "_induct", make Rep_induct),
                  [RuleCases.case_names [Rep_name], InductAttrib.induct_set full_name]),
                ((Abs_name ^ "_induct", make Abs_induct),
                  [RuleCases.case_names [Abs_name], InductAttrib.induct_type full_tname])])
            ||> Theory.parent_path
            ||> put_typedef newT oldT (full Abs_name) (full Rep_name)
                 set_def abs_inject abs_inverse
          val result = {type_definition = type_definition, set_def = set_def,
            Rep = Rep, Rep_inverse = Rep_inverse, Abs_inverse = Abs_inverse,
            Rep_inject = Rep_inject, Abs_inject = Abs_inject, Rep_cases = Rep_cases,
            Abs_cases = Abs_cases, Rep_induct = Rep_induct, Abs_induct = Abs_induct};
        in ((type_definition, result), Context.Theory theory'') end);


    (* errors *)

    fun show_names pairs = commas_quote (map fst pairs);

    val illegal_vars =
      if null (term_vars set) andalso null (term_tvars set) then []
      else ["Illegal schematic variable(s) on rhs"];

    val dup_lhs_tfrees =
      (case duplicates (op =) lhs_tfrees of [] => []
      | dups => ["Duplicate type variables on lhs: " ^ show_names dups]);

    val extra_rhs_tfrees =
      (case fold (remove (op =)) lhs_tfrees rhs_tfrees of [] => []
      | extras => ["Extra type variables on rhs: " ^ show_names extras]);

    val illegal_frees =
      (case term_frees set of [] => []
      | xs => ["Illegal variables on rhs: " ^ show_names (map dest_Free xs)]);

    val errs = illegal_vars @ dup_lhs_tfrees @ extra_rhs_tfrees @ illegal_frees;
    val _ = if null errs then () else error (cat_lines errs);

    (*test theory errors now!*)
    val test_thy = Theory.copy thy;
    val _ = 
      Context.Theory test_thy
      |> typedef_result (setmp quick_and_dirty true (SkipProof.make_thm test_thy) goal);

  in (cset, goal, goal_pat, typedef_result) end
  handle ERROR msg => err_in_typedef msg name;


(* add_typedef interfaces *)

local

fun gen_typedef prep_term def opt_name typ set opt_morphs tac thy =
  let
    val name = the_default (#1 typ) opt_name;
    val (cset, goal, _, typedef_result) =
      prepare_typedef prep_term def name typ set opt_morphs thy;
    val _ = message ("Proving non-emptiness of set " ^ quote (string_of_cterm cset) ^ " ...");
    val non_empty = Goal.prove thy [] [] goal (K tac) handle ERROR msg =>
      cat_error msg ("Failed to prove non-emptiness of " ^ quote (string_of_cterm cset));
  in
    Context.Theory thy
    |> typedef_result non_empty
    ||> Context.the_theory
    |-> (fn (_, result) => pair result)
  end;

in

val add_typedef = gen_typedef read_term;
val add_typedef_i = gen_typedef cert_term;

end;


(* Isar typedef interface *)

local

fun gen_typedef prep_term ((def, name), typ, set, opt_morphs) thy =
  let
    val (_, goal, goal_pat, att_result) =
      prepare_typedef prep_term def name typ set opt_morphs thy;
    fun att (thy, th) =
      let val ((th', _), thy') = att_result th thy
      in (thy', th') end;
  in IsarThy.theorem_i PureThy.internalK ("", [att]) (goal, ([goal_pat], [])) thy end;

in

val typedef = gen_typedef read_term;
val typedef_i = gen_typedef cert_term;

end;



(** trivial code generator **)

fun typedef_codegen thy defs gr dep module brack t =
  let
    fun get_name (Type (tname, _)) = tname
      | get_name _ = "";
    fun mk_fun s T ts =
      let
        val (gr', _) = Codegen.invoke_tycodegen thy defs dep module false (gr, T);
        val (gr'', ps) =
          foldl_map (Codegen.invoke_codegen thy defs dep module true) (gr', ts);
        val id = Codegen.mk_qual_id module (Codegen.get_const_id s gr'')
      in SOME (gr'', Codegen.mk_app brack (Pretty.str id) ps) end;
    fun lookup f T =
      (case Symtab.lookup (TypedefData.get thy) (get_name T) of
        NONE => ""
      | SOME (s, _) => f s);
  in
    (case strip_comb t of
       (Const (s, Type ("fun", [T, U])), ts) =>
         if lookup #4 T = s andalso
           is_none (Codegen.get_assoc_type thy (get_name T))
         then mk_fun s T ts
         else if lookup #3 U = s andalso
           is_none (Codegen.get_assoc_type thy (get_name U))
         then mk_fun s U ts
         else NONE
     | _ => NONE)
  end;

fun mk_tyexpr [] s = Pretty.str s
  | mk_tyexpr [p] s = Pretty.block [p, Pretty.str (" " ^ s)]
  | mk_tyexpr ps s = Pretty.list "(" (") " ^ s) ps;

fun typedef_tycodegen thy defs gr dep module brack (Type (s, Ts)) =
      (case Symtab.lookup (TypedefData.get thy) s of
         NONE => NONE
       | SOME ((newT as Type (tname, Us), oldT, Abs_name, Rep_name), _) =>
           if is_some (Codegen.get_assoc_type thy tname) then NONE else
           let
             val module' = Codegen.if_library
               (Codegen.thyname_of_type tname thy) module;
             val node_id = tname ^ " (type)";
             val (gr', (((qs, (_, Abs_id)), (_, Rep_id)), ty_id)) = foldl_map
                 (Codegen.invoke_tycodegen thy defs dep module (length Ts = 1))
                   (gr, Ts) |>>>
               Codegen.mk_const_id module' Abs_name |>>>
               Codegen.mk_const_id module' Rep_name |>>>
               Codegen.mk_type_id module' s;
             val tyexpr = mk_tyexpr qs (Codegen.mk_qual_id module ty_id)
           in SOME (case try (Codegen.get_node gr') node_id of
               NONE =>
               let
                 val (gr'', p :: ps) = foldl_map
                   (Codegen.invoke_tycodegen thy defs node_id module' false)
                   (Codegen.add_edge (node_id, dep)
                      (Codegen.new_node (node_id, (NONE, "", "")) gr'), oldT :: Us);
                 val s =
                   Pretty.string_of (Pretty.block [Pretty.str "datatype ",
                     mk_tyexpr ps (snd ty_id),
                     Pretty.str " =", Pretty.brk 1, Pretty.str (Abs_id ^ " of"),
                     Pretty.brk 1, p, Pretty.str ";"]) ^ "\n\n" ^
                   Pretty.string_of (Pretty.block [Pretty.str ("fun " ^ Rep_id),
                     Pretty.brk 1, Pretty.str ("(" ^ Abs_id), Pretty.brk 1,
                     Pretty.str "x) = x;"]) ^ "\n\n" ^
                   (if "term_of" mem !Codegen.mode then
                      Pretty.string_of (Pretty.block [Pretty.str "fun ",
                        Codegen.mk_term_of gr'' module' false newT, Pretty.brk 1,
                        Pretty.str ("(" ^ Abs_id), Pretty.brk 1,
                        Pretty.str "x) =", Pretty.brk 1,
                        Pretty.block [Pretty.str ("Const (\"" ^ Abs_name ^ "\","),
                          Pretty.brk 1, Codegen.mk_type false (oldT --> newT),
                          Pretty.str ")"], Pretty.str " $", Pretty.brk 1,
                        Codegen.mk_term_of gr'' module' false oldT, Pretty.brk 1,
                        Pretty.str "x;"]) ^ "\n\n"
                    else "") ^
                   (if "test" mem !Codegen.mode then
                      Pretty.string_of (Pretty.block [Pretty.str "fun ",
                        Codegen.mk_gen gr'' module' false [] "" newT, Pretty.brk 1,
                        Pretty.str "i =", Pretty.brk 1,
                        Pretty.block [Pretty.str (Abs_id ^ " ("),
                          Codegen.mk_gen gr'' module' false [] "" oldT, Pretty.brk 1,
                          Pretty.str "i);"]]) ^ "\n\n"
                    else "")
               in Codegen.map_node node_id (K (NONE, module', s)) gr'' end
             | SOME _ => Codegen.add_edge (node_id, dep) gr', tyexpr)
           end)
  | typedef_tycodegen thy defs gr dep module brack _ = NONE;

fun typedef_type_extr thy tyco =
  case Symtab.lookup (TypedefData.get thy) tyco
   of SOME ((ty_abs, ty_rep, c_abs, c_rep), (SOME def, inject, _)) =>
        let
          val exists_thm =
            UNIV_I
            |> Drule.instantiate' [SOME (ctyp_of thy ty_rep)] []
            |> rewrite_rule [symmetric def];
        in case try (Tactic.rule_by_tactic ((ALLGOALS o resolve_tac) [exists_thm])) inject
         of SOME eq_thm => SOME (((Term.typ_tfrees o Type.no_tvars) ty_abs, [(c_abs, [ty_rep])]),
             (ALLGOALS o resolve_tac) [eq_reflection]
            THEN (ALLGOALS o resolve_tac) [eq_thm])
          | NONE => NONE
        end
    | _ => NONE;

fun typedef_fun_extr thy (c, ty) =
  case (fst o strip_type) ty
   of Type (tyco, _) :: _ =>
    (case Symtab.lookup (TypedefData.get thy) tyco
     of SOME ((ty_abs, ty_rep, c_abs, c_rep), (SOME def, _, inverse)) =>
          if c = c_rep then
            let
              val exists_thm =
                UNIV_I
                |> Drule.instantiate' [SOME (ctyp_of thy ty_rep)] []
                |> rewrite_rule [symmetric def]
            in case try (Tactic.rule_by_tactic ((ALLGOALS o resolve_tac) [exists_thm])) inverse
             of SOME eq_thm => SOME [eq_thm]
              | NONE => NONE
            end
          else NONE
      | _ => NONE)
    | _ => NONE;

val setup =
  TypedefData.init
  #> Codegen.add_codegen "typedef" typedef_codegen
  #> Codegen.add_tycodegen "typedef" typedef_tycodegen
  #> CodegenTheorems.add_fun_extr (these oo typedef_fun_extr)
  #> CodegenTheorems.add_datatype_extr typedef_type_extr



(** outer syntax **)

local structure P = OuterParse and K = OuterKeyword in

val typedeclP =
  OuterSyntax.command "typedecl" "type declaration (HOL)" K.thy_decl
    (P.type_args -- P.name -- P.opt_infix >> (fn ((vs, t), mx) =>
      Toplevel.theory (add_typedecls [(t, vs, mx)])));


val typedef_decl =
  Scan.optional (P.$$$ "(" |--
      ((P.$$$ "open" >> K false) -- Scan.option P.name || P.name >> (fn s => (true, SOME s)))
        --| P.$$$ ")") (true, NONE) --
    (P.type_args -- P.name) -- P.opt_infix -- (P.$$$ "=" |-- P.term) --
    Scan.option (P.$$$ "morphisms" |-- P.!!! (P.name -- P.name));

fun mk_typedef ((((((def, opt_name), (vs, t)), mx), A), morphs)) =
  typedef ((def, if_none opt_name (Syntax.type_name t mx)), (t, vs, mx), A, morphs);

val typedefP =
  OuterSyntax.command "typedef" "HOL type definition (requires non-emptiness proof)" K.thy_goal
    (typedef_decl >> (Toplevel.print oo (Toplevel.theory_to_proof o mk_typedef)));


val _ = OuterSyntax.add_keywords ["morphisms"];
val _ = OuterSyntax.add_parsers [typedeclP, typedefP];

end;

end;
