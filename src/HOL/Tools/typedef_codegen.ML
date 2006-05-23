(*  Title:      HOL/Tools/typedef_codegen.ML
    ID:         $Id$
    Author:     Stefan Berghofer and Florian Haftmann, TU Muenchen

Code generators for trivial typedefs.
*)

signature TYPEDEF_CODEGEN =
sig
  val typedef_fun_extr: theory -> string * typ -> thm list option
  val typedef_type_extr: theory -> string
      -> (((string * sort) list * (string * typ list) list) * tactic) option
  val setup: theory -> theory;
end;

structure TypedefCodegen: TYPEDEF_CODEGEN =
struct

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
      (case TypedefPackage.get_info thy (get_name T) of
        NONE => ""
      | SOME info => f info);
  in
    (case strip_comb t of
       (Const (s, Type ("fun", [T, U])), ts) =>
         if lookup #Rep_name T = s andalso
           is_none (Codegen.get_assoc_type thy (get_name T))
         then mk_fun s T ts
         else if lookup #Abs_name U = s andalso
           is_none (Codegen.get_assoc_type thy (get_name U))
         then mk_fun s U ts
         else NONE
     | _ => NONE)
  end;

fun mk_tyexpr [] s = Pretty.str s
  | mk_tyexpr [p] s = Pretty.block [p, Pretty.str (" " ^ s)]
  | mk_tyexpr ps s = Pretty.list "(" (") " ^ s) ps;

fun typedef_tycodegen thy defs gr dep module brack (Type (s, Ts)) =
      (case TypedefPackage.get_info thy s of
         NONE => NONE
       | SOME {abs_type as newT as Type (tname, Us), rep_type = oldT, Abs_name, Rep_name, ...} =>
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
  case TypedefPackage.get_info thy tyco
   of SOME {abs_type = ty_abs, rep_type = ty_rep, Abs_name = c_abs, Rep_name = c_rep,
     set_def = SOME def, Abs_inject = inject, ...} =>
        let
          val exists_thm =
            UNIV_I
            |> Drule.instantiate' [SOME (ctyp_of thy ty_rep)] []
            |> rewrite_rule [symmetric def];
        in case try (Tactic.rule_by_tactic ((ALLGOALS o match_tac) [exists_thm])) inject
         of SOME eq_thm => SOME (((Term.typ_tfrees o Type.no_tvars) ty_abs, [(c_abs, [ty_rep])]),
             (ALLGOALS o match_tac) [eq_reflection]
            THEN (ALLGOALS o match_tac) [eq_thm])
          | NONE => NONE
        end
    | _ => NONE;

fun typedef_fun_extr thy (c, ty) =
  case (fst o strip_type) ty
   of Type (tyco, _) :: _ =>
    (case TypedefPackage.get_info thy tyco
     of SOME {abs_type = ty_abs, rep_type = ty_rep, Abs_name = c_abs, Rep_name = c_rep,
       set_def = SOME def, Abs_inverse = inverse, ...} =>
          if c = c_rep then
            let
              val exists_thm =
                UNIV_I
                |> Drule.instantiate' [SOME (ctyp_of thy ty_rep)] []
                |> rewrite_rule [symmetric def]
            in case try (Tactic.rule_by_tactic ((ALLGOALS o match_tac) [exists_thm])) inverse
             of SOME eq_thm => SOME [eq_thm]
              | NONE => NONE
            end
          else NONE
      | _ => NONE)
    | _ => NONE;

val setup =
  Codegen.add_codegen "typedef" typedef_codegen
  #> Codegen.add_tycodegen "typedef" typedef_tycodegen
  #> CodegenTheorems.add_fun_extr (these oo typedef_fun_extr)
  #> CodegenTheorems.add_datatype_extr typedef_type_extr

end;
