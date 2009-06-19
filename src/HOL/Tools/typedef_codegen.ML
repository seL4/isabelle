(*  Title:      HOL/Tools/typedef_codegen.ML
    Author:     Stefan Berghofer, TU Muenchen

Code generators for trivial typedefs.
*)

signature TYPEDEF_CODEGEN =
sig
  val setup: theory -> theory
end;

structure TypedefCodegen: TYPEDEF_CODEGEN =
struct

fun typedef_codegen thy defs dep module brack t gr =
  let
    fun get_name (Type (tname, _)) = tname
      | get_name _ = "";
    fun mk_fun s T ts =
      let
        val (_, gr') = Codegen.invoke_tycodegen thy defs dep module false T gr;
        val (ps, gr'') =
          fold_map (Codegen.invoke_codegen thy defs dep module true) ts gr';
        val id = Codegen.mk_qual_id module (Codegen.get_const_id gr'' s)
      in SOME (Codegen.mk_app brack (Codegen.str id) ps, gr'') end;
    fun lookup f T =
      (case Typedef.get_info thy (get_name T) of
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

fun mk_tyexpr [] s = Codegen.str s
  | mk_tyexpr [p] s = Pretty.block [p, Codegen.str (" " ^ s)]
  | mk_tyexpr ps s = Pretty.list "(" (") " ^ s) ps;

fun typedef_tycodegen thy defs dep module brack (Type (s, Ts)) gr =
      (case Typedef.get_info thy s of
         NONE => NONE
       | SOME {abs_type as newT as Type (tname, Us), rep_type = oldT, Abs_name, Rep_name, ...} =>
           if is_some (Codegen.get_assoc_type thy tname) then NONE else
           let
             val module' = Codegen.if_library
               (Codegen.thyname_of_type thy tname) module;
             val node_id = tname ^ " (type)";
             val ((((qs, (_, Abs_id)), (_, Rep_id)), ty_id), gr') = gr |> fold_map
                 (Codegen.invoke_tycodegen thy defs dep module (length Ts = 1))
                   Ts ||>>
               Codegen.mk_const_id module' Abs_name ||>>
               Codegen.mk_const_id module' Rep_name ||>>
               Codegen.mk_type_id module' s;
             val tyexpr = mk_tyexpr qs (Codegen.mk_qual_id module ty_id)
           in SOME (tyexpr, case try (Codegen.get_node gr') node_id of
               NONE =>
               let
                 val (p :: ps, gr'') = fold_map
                   (Codegen.invoke_tycodegen thy defs node_id module' false)
                   (oldT :: Us) (Codegen.add_edge (node_id, dep)
                      (Codegen.new_node (node_id, (NONE, "", "")) gr'));
                 val s =
                   Codegen.string_of (Pretty.block [Codegen.str "datatype ",
                     mk_tyexpr ps (snd ty_id),
                     Codegen.str " =", Pretty.brk 1, Codegen.str (Abs_id ^ " of"),
                     Pretty.brk 1, p, Codegen.str ";"]) ^ "\n\n" ^
                   Codegen.string_of (Pretty.block [Codegen.str ("fun " ^ Rep_id),
                     Pretty.brk 1, Codegen.str ("(" ^ Abs_id), Pretty.brk 1,
                     Codegen.str "x) = x;"]) ^ "\n\n" ^
                   (if "term_of" mem !Codegen.mode then
                      Codegen.string_of (Pretty.block [Codegen.str "fun ",
                        Codegen.mk_term_of gr'' module' false newT, Pretty.brk 1,
                        Codegen.str ("(" ^ Abs_id), Pretty.brk 1,
                        Codegen.str "x) =", Pretty.brk 1,
                        Pretty.block [Codegen.str ("Const (\"" ^ Abs_name ^ "\","),
                          Pretty.brk 1, Codegen.mk_type false (oldT --> newT),
                          Codegen.str ")"], Codegen.str " $", Pretty.brk 1,
                        Codegen.mk_term_of gr'' module' false oldT, Pretty.brk 1,
                        Codegen.str "x;"]) ^ "\n\n"
                    else "") ^
                   (if "test" mem !Codegen.mode then
                      Codegen.string_of (Pretty.block [Codegen.str "fun ",
                        Codegen.mk_gen gr'' module' false [] "" newT, Pretty.brk 1,
                        Codegen.str "i =", Pretty.brk 1,
                        Pretty.block [Codegen.str (Abs_id ^ " ("),
                          Codegen.mk_gen gr'' module' false [] "" oldT, Pretty.brk 1,
                          Codegen.str "i);"]]) ^ "\n\n"
                    else "")
               in Codegen.map_node node_id (K (NONE, module', s)) gr'' end
             | SOME _ => Codegen.add_edge (node_id, dep) gr')
           end)
  | typedef_tycodegen thy defs dep module brack _ gr = NONE;

val setup =
  Codegen.add_codegen "typedef" typedef_codegen
  #> Codegen.add_tycodegen "typedef" typedef_tycodegen

end;
