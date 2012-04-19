(*  Title:      Tools/Code/code_ml.ML
    Author:     Florian Haftmann, TU Muenchen

Serializer for SML and OCaml.
*)

signature CODE_ML =
sig
  val target_SML: string
  val target_OCaml: string
  val setup: theory -> theory
end;

structure Code_ML : CODE_ML =
struct

open Basic_Code_Thingol;
open Code_Printer;

infixr 5 @@;
infixr 5 @|;


(** generic **)

val target_SML = "SML";
val target_OCaml = "OCaml";

datatype ml_binding =
    ML_Function of string * (typscheme * ((iterm list * iterm) * (thm option * bool)) list)
  | ML_Instance of string * ((class * (string * (vname * sort) list))
        * ((class * (string * (string * dict list list))) list
      * (((string * const) * (thm * bool)) list * ((string * const) * (thm * bool)) list)));

datatype ml_stmt =
    ML_Exc of string * (typscheme * int)
  | ML_Val of ml_binding
  | ML_Funs of ml_binding list * string list
  | ML_Datas of (string * ((vname * sort) list * ((string * vname list) * itype list) list)) list
  | ML_Class of string * (vname * ((class * string) list * (string * itype) list));

fun print_product _ [] = NONE
  | print_product print [x] = SOME (print x)
  | print_product print xs = (SOME o enum " *" "" "") (map print xs);

fun tuplify _ _ [] = NONE
  | tuplify print fxy [x] = SOME (print fxy x)
  | tuplify print _ xs = SOME (enum "," "(" ")" (map (print NOBR) xs));


(** SML serializer **)

fun print_sml_stmt tyco_syntax const_syntax reserved is_cons deresolve =
  let
    fun print_tyco_expr (tyco, []) = (str o deresolve) tyco
      | print_tyco_expr (tyco, [ty]) =
          concat [print_typ BR ty, (str o deresolve) tyco]
      | print_tyco_expr (tyco, tys) =
          concat [enum "," "(" ")" (map (print_typ BR) tys), (str o deresolve) tyco]
    and print_typ fxy (tyco `%% tys) = (case tyco_syntax tyco
         of NONE => print_tyco_expr (tyco, tys)
          | SOME (_, print) => print print_typ fxy tys)
      | print_typ fxy (ITyVar v) = str ("'" ^ v);
    fun print_dicttyp (class, ty) = print_tyco_expr (class, [ty]);
    fun print_typscheme_prefix (vs, p) = enum " ->" "" ""
      (map_filter (fn (v, sort) =>
        (print_product (fn class => print_dicttyp (class, ITyVar v)) sort)) vs @| p);
    fun print_typscheme (vs, ty) = print_typscheme_prefix (vs, print_typ NOBR ty);
    fun print_dicttypscheme (vs, class_ty) = print_typscheme_prefix (vs, print_dicttyp class_ty);
    fun print_classrels fxy [] ps = brackify fxy ps
      | print_classrels fxy [classrel] ps = brackify fxy [(str o deresolve) classrel, brackify BR ps]
      | print_classrels fxy classrels ps =
          brackify fxy [enum " o" "(" ")" (map (str o deresolve) classrels), brackify BR ps]
    fun print_dict is_pseudo_fun fxy (Dict (classrels, x)) =
      print_classrels fxy classrels (print_plain_dict is_pseudo_fun fxy x)
    and print_plain_dict is_pseudo_fun fxy (Dict_Const (inst, dss)) =
          ((str o deresolve) inst ::
            (if is_pseudo_fun inst then [str "()"]
            else map_filter (print_dicts is_pseudo_fun BR) dss))
      | print_plain_dict is_pseudo_fun fxy (Dict_Var (v, (i, k))) =
          [str (if k = 1 then first_upper v ^ "_"
            else first_upper v ^ string_of_int (i+1) ^ "_")]
    and print_dicts is_pseudo_fun = tuplify (print_dict is_pseudo_fun);
    val print_dict_args = map_filter (fn (v, sort) => print_dicts (K false) BR
      (map_index (fn (i, _) => Dict ([], Dict_Var (v, (i, length sort)))) sort));
    fun print_term is_pseudo_fun some_thm vars fxy (IConst c) =
          print_app is_pseudo_fun some_thm vars fxy (c, [])
      | print_term is_pseudo_fun some_thm vars fxy (IVar NONE) =
          str "_"
      | print_term is_pseudo_fun some_thm vars fxy (IVar (SOME v)) =
          str (lookup_var vars v)
      | print_term is_pseudo_fun some_thm vars fxy (t as t1 `$ t2) =
          (case Code_Thingol.unfold_const_app t
           of SOME c_ts => print_app is_pseudo_fun some_thm vars fxy c_ts
            | NONE => brackify fxy [print_term is_pseudo_fun some_thm vars NOBR t1,
                print_term is_pseudo_fun some_thm vars BR t2])
      | print_term is_pseudo_fun some_thm vars fxy (t as _ `|=> _) =
          let
            val (binds, t') = Code_Thingol.unfold_pat_abs t;
            fun print_abs (pat, ty) =
              print_bind is_pseudo_fun some_thm NOBR pat
              #>> (fn p => concat [str "fn", p, str "=>"]);
            val (ps, vars') = fold_map print_abs binds vars;
          in brackets (ps @ [print_term is_pseudo_fun some_thm vars' NOBR t']) end
      | print_term is_pseudo_fun some_thm vars fxy (ICase (cases as (_, t0))) =
          (case Code_Thingol.unfold_const_app t0
           of SOME (c_ts as ((c, _), _)) => if is_none (const_syntax c)
                then print_case is_pseudo_fun some_thm vars fxy cases
                else print_app is_pseudo_fun some_thm vars fxy c_ts
            | NONE => print_case is_pseudo_fun some_thm vars fxy cases)
    and print_app_expr is_pseudo_fun some_thm vars (app as ((c, (((_, iss), (arg_tys, _)), _)), ts)) =
      if is_cons c then
        let val k = length arg_tys in
          if k < 2 orelse length ts = k
          then (str o deresolve) c
            :: the_list (tuplify (print_term is_pseudo_fun some_thm vars) BR ts)
          else [print_term is_pseudo_fun some_thm vars BR (Code_Thingol.eta_expand k app)]
        end
      else if is_pseudo_fun c
        then (str o deresolve) c @@ str "()"
      else (str o deresolve) c :: map_filter (print_dicts is_pseudo_fun BR) iss
        @ map (print_term is_pseudo_fun some_thm vars BR) ts
    and print_app is_pseudo_fun some_thm vars = gen_print_app (print_app_expr is_pseudo_fun)
      (print_term is_pseudo_fun) const_syntax some_thm vars
    and print_bind is_pseudo_fun = gen_print_bind (print_term is_pseudo_fun)
    and print_case is_pseudo_fun some_thm vars fxy (cases as ((_, [_]), _)) =
          let
            val (binds, body) = Code_Thingol.unfold_let (ICase cases);
            fun print_match ((pat, _), t) vars =
              vars
              |> print_bind is_pseudo_fun some_thm NOBR pat
              |>> (fn p => semicolon [str "val", p, str "=",
                    print_term is_pseudo_fun some_thm vars NOBR t])
            val (ps, vars') = fold_map print_match binds vars;
          in
            Pretty.chunks [
              Pretty.block [str "let", Pretty.fbrk, Pretty.chunks ps],
              Pretty.block [str "in", Pretty.fbrk, print_term is_pseudo_fun some_thm vars' NOBR body],
              str "end"
            ]
          end
      | print_case is_pseudo_fun some_thm vars fxy (((t, ty), clause :: clauses), _) =
          let
            fun print_select delim (pat, body) =
              let
                val (p, vars') = print_bind is_pseudo_fun some_thm NOBR pat vars;
              in
                concat [str delim, p, str "=>", print_term is_pseudo_fun some_thm vars' NOBR body]
              end;
          in
            brackets (
              str "case"
              :: print_term is_pseudo_fun some_thm vars NOBR t
              :: print_select "of" clause
              :: map (print_select "|") clauses
            )
          end
      | print_case is_pseudo_fun some_thm vars fxy ((_, []), _) =
          (concat o map str) ["raise", "Fail", "\"empty case\""];
    fun print_val_decl print_typscheme (name, typscheme) = concat
      [str "val", str (deresolve name), str ":", print_typscheme typscheme];
    fun print_datatype_decl definer (tyco, (vs, cos)) =
      let
        fun print_co ((co, _), []) = str (deresolve co)
          | print_co ((co, _), tys) = concat [str (deresolve co), str "of",
              enum " *" "" "" (map (print_typ (INFX (2, X))) tys)];
      in
        concat (
          str definer
          :: print_tyco_expr (tyco, map (ITyVar o fst) vs)
          :: str "="
          :: separate (str "|") (map print_co cos)
        )
      end;
    fun print_def is_pseudo_fun needs_typ definer
          (ML_Function (name, (vs_ty as (vs, ty), eq :: eqs))) =
          let
            fun print_eqn definer ((ts, t), (some_thm, _)) =
              let
                val consts = fold Code_Thingol.add_constnames (t :: ts) [];
                val vars = reserved
                  |> intro_base_names
                       (is_none o const_syntax) deresolve consts
                  |> intro_vars ((fold o Code_Thingol.fold_varnames)
                       (insert (op =)) ts []);
                val prolog = if needs_typ then
                  concat [str definer, (str o deresolve) name, str ":", print_typ NOBR ty]
                    else (concat o map str) [definer, deresolve name];
              in
                concat (
                  prolog
                  :: (if is_pseudo_fun name then [str "()"]
                      else print_dict_args vs
                        @ map (print_term is_pseudo_fun some_thm vars BR) ts)
                  @ str "="
                  @@ print_term is_pseudo_fun some_thm vars NOBR t
                )
              end
            val shift = if null eqs then I else
              map (Pretty.block o single o Pretty.block o single);
          in pair
            (print_val_decl print_typscheme (name, vs_ty))
            ((Pretty.block o Pretty.fbreaks o shift) (
              print_eqn definer eq
              :: map (print_eqn "|") eqs
            ))
          end
      | print_def is_pseudo_fun _ definer
          (ML_Instance (inst, ((class, (tyco, vs)), (super_instances, (classparam_instances, _))))) =
          let
            fun print_super_instance (_, (classrel, x)) =
              concat [
                (str o Long_Name.base_name o deresolve) classrel,
                str "=",
                print_dict is_pseudo_fun NOBR (Dict ([], Dict_Const x))
              ];
            fun print_classparam_instance ((classparam, const), (thm, _)) =
              concat [
                (str o Long_Name.base_name o deresolve) classparam,
                str "=",
                print_app (K false) (SOME thm) reserved NOBR (const, [])
              ];
          in pair
            (print_val_decl print_dicttypscheme
              (inst, (vs, (class, tyco `%% map (ITyVar o fst) vs))))
            (concat (
              str definer
              :: (str o deresolve) inst
              :: (if is_pseudo_fun inst then [str "()"]
                  else print_dict_args vs)
              @ str "="
              :: enum "," "{" "}"
                (map print_super_instance super_instances
                  @ map print_classparam_instance classparam_instances)
              :: str ":"
              @@ print_tyco_expr (class, [tyco `%% map (ITyVar o fst) vs])
            ))
          end;
    fun print_stmt (ML_Exc (name, (vs_ty, n))) = pair
          [print_val_decl print_typscheme (name, vs_ty)]
          ((semicolon o map str) (
            (if n = 0 then "val" else "fun")
            :: deresolve name
            :: replicate n "_"
            @ "="
            :: "raise"
            :: "Fail"
            @@ (ML_Syntax.print_string o Long_Name.base_name o Long_Name.qualifier) name
          ))
      | print_stmt (ML_Val binding) =
          let
            val (sig_p, p) = print_def (K false) true "val" binding
          in pair
            [sig_p]
            (semicolon [p])
          end
      | print_stmt (ML_Funs (binding :: bindings, pseudo_funs)) =
          let
            val print_def' = print_def (member (op =) pseudo_funs) false;
            fun print_pseudo_fun name = concat [
                str "val",
                (str o deresolve) name,
                str "=",
                (str o deresolve) name,
                str "();"
              ];
            val (sig_ps, (ps, p)) = (apsnd split_last o split_list)
              (print_def' "fun" binding :: map (print_def' "and") bindings);
            val pseudo_ps = map print_pseudo_fun pseudo_funs;
          in pair
            sig_ps
            (Pretty.chunks (ps @ semicolon [p] :: pseudo_ps))
          end
     | print_stmt (ML_Datas [(tyco, (vs, []))]) =
          let
            val ty_p = print_tyco_expr (tyco, map (ITyVar o fst) vs);
          in
            pair
            [concat [str "type", ty_p]]
            (concat [str "datatype", ty_p, str "=", str "EMPTY__"])
          end
     | print_stmt (ML_Datas (data :: datas)) = 
          let
            val sig_ps = print_datatype_decl "datatype" data
              :: map (print_datatype_decl "and") datas;
            val (ps, p) = split_last sig_ps;
          in pair
            sig_ps
            (Pretty.chunks (ps @| semicolon [p]))
          end
     | print_stmt (ML_Class (class, (v, (super_classes, classparams)))) =
          let
            fun print_field s p = concat [str s, str ":", p];
            fun print_proj s p = semicolon
              (map str ["val", s, "=", "#" ^ s, ":"] @| p);
            fun print_super_class_decl (super_class, classrel) =
              print_val_decl print_dicttypscheme
                (classrel, ([(v, [class])], (super_class, ITyVar v)));
            fun print_super_class_field (super_class, classrel) =
              print_field (deresolve classrel) (print_dicttyp (super_class, ITyVar v));
            fun print_super_class_proj (super_class, classrel) =
              print_proj (deresolve classrel)
                (print_dicttypscheme ([(v, [class])], (super_class, ITyVar v)));
            fun print_classparam_decl (classparam, ty) =
              print_val_decl print_typscheme
                (classparam, ([(v, [class])], ty));
            fun print_classparam_field (classparam, ty) =
              print_field (deresolve classparam) (print_typ NOBR ty);
            fun print_classparam_proj (classparam, ty) =
              print_proj (deresolve classparam)
                (print_typscheme ([(v, [class])], ty));
          in pair
            (concat [str "type", print_dicttyp (class, ITyVar v)]
              :: map print_super_class_decl super_classes
              @ map print_classparam_decl classparams)
            (Pretty.chunks (
              concat [
                str ("type '" ^ v),
                (str o deresolve) class,
                str "=",
                enum "," "{" "};" (
                  map print_super_class_field super_classes
                  @ map print_classparam_field classparams
                )
              ]
              :: map print_super_class_proj super_classes
              @ map print_classparam_proj classparams
            ))
          end;
  in print_stmt end;

fun print_sml_module name some_decls body =
  Pretty.chunks2 (
    Pretty.chunks (
      str ("structure " ^ name ^ (if is_some some_decls then " : sig" else " ="))
      :: (the_list o Option.map (indent 2 o Pretty.chunks)) some_decls
      @| (if is_some some_decls then str "end = struct" else str "struct")
    )
    :: body
    @| str ("end; (*struct " ^ name ^ "*)")
  );

val literals_sml = Literals {
  literal_char = prefix "#" o quote o ML_Syntax.print_char,
  literal_string = quote o translate_string ML_Syntax.print_char,
  literal_numeral = fn k => "(" ^ string_of_int k ^ " : IntInf.int)",
  literal_positive_numeral = fn k => "(" ^ string_of_int k ^ " : IntInf.int)",
  literal_alternative_numeral = fn k => "(" ^ string_of_int k ^ " : IntInf.int)",
  literal_naive_numeral = string_of_int,
  literal_list = enum "," "[" "]",
  infix_cons = (7, "::")
};


(** OCaml serializer **)

fun print_ocaml_stmt tyco_syntax const_syntax reserved is_cons deresolve =
  let
    fun print_tyco_expr (tyco, []) = (str o deresolve) tyco
      | print_tyco_expr (tyco, [ty]) =
          concat [print_typ BR ty, (str o deresolve) tyco]
      | print_tyco_expr (tyco, tys) =
          concat [enum "," "(" ")" (map (print_typ BR) tys), (str o deresolve) tyco]
    and print_typ fxy (tyco `%% tys) = (case tyco_syntax tyco
         of NONE => print_tyco_expr (tyco, tys)
          | SOME (_, print) => print print_typ fxy tys)
      | print_typ fxy (ITyVar v) = str ("'" ^ v);
    fun print_dicttyp (class, ty) = print_tyco_expr (class, [ty]);
    fun print_typscheme_prefix (vs, p) = enum " ->" "" ""
      (map_filter (fn (v, sort) =>
        (print_product (fn class => print_dicttyp (class, ITyVar v)) sort)) vs @| p);
    fun print_typscheme (vs, ty) = print_typscheme_prefix (vs, print_typ NOBR ty);
    fun print_dicttypscheme (vs, class_ty) = print_typscheme_prefix (vs, print_dicttyp class_ty);
    val print_classrels =
      fold_rev (fn classrel => fn p => Pretty.block [p, str ".", (str o deresolve) classrel])
    fun print_dict is_pseudo_fun fxy (Dict (classrels, x)) =
      print_plain_dict is_pseudo_fun fxy x
      |> print_classrels classrels
    and print_plain_dict is_pseudo_fun fxy (Dict_Const (inst, dss)) =
          brackify BR ((str o deresolve) inst ::
            (if is_pseudo_fun inst then [str "()"]
            else map_filter (print_dicts is_pseudo_fun BR) dss))
      | print_plain_dict is_pseudo_fun fxy (Dict_Var (v, (i, k))) =
          str (if k = 1 then "_" ^ first_upper v
            else "_" ^ first_upper v ^ string_of_int (i+1))
    and print_dicts is_pseudo_fun = tuplify (print_dict is_pseudo_fun);
    val print_dict_args = map_filter (fn (v, sort) => print_dicts (K false) BR
      (map_index (fn (i, _) => Dict ([], Dict_Var (v, (i, length sort)))) sort));
    fun print_term is_pseudo_fun some_thm vars fxy (IConst c) =
          print_app is_pseudo_fun some_thm vars fxy (c, [])
      | print_term is_pseudo_fun some_thm vars fxy (IVar NONE) =
          str "_"
      | print_term is_pseudo_fun some_thm vars fxy (IVar (SOME v)) =
          str (lookup_var vars v)
      | print_term is_pseudo_fun some_thm vars fxy (t as t1 `$ t2) =
          (case Code_Thingol.unfold_const_app t
           of SOME c_ts => print_app is_pseudo_fun some_thm vars fxy c_ts
            | NONE => brackify fxy [print_term is_pseudo_fun some_thm vars NOBR t1,
                print_term is_pseudo_fun some_thm vars BR t2])
      | print_term is_pseudo_fun some_thm vars fxy (t as _ `|=> _) =
          let
            val (binds, t') = Code_Thingol.unfold_pat_abs t;
            val (ps, vars') = fold_map (print_bind is_pseudo_fun some_thm BR o fst) binds vars;
          in brackets (str "fun" :: ps @ str "->" @@ print_term is_pseudo_fun some_thm vars' NOBR t') end
      | print_term is_pseudo_fun some_thm vars fxy (ICase (cases as (_, t0))) =
          (case Code_Thingol.unfold_const_app t0
           of SOME (c_ts as ((c, _), _)) => if is_none (const_syntax c)
                then print_case is_pseudo_fun some_thm vars fxy cases
                else print_app is_pseudo_fun some_thm vars fxy c_ts
            | NONE => print_case is_pseudo_fun some_thm vars fxy cases)
    and print_app_expr is_pseudo_fun some_thm vars (app as ((c, (((_, iss), (tys, _)), _)), ts)) =
      if is_cons c then
        let val k = length tys in
          if length ts = k
          then (str o deresolve) c
            :: the_list (tuplify (print_term is_pseudo_fun some_thm vars) BR ts)
          else [print_term is_pseudo_fun some_thm vars BR (Code_Thingol.eta_expand k app)]
        end
      else if is_pseudo_fun c
        then (str o deresolve) c @@ str "()"
      else (str o deresolve) c :: map_filter (print_dicts is_pseudo_fun BR) iss
        @ map (print_term is_pseudo_fun some_thm vars BR) ts
    and print_app is_pseudo_fun some_thm vars = gen_print_app (print_app_expr is_pseudo_fun)
      (print_term is_pseudo_fun) const_syntax some_thm vars
    and print_bind is_pseudo_fun = gen_print_bind (print_term is_pseudo_fun)
    and print_case is_pseudo_fun some_thm vars fxy (cases as ((_, [_]), _)) =
          let
            val (binds, body) = Code_Thingol.unfold_let (ICase cases);
            fun print_let ((pat, _), t) vars =
              vars
              |> print_bind is_pseudo_fun some_thm NOBR pat
              |>> (fn p => concat
                  [str "let", p, str "=", print_term is_pseudo_fun some_thm vars NOBR t, str "in"])
            val (ps, vars') = fold_map print_let binds vars;
          in
            brackify_block fxy (Pretty.chunks ps) []
              (print_term is_pseudo_fun some_thm vars' NOBR body)
          end
      | print_case is_pseudo_fun some_thm vars fxy (((t, ty), clause :: clauses), _) =
          let
            fun print_select delim (pat, body) =
              let
                val (p, vars') = print_bind is_pseudo_fun some_thm NOBR pat vars;
              in concat [str delim, p, str "->", print_term is_pseudo_fun some_thm vars' NOBR body] end;
          in
            brackets (
              str "match"
              :: print_term is_pseudo_fun some_thm vars NOBR t
              :: print_select "with" clause
              :: map (print_select "|") clauses
            )
          end
      | print_case is_pseudo_fun some_thm vars fxy ((_, []), _) =
          (concat o map str) ["failwith", "\"empty case\""];
    fun print_val_decl print_typscheme (name, typscheme) = concat
      [str "val", str (deresolve name), str ":", print_typscheme typscheme];
    fun print_datatype_decl definer (tyco, (vs, cos)) =
      let
        fun print_co ((co, _), []) = str (deresolve co)
          | print_co ((co, _), tys) = concat [str (deresolve co), str "of",
              enum " *" "" "" (map (print_typ (INFX (2, X))) tys)];
      in
        concat (
          str definer
          :: print_tyco_expr (tyco, map (ITyVar o fst) vs)
          :: str "="
          :: separate (str "|") (map print_co cos)
        )
      end;
    fun print_def is_pseudo_fun needs_typ definer
          (ML_Function (name, (vs_ty as (vs, ty), eqs))) =
          let
            fun print_eqn ((ts, t), (some_thm, _)) =
              let
                val consts = fold Code_Thingol.add_constnames (t :: ts) [];
                val vars = reserved
                  |> intro_base_names
                      (is_none o const_syntax) deresolve consts
                  |> intro_vars ((fold o Code_Thingol.fold_varnames)
                      (insert (op =)) ts []);
              in concat [
                (Pretty.block o commas)
                  (map (print_term is_pseudo_fun some_thm vars NOBR) ts),
                str "->",
                print_term is_pseudo_fun some_thm vars NOBR t
              ] end;
            fun print_eqns is_pseudo [((ts, t), (some_thm, _))] =
                  let
                    val consts = fold Code_Thingol.add_constnames (t :: ts) [];
                    val vars = reserved
                      |> intro_base_names
                          (is_none o const_syntax) deresolve consts
                      |> intro_vars ((fold o Code_Thingol.fold_varnames)
                          (insert (op =)) ts []);
                  in
                    concat (
                      (if is_pseudo then [str "()"]
                        else map (print_term is_pseudo_fun some_thm vars BR) ts)
                      @ str "="
                      @@ print_term is_pseudo_fun some_thm vars NOBR t
                    )
                  end
              | print_eqns _ ((eq as (([_], _), _)) :: eqs) =
                  Pretty.block (
                    str "="
                    :: Pretty.brk 1
                    :: str "function"
                    :: Pretty.brk 1
                    :: print_eqn eq
                    :: maps (append [Pretty.fbrk, str "|", Pretty.brk 1]
                          o single o print_eqn) eqs
                  )
              | print_eqns _ (eqs as eq :: eqs') =
                  let
                    val consts = fold Code_Thingol.add_constnames (map (snd o fst) eqs) [];
                    val vars = reserved
                      |> intro_base_names
                          (is_none o const_syntax) deresolve consts;
                    val dummy_parms = (map str o aux_params vars o map (fst o fst)) eqs;
                  in
                    Pretty.block (
                      Pretty.breaks dummy_parms
                      @ Pretty.brk 1
                      :: str "="
                      :: Pretty.brk 1
                      :: str "match"
                      :: Pretty.brk 1
                      :: (Pretty.block o commas) dummy_parms
                      :: Pretty.brk 1
                      :: str "with"
                      :: Pretty.brk 1
                      :: print_eqn eq
                      :: maps (append [Pretty.fbrk, str "|", Pretty.brk 1]
                           o single o print_eqn) eqs'
                    )
                  end;
            val prolog = if needs_typ then
              concat [str definer, (str o deresolve) name, str ":", print_typ NOBR ty]
                else (concat o map str) [definer, deresolve name];
          in pair
            (print_val_decl print_typscheme (name, vs_ty))
            (concat (
              prolog
              :: print_dict_args vs
              @| print_eqns (is_pseudo_fun name) eqs
            ))
          end
      | print_def is_pseudo_fun _ definer
            (ML_Instance (inst, ((class, (tyco, vs)), (super_instances, (classparam_instances, _))))) =
          let
            fun print_super_instance (_, (classrel, x)) =
              concat [
                (str o deresolve) classrel,
                str "=",
                print_dict is_pseudo_fun NOBR (Dict ([], Dict_Const x))
              ];
            fun print_classparam_instance ((classparam, const), (thm, _)) =
              concat [
                (str o deresolve) classparam,
                str "=",
                print_app (K false) (SOME thm) reserved NOBR (const, [])
              ];
          in pair
            (print_val_decl print_dicttypscheme
              (inst, (vs, (class, tyco `%% map (ITyVar o fst) vs))))
            (concat (
              str definer
              :: (str o deresolve) inst
              :: (if is_pseudo_fun inst then [str "()"]
                  else print_dict_args vs)
              @ str "="
              @@ brackets [
                enum_default "()" ";" "{" "}" (map print_super_instance super_instances
                  @ map print_classparam_instance classparam_instances),
                str ":",
                print_tyco_expr (class, [tyco `%% map (ITyVar o fst) vs])
              ]
            ))
          end;
     fun print_stmt (ML_Exc (name, (vs_ty, n))) = pair
          [print_val_decl print_typscheme (name, vs_ty)]
          ((doublesemicolon o map str) (
            "let"
            :: deresolve name
            :: replicate n "_"
            @ "="
            :: "failwith"
            @@ (ML_Syntax.print_string o Long_Name.base_name o Long_Name.qualifier) name
          ))
      | print_stmt (ML_Val binding) =
          let
            val (sig_p, p) = print_def (K false) true "let" binding
          in pair
            [sig_p]
            (doublesemicolon [p])
          end
      | print_stmt (ML_Funs (binding :: bindings, pseudo_funs)) =
          let
            val print_def' = print_def (member (op =) pseudo_funs) false;
            fun print_pseudo_fun name = concat [
                str "let",
                (str o deresolve) name,
                str "=",
                (str o deresolve) name,
                str "();;"
              ];
            val (sig_ps, (ps, p)) = (apsnd split_last o split_list)
              (print_def' "let rec" binding :: map (print_def' "and") bindings);
            val pseudo_ps = map print_pseudo_fun pseudo_funs;
          in pair
            sig_ps
            (Pretty.chunks (ps @ doublesemicolon [p] :: pseudo_ps))
          end
     | print_stmt (ML_Datas [(tyco, (vs, []))]) =
          let
            val ty_p = print_tyco_expr (tyco, map (ITyVar o fst) vs);
          in
            pair
            [concat [str "type", ty_p]]
            (concat [str "type", ty_p, str "=", str "EMPTY__"])
          end
     | print_stmt (ML_Datas (data :: datas)) = 
          let
            val sig_ps = print_datatype_decl "type" data
              :: map (print_datatype_decl "and") datas;
            val (ps, p) = split_last sig_ps;
          in pair
            sig_ps
            (Pretty.chunks (ps @| doublesemicolon [p]))
          end
     | print_stmt (ML_Class (class, (v, (super_classes, classparams)))) =
          let
            fun print_field s p = concat [str s, str ":", p];
            fun print_super_class_field (super_class, classrel) =
              print_field (deresolve classrel) (print_dicttyp (super_class, ITyVar v));
            fun print_classparam_decl (classparam, ty) =
              print_val_decl print_typscheme
                (classparam, ([(v, [class])], ty));
            fun print_classparam_field (classparam, ty) =
              print_field (deresolve classparam) (print_typ NOBR ty);
            val w = "_" ^ first_upper v;
            fun print_classparam_proj (classparam, _) =
              (concat o map str) ["let", deresolve classparam, w, "=",
                w ^ "." ^ deresolve classparam ^ ";;"];
            val type_decl_p = concat [
                str ("type '" ^ v),
                (str o deresolve) class,
                str "=",
                enum_default "unit" ";" "{" "}" (
                  map print_super_class_field super_classes
                  @ map print_classparam_field classparams
                )
              ];
          in pair
            (type_decl_p :: map print_classparam_decl classparams)
            (Pretty.chunks (
              doublesemicolon [type_decl_p]
              :: map print_classparam_proj classparams
            ))
          end;
  in print_stmt end;

fun print_ocaml_module name some_decls body =
  Pretty.chunks2 (
    Pretty.chunks (
      str ("module " ^ name ^ (if is_some some_decls then " : sig" else " ="))
      :: (the_list o Option.map (indent 2 o Pretty.chunks)) some_decls
      @| (if is_some some_decls then str "end = struct" else str "struct")
    )
    :: body
    @| str ("end;; (*struct " ^ name ^ "*)")
  );

val literals_ocaml = let
  fun chr i =
    let
      val xs = string_of_int i;
      val ys = replicate_string (3 - length (raw_explode xs)) "0";
    in "\\" ^ ys ^ xs end;
  fun char_ocaml c =
    let
      val i = ord c;
      val s = if i < 32 orelse i = 34 orelse i = 39 orelse i = 92 orelse i > 126
        then chr i else c
    in s end;
  fun numeral_ocaml k = if k < 0
    then "(Big_int.minus_big_int " ^ numeral_ocaml (~ k) ^ ")"
    else if k <= 1073741823
      then "(Big_int.big_int_of_int " ^ string_of_int k ^ ")"
      else "(Big_int.big_int_of_string " ^ quote (string_of_int k) ^ ")"
in Literals {
  literal_char = Library.enclose "'" "'" o char_ocaml,
  literal_string = quote o translate_string char_ocaml,
  literal_numeral = numeral_ocaml,
  literal_positive_numeral = numeral_ocaml,
  literal_alternative_numeral = numeral_ocaml,
  literal_naive_numeral = numeral_ocaml,
  literal_list = enum ";" "[" "]",
  infix_cons = (6, "::")
} end;



(** SML/OCaml generic part **)

fun ml_program_of_program labelled_name reserved module_alias program =
  let
    fun namify_const upper base (nsp_const, nsp_type) =
      let
        val (base', nsp_const') =
          Name.variant (if upper then first_upper base else base) nsp_const
      in (base', (nsp_const', nsp_type)) end;
    fun namify_type base (nsp_const, nsp_type) =
      let
        val (base', nsp_type') = Name.variant base nsp_type
      in (base', (nsp_const, nsp_type')) end;
    fun namify_stmt (Code_Thingol.Fun _) = namify_const false
      | namify_stmt (Code_Thingol.Datatype _) = namify_type
      | namify_stmt (Code_Thingol.Datatypecons _) = namify_const true
      | namify_stmt (Code_Thingol.Class _) = namify_type
      | namify_stmt (Code_Thingol.Classrel _) = namify_const false
      | namify_stmt (Code_Thingol.Classparam _) = namify_const false
      | namify_stmt (Code_Thingol.Classinst _) = namify_const false;
    fun ml_binding_of_stmt (name, Code_Thingol.Fun (_, ((tysm as (vs, ty), raw_eqs), _))) =
          let
            val eqs = filter (snd o snd) raw_eqs;
            val (eqs', some_value_name) = if null (filter_out (null o snd) vs) then case eqs
               of [(([], t), some_thm)] => if (not o null o fst o Code_Thingol.unfold_fun) ty
                  then ([(([IVar (SOME "x")], t `$ IVar (SOME "x")), some_thm)], NONE)
                  else (eqs, SOME (name, member (op =) (Code_Thingol.add_constnames t []) name))
                | _ => (eqs, NONE)
              else (eqs, NONE)
          in (ML_Function (name, (tysm, eqs')), some_value_name) end
      | ml_binding_of_stmt (name, Code_Thingol.Classinst (stmt as ((_, (_, vs)), _))) =
          (ML_Instance (name, stmt), if forall (null o snd) vs then SOME (name, false) else NONE)
      | ml_binding_of_stmt (name, _) =
          error ("Binding block containing illegal statement: " ^ labelled_name name)
    fun modify_fun (name, stmt) =
      let
        val (binding, some_value_name) = ml_binding_of_stmt (name, stmt);
        val ml_stmt = case binding
         of ML_Function (name, ((vs, ty), [])) =>
              ML_Exc (name, ((vs, ty),
                (length o filter_out (null o snd)) vs + (length o fst o Code_Thingol.unfold_fun) ty))
          | _ => case some_value_name
             of NONE => ML_Funs ([binding], [])
              | SOME (name, true) => ML_Funs ([binding], [name])
              | SOME (name, false) => ML_Val binding
      in SOME ml_stmt end;
    fun modify_funs stmts = single (SOME
      (ML_Funs (map_split ml_binding_of_stmt stmts |> (apsnd o map_filter o Option.map) fst)))
    fun modify_datatypes stmts = single (SOME
      (ML_Datas (map_filter
        (fn (name, Code_Thingol.Datatype (_, stmt)) => SOME (name, stmt) | _ => NONE) stmts)))
    fun modify_class stmts = single (SOME
      (ML_Class (the_single (map_filter
        (fn (name, Code_Thingol.Class (_, stmt)) => SOME (name, stmt) | _ => NONE) stmts))))
    fun modify_stmts ([stmt as (_, stmt' as Code_Thingol.Fun _)]) =
          if Code_Thingol.is_case stmt' then [] else [modify_fun stmt]
      | modify_stmts ((stmts as (_, Code_Thingol.Fun _)::_)) =
          modify_funs (filter_out (Code_Thingol.is_case o snd) stmts)
      | modify_stmts ((stmts as (_, Code_Thingol.Datatypecons _)::_)) =
          modify_datatypes stmts
      | modify_stmts ((stmts as (_, Code_Thingol.Datatype _)::_)) =
          modify_datatypes stmts
      | modify_stmts ((stmts as (_, Code_Thingol.Class _)::_)) =
          modify_class stmts
      | modify_stmts ((stmts as (_, Code_Thingol.Classrel _)::_)) =
          modify_class stmts
      | modify_stmts ((stmts as (_, Code_Thingol.Classparam _)::_)) =
          modify_class stmts
      | modify_stmts ([stmt as (_, Code_Thingol.Classinst _)]) =
          [modify_fun stmt]
      | modify_stmts ((stmts as (_, Code_Thingol.Classinst _)::_)) =
          modify_funs stmts
      | modify_stmts stmts = error ("Illegal mutual dependencies: " ^
          (Library.commas o map (labelled_name o fst)) stmts);
  in
    Code_Namespace.hierarchical_program labelled_name { module_alias = module_alias, reserved = reserved,
      empty_nsp = (reserved, reserved), namify_module = pair, namify_stmt = namify_stmt,
      cyclic_modules = false, empty_data = (), memorize_data = K I, modify_stmts = modify_stmts } program
  end;

fun serialize_ml print_ml_module print_ml_stmt with_signatures
    { labelled_name, reserved_syms, includes, module_alias,
      class_syntax, tyco_syntax, const_syntax } program =
  let

    (* build program *)
    val { deresolver, hierarchical_program = ml_program } =
      ml_program_of_program labelled_name (Name.make_context reserved_syms) module_alias program;

    (* print statements *)
    fun print_stmt prefix_fragments (_, stmt) = print_ml_stmt
      tyco_syntax const_syntax (make_vars reserved_syms)
      (Code_Thingol.is_cons program) (deresolver prefix_fragments) stmt
      |> apfst SOME;

    (* print modules *)
    fun print_module _ base _ xs =
      let
        val (raw_decls, body) = split_list xs;
        val decls = if with_signatures then SOME (maps these raw_decls) else NONE 
      in (NONE, print_ml_module base decls body) end;

    (* serialization *)
    val p = Pretty.chunks2 (map snd includes
      @ map snd (Code_Namespace.print_hierarchical {
        print_module = print_module, print_stmt = print_stmt,
        lift_markup = apsnd } ml_program));
    fun write width NONE = writeln o format [] width
      | write width (SOME p) = File.write p o format [] width;
  in
    Code_Target.serialization write (rpair (try (deresolver [])) ooo format) p
  end;

val serializer_sml : Code_Target.serializer =
  Code_Target.parse_args (Scan.optional (Args.$$$ "no_signatures" >> K false) true
  >> (fn with_signatures => serialize_ml print_sml_module print_sml_stmt with_signatures));

val serializer_ocaml : Code_Target.serializer =
  Code_Target.parse_args (Scan.optional (Args.$$$ "no_signatures" >> K false) true
  >> (fn with_signatures => serialize_ml print_ocaml_module print_ocaml_stmt with_signatures));


(** Isar setup **)

val setup =
  Code_Target.add_target
    (target_SML, { serializer = serializer_sml, literals = literals_sml,
      check = { env_var = "ISABELLE_PROCESS",
        make_destination = fn p => Path.append p (Path.explode "ROOT.ML"),
        make_command = fn _ => "\"$ISABELLE_PROCESS\" -r -q -u Pure" } })
  #> Code_Target.add_target
    (target_OCaml, { serializer = serializer_ocaml, literals = literals_ocaml,
      check = { env_var = "ISABELLE_OCAML",
        make_destination = fn p => Path.append p (Path.explode "ROOT.ocaml"),
        make_command = fn _ => "\"$ISABELLE_OCAML\" -w pu nums.cma ROOT.ocaml" } })
  #> Code_Target.add_tyco_syntax target_SML "fun" (SOME (2, fn print_typ => fn fxy => fn [ty1, ty2] =>
      brackify_infix (1, R) fxy (
        print_typ (INFX (1, X)) ty1,
        str "->",
        print_typ (INFX (1, R)) ty2
      )))
  #> Code_Target.add_tyco_syntax target_OCaml "fun" (SOME (2, fn print_typ => fn fxy => fn [ty1, ty2] =>
      brackify_infix (1, R) fxy (
        print_typ (INFX (1, X)) ty1,
        str "->",
        print_typ (INFX (1, R)) ty2
      )))
  #> fold (Code_Target.add_reserved target_SML) ML_Syntax.reserved_names
  #> fold (Code_Target.add_reserved target_SML)
      ["ref" (*rebinding is illegal*), "o" (*dictionary projections use it already*),
        "Fail", "div", "mod" (*standard infixes*), "IntInf"]
  #> fold (Code_Target.add_reserved target_OCaml) [
      "and", "as", "assert", "begin", "class",
      "constraint", "do", "done", "downto", "else", "end", "exception",
      "external", "false", "for", "fun", "function", "functor", "if",
      "in", "include", "inherit", "initializer", "lazy", "let", "match", "method",
      "module", "mutable", "new", "object", "of", "open", "or", "private", "rec",
      "sig", "struct", "then", "to", "true", "try", "type", "val",
      "virtual", "when", "while", "with"
    ]
  #> fold (Code_Target.add_reserved target_OCaml) ["failwith", "mod", "Big_int"];

end; (*struct*)
