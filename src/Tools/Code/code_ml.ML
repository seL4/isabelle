(*  Title:      Tools/code/code_ml.ML_
    Author:     Florian Haftmann, TU Muenchen

Serializer for SML and OCaml.
*)

signature CODE_ML =
sig
  val target_SML: string
  val evaluation_code_of: theory -> string -> string option
    -> Code_Thingol.naming -> Code_Thingol.program -> string list -> string * string option list
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
    ML_Function of string * (typscheme * ((iterm list * iterm) * (thm * bool)) list)
  | ML_Instance of string * ((class * (string * (vname * sort) list))
        * ((class * (string * (string * dict list list))) list
      * ((string * const) * (thm * bool)) list));

datatype ml_stmt =
    ML_Exc of string * (typscheme * int)
  | ML_Val of ml_binding
  | ML_Funs of ml_binding list * string list
  | ML_Datas of (string * ((vname * sort) list * (string * itype list) list)) list
  | ML_Class of string * (vname * ((class * string) list * (string * itype) list));

fun stmt_name_of_binding (ML_Function (name, _)) = name
  | stmt_name_of_binding (ML_Instance (name, _)) = name;

fun stmt_names_of (ML_Exc (name, _)) = [name]
  | stmt_names_of (ML_Val binding) = [stmt_name_of_binding binding]
  | stmt_names_of (ML_Funs (bindings, _)) = map stmt_name_of_binding bindings
  | stmt_names_of (ML_Datas ds) = map fst ds
  | stmt_names_of (ML_Class (name, _)) = [name];

fun print_product _ [] = NONE
  | print_product print [x] = SOME (print x)
  | print_product print xs = (SOME o Pretty.enum " *" "" "") (map print xs);

fun print_tuple _ _ [] = NONE
  | print_tuple print fxy [x] = SOME (print fxy x)
  | print_tuple print _ xs = SOME (Pretty.list "(" ")" (map (print NOBR) xs));


(** SML serializer **)

fun print_sml_stmt labelled_name syntax_tyco syntax_const reserved is_cons deresolve =
  let
    fun print_tyco_expr fxy (tyco, []) = (str o deresolve) tyco
      | print_tyco_expr fxy (tyco, [ty]) =
          concat [print_typ BR ty, (str o deresolve) tyco]
      | print_tyco_expr fxy (tyco, tys) =
          concat [Pretty.list "(" ")" (map (print_typ BR) tys), (str o deresolve) tyco]
    and print_typ fxy (tyco `%% tys) = (case syntax_tyco tyco
         of NONE => print_tyco_expr fxy (tyco, tys)
          | SOME (i, print) => print print_typ fxy tys)
      | print_typ fxy (ITyVar v) = str ("'" ^ v);
    fun print_dicttyp (class, ty) = print_tyco_expr NOBR (class, [ty]);
    fun print_typscheme_prefix (vs, p) = Pretty.enum " ->" "" ""
      (map_filter (fn (v, sort) =>
        (print_product (fn class => print_dicttyp (class, ITyVar v)) sort)) vs @| p);
    fun print_typscheme (vs, ty) = print_typscheme_prefix (vs, print_typ NOBR ty);
    fun print_dicttypscheme (vs, class_ty) = print_typscheme_prefix (vs, print_dicttyp class_ty);
    fun print_dict is_pseudo_fun fxy (DictConst (inst, dss)) =
          brackify fxy ((str o deresolve) inst ::
            (if is_pseudo_fun inst then [str "()"]
            else map_filter (print_dicts is_pseudo_fun BR) dss))
      | print_dict is_pseudo_fun fxy (DictVar (classrels, (v, (i, k)))) =
          let
            val v_p = str (if k = 1 then first_upper v ^ "_"
              else first_upper v ^ string_of_int (i+1) ^ "_");
          in case classrels
           of [] => v_p
            | [classrel] => brackets [(str o deresolve) classrel, v_p]
            | classrels => brackets
                [Pretty.enum " o" "(" ")" (map (str o deresolve) classrels), v_p]
          end
    and print_dicts is_pseudo_fun = print_tuple (print_dict is_pseudo_fun);
    val print_dict_args = map_filter (fn (v, sort) => print_dicts (K false) BR
      (map_index (fn (i, _) => DictVar ([], (v, (i, length sort)))) sort));
    fun print_term is_pseudo_fun thm vars fxy (IConst c) =
          print_app is_pseudo_fun thm vars fxy (c, [])
      | print_term is_pseudo_fun thm vars fxy (IVar NONE) =
          str "_"
      | print_term is_pseudo_fun thm vars fxy (IVar (SOME v)) =
          str (lookup_var vars v)
      | print_term is_pseudo_fun thm vars fxy (t as t1 `$ t2) =
          (case Code_Thingol.unfold_const_app t
           of SOME c_ts => print_app is_pseudo_fun thm vars fxy c_ts
            | NONE => brackify fxy [print_term is_pseudo_fun thm vars NOBR t1,
                print_term is_pseudo_fun thm vars BR t2])
      | print_term is_pseudo_fun thm vars fxy (t as _ `|=> _) =
          let
            val (binds, t') = Code_Thingol.unfold_pat_abs t;
            fun print_abs (pat, ty) =
              print_bind is_pseudo_fun thm NOBR pat
              #>> (fn p => concat [str "fn", p, str "=>"]);
            val (ps, vars') = fold_map print_abs binds vars;
          in brackets (ps @ [print_term is_pseudo_fun thm vars' NOBR t']) end
      | print_term is_pseudo_fun thm vars fxy (ICase (cases as (_, t0))) =
          (case Code_Thingol.unfold_const_app t0
           of SOME (c_ts as ((c, _), _)) => if is_none (syntax_const c)
                then print_case is_pseudo_fun thm vars fxy cases
                else print_app is_pseudo_fun thm vars fxy c_ts
            | NONE => print_case is_pseudo_fun thm vars fxy cases)
    and print_app_expr is_pseudo_fun thm vars (app as ((c, ((_, iss), tys)), ts)) =
      if is_cons c then
        let val k = length tys in
          if k < 2 orelse length ts = k
          then (str o deresolve) c
            :: the_list (print_tuple (print_term is_pseudo_fun thm vars) BR ts)
          else [print_term is_pseudo_fun thm vars BR (Code_Thingol.eta_expand k app)]
        end
      else if is_pseudo_fun c
        then (str o deresolve) c @@ str "()"
      else (str o deresolve) c :: map_filter (print_dicts is_pseudo_fun BR) iss
        @ map (print_term is_pseudo_fun thm vars BR) ts
    and print_app is_pseudo_fun thm vars = gen_print_app (print_app_expr is_pseudo_fun)
      (print_term is_pseudo_fun) syntax_const thm vars
    and print_bind is_pseudo_fun = gen_print_bind (print_term is_pseudo_fun)
    and print_case is_pseudo_fun thm vars fxy (cases as ((_, [_]), _)) =
          let
            val (binds, body) = Code_Thingol.unfold_let (ICase cases);
            fun print_match ((pat, ty), t) vars =
              vars
              |> print_bind is_pseudo_fun thm NOBR pat
              |>> (fn p => semicolon [str "val", p, str "=",
                    print_term is_pseudo_fun thm vars NOBR t])
            val (ps, vars') = fold_map print_match binds vars;
          in
            Pretty.chunks [
              Pretty.block [str ("let"), Pretty.fbrk, Pretty.chunks ps],
              Pretty.block [str ("in"), Pretty.fbrk, print_term is_pseudo_fun thm vars' NOBR body],
              str ("end")
            ]
          end
      | print_case is_pseudo_fun thm vars fxy (((t, ty), clause :: clauses), _) =
          let
            fun print_select delim (pat, body) =
              let
                val (p, vars') = print_bind is_pseudo_fun thm NOBR pat vars;
              in
                concat [str delim, p, str "=>", print_term is_pseudo_fun thm vars' NOBR body]
              end;
          in
            brackets (
              str "case"
              :: print_term is_pseudo_fun thm vars NOBR t
              :: print_select "of" clause
              :: map (print_select "|") clauses
            )
          end
      | print_case is_pseudo_fun thm vars fxy ((_, []), _) =
          (concat o map str) ["raise", "Fail", "\"empty case\""];
    fun print_val_decl print_typscheme (name, typscheme) = concat
      [str "val", str (deresolve name), str ":", print_typscheme typscheme];
    fun print_datatype_decl definer (tyco, (vs, cos)) =
      let
        fun print_co (co, []) = str (deresolve co)
          | print_co (co, tys) = concat [str (deresolve co), str "of",
              Pretty.enum " *" "" "" (map (print_typ (INFX (2, X))) tys)];
      in
        concat (
          str definer
          :: print_tyco_expr NOBR (tyco, map (ITyVar o fst) vs)
          :: str "="
          :: separate (str "|") (map print_co cos)
        )
      end;
    fun print_def is_pseudo_fun needs_typ definer
          (ML_Function (name, (vs_ty as (vs, ty), eq :: eqs))) =
          let
            fun print_eqn definer ((ts, t), (thm, _)) =
              let
                val consts = fold Code_Thingol.add_constnames (t :: ts) [];
                val vars = reserved
                  |> intro_base_names
                       (is_none o syntax_const) deresolve consts
                  |> intro_vars ((fold o Code_Thingol.fold_varnames)
                       (insert (op =)) ts []);
                val prolog = if needs_typ then
                  concat [str definer, (str o deresolve) name, str ":", print_typ NOBR ty]
                    else Pretty.strs [definer, deresolve name];
              in
                concat (
                  prolog
                  :: (if is_pseudo_fun name then [str "()"]
                      else print_dict_args vs
                        @ map (print_term is_pseudo_fun thm vars BR) ts)
                  @ str "="
                  @@ print_term is_pseudo_fun thm vars NOBR t
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
          (ML_Instance (inst, ((class, (tyco, vs)), (superinsts, classparams)))) =
          let
            fun print_superinst (_, (classrel, dss)) =
              concat [
                (str o Long_Name.base_name o deresolve) classrel,
                str "=",
                print_dict is_pseudo_fun NOBR (DictConst dss)
              ];
            fun print_classparam ((classparam, c_inst), (thm, _)) =
              concat [
                (str o Long_Name.base_name o deresolve) classparam,
                str "=",
                print_app (K false) thm reserved NOBR (c_inst, [])
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
              :: Pretty.list "{" "}"
                (map print_superinst superinsts @ map print_classparam classparams)
              :: str ":"
              @@ print_tyco_expr NOBR (class, [tyco `%% map (ITyVar o fst) vs])
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
            val ty_p = print_tyco_expr NOBR (tyco, map (ITyVar o fst) vs);
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
     | print_stmt (ML_Class (class, (v, (superclasses, classparams)))) =
          let
            fun print_field s p = concat [str s, str ":", p];
            fun print_proj s p = semicolon
              (map str ["val", s, "=", "#" ^ s, ":"] @| p);
            fun print_superclass_decl (superclass, classrel) =
              print_val_decl print_dicttypscheme
                (classrel, ([(v, [class])], (superclass, ITyVar v)));
            fun print_superclass_field (superclass, classrel) =
              print_field (deresolve classrel) (print_dicttyp (superclass, ITyVar v));
            fun print_superclass_proj (superclass, classrel) =
              print_proj (deresolve classrel)
                (print_dicttypscheme ([(v, [class])], (superclass, ITyVar v)));
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
              :: map print_superclass_decl superclasses
              @ map print_classparam_decl classparams)
            (Pretty.chunks (
              concat [
                str ("type '" ^ v),
                (str o deresolve) class,
                str "=",
                Pretty.list "{" "};" (
                  map print_superclass_field superclasses
                  @ map print_classparam_field classparams
                )
              ]
              :: map print_superclass_proj superclasses
              @ map print_classparam_proj classparams
            ))
          end;
  in print_stmt end;

fun print_sml_module name some_decls body = Pretty.chunks2 (
    Pretty.chunks (
      str ("structure " ^ name ^ (if is_some some_decls then " : sig" else " ="))
      :: (the_list o Option.map (Pretty.indent 2 o Pretty.chunks)) some_decls
      @| (if is_some some_decls then str "end = struct" else str "struct")
    )
    :: body
    @| str ("end; (*struct " ^ name ^ "*)")
  );

val literals_sml = Literals {
  literal_char = prefix "#" o quote o ML_Syntax.print_char,
  literal_string = quote o translate_string ML_Syntax.print_char,
  literal_numeral = fn unbounded => fn k =>
    if unbounded then "(" ^ string_of_int k ^ " : IntInf.int)"
    else string_of_int k,
  literal_list = Pretty.list "[" "]",
  infix_cons = (7, "::")
};


(** OCaml serializer **)

fun print_ocaml_stmt labelled_name syntax_tyco syntax_const reserved is_cons deresolve =
  let
    fun print_tyco_expr fxy (tyco, []) = (str o deresolve) tyco
      | print_tyco_expr fxy (tyco, [ty]) =
          concat [print_typ BR ty, (str o deresolve) tyco]
      | print_tyco_expr fxy (tyco, tys) =
          concat [Pretty.list "(" ")" (map (print_typ BR) tys), (str o deresolve) tyco]
    and print_typ fxy (tyco `%% tys) = (case syntax_tyco tyco
         of NONE => print_tyco_expr fxy (tyco, tys)
          | SOME (i, print) => print print_typ fxy tys)
      | print_typ fxy (ITyVar v) = str ("'" ^ v);
    fun print_dicttyp (class, ty) = print_tyco_expr NOBR (class, [ty]);
    fun print_typscheme_prefix (vs, p) = Pretty.enum " ->" "" ""
      (map_filter (fn (v, sort) =>
        (print_product (fn class => print_dicttyp (class, ITyVar v)) sort)) vs @| p);
    fun print_typscheme (vs, ty) = print_typscheme_prefix (vs, print_typ NOBR ty);
    fun print_dicttypscheme (vs, class_ty) = print_typscheme_prefix (vs, print_dicttyp class_ty);
    fun print_dict is_pseudo_fun fxy (DictConst (inst, dss)) =
          brackify fxy ((str o deresolve) inst ::
            (if is_pseudo_fun inst then [str "()"]
            else map_filter (print_dicts is_pseudo_fun BR) dss))
      | print_dict is_pseudo_fun fxy (DictVar (classrels, (v, (i, k)))) =
          str (if k = 1 then "_" ^ first_upper v
            else "_" ^ first_upper v ^ string_of_int (i+1))
          |> fold_rev (fn classrel => fn p =>
               Pretty.block [p, str ".", (str o deresolve) classrel]) classrels
    and print_dicts is_pseudo_fun = print_tuple (print_dict is_pseudo_fun);
    val print_dict_args = map_filter (fn (v, sort) => print_dicts (K false) BR
      (map_index (fn (i, _) => DictVar ([], (v, (i, length sort)))) sort));
    fun print_term is_pseudo_fun thm vars fxy (IConst c) =
          print_app is_pseudo_fun thm vars fxy (c, [])
      | print_term is_pseudo_fun thm vars fxy (IVar NONE) =
          str "_"
      | print_term is_pseudo_fun thm vars fxy (IVar (SOME v)) =
          str (lookup_var vars v)
      | print_term is_pseudo_fun thm vars fxy (t as t1 `$ t2) =
          (case Code_Thingol.unfold_const_app t
           of SOME c_ts => print_app is_pseudo_fun thm vars fxy c_ts
            | NONE => brackify fxy [print_term is_pseudo_fun thm vars NOBR t1,
                print_term is_pseudo_fun thm vars BR t2])
      | print_term is_pseudo_fun thm vars fxy (t as _ `|=> _) =
          let
            val (binds, t') = Code_Thingol.unfold_pat_abs t;
            val (ps, vars') = fold_map (print_bind is_pseudo_fun thm BR o fst) binds vars;
          in brackets (str "fun" :: ps @ str "->" @@ print_term is_pseudo_fun thm vars' NOBR t') end
      | print_term is_pseudo_fun thm vars fxy (ICase (cases as (_, t0))) =
          (case Code_Thingol.unfold_const_app t0
           of SOME (c_ts as ((c, _), _)) => if is_none (syntax_const c)
                then print_case is_pseudo_fun thm vars fxy cases
                else print_app is_pseudo_fun thm vars fxy c_ts
            | NONE => print_case is_pseudo_fun thm vars fxy cases)
    and print_app_expr is_pseudo_fun thm vars (app as ((c, ((_, iss), tys)), ts)) =
      if is_cons c then
        let val k = length tys in
          if length ts = k
          then (str o deresolve) c
            :: the_list (print_tuple (print_term is_pseudo_fun thm vars) BR ts)
          else [print_term is_pseudo_fun thm vars BR (Code_Thingol.eta_expand k app)]
        end
      else if is_pseudo_fun c
        then (str o deresolve) c @@ str "()"
      else (str o deresolve) c :: map_filter (print_dicts is_pseudo_fun BR) iss
        @ map (print_term is_pseudo_fun thm vars BR) ts
    and print_app is_pseudo_fun thm vars = gen_print_app (print_app_expr is_pseudo_fun)
      (print_term is_pseudo_fun) syntax_const thm vars
    and print_bind is_pseudo_fun = gen_print_bind (print_term is_pseudo_fun)
    and print_case is_pseudo_fun thm vars fxy (cases as ((_, [_]), _)) =
          let
            val (binds, body) = Code_Thingol.unfold_let (ICase cases);
            fun print_let ((pat, ty), t) vars =
              vars
              |> print_bind is_pseudo_fun thm NOBR pat
              |>> (fn p => concat
                  [str "let", p, str "=", print_term is_pseudo_fun thm vars NOBR t, str "in"])
            val (ps, vars') = fold_map print_let binds vars;
          in
            brackify_block fxy (Pretty.chunks ps) []
              (print_term is_pseudo_fun thm vars' NOBR body)
          end
      | print_case is_pseudo_fun thm vars fxy (((t, ty), clause :: clauses), _) =
          let
            fun print_select delim (pat, body) =
              let
                val (p, vars') = print_bind is_pseudo_fun thm NOBR pat vars;
              in concat [str delim, p, str "->", print_term is_pseudo_fun thm vars' NOBR body] end;
          in
            brackets (
              str "match"
              :: print_term is_pseudo_fun thm vars NOBR t
              :: print_select "with" clause
              :: map (print_select "|") clauses
            )
          end
      | print_case is_pseudo_fun thm vars fxy ((_, []), _) =
          (concat o map str) ["failwith", "\"empty case\""];
    fun print_val_decl print_typscheme (name, typscheme) = concat
      [str "val", str (deresolve name), str ":", print_typscheme typscheme];
    fun print_datatype_decl definer (tyco, (vs, cos)) =
      let
        fun print_co (co, []) = str (deresolve co)
          | print_co (co, tys) = concat [str (deresolve co), str "of",
              Pretty.enum " *" "" "" (map (print_typ (INFX (2, X))) tys)];
      in
        concat (
          str definer
          :: print_tyco_expr NOBR (tyco, map (ITyVar o fst) vs)
          :: str "="
          :: separate (str "|") (map print_co cos)
        )
      end;
    fun print_def is_pseudo_fun needs_typ definer
          (ML_Function (name, (vs_ty as (vs, ty), eqs))) =
          let
            fun print_eqn ((ts, t), (thm, _)) =
              let
                val consts = fold Code_Thingol.add_constnames (t :: ts) [];
                val vars = reserved
                  |> intro_base_names
                      (is_none o syntax_const) deresolve consts
                  |> intro_vars ((fold o Code_Thingol.fold_varnames)
                      (insert (op =)) ts []);
              in concat [
                (Pretty.block o Pretty.commas)
                  (map (print_term is_pseudo_fun thm vars NOBR) ts),
                str "->",
                print_term is_pseudo_fun thm vars NOBR t
              ] end;
            fun print_eqns is_pseudo [((ts, t), (thm, _))] =
                  let
                    val consts = fold Code_Thingol.add_constnames (t :: ts) [];
                    val vars = reserved
                      |> intro_base_names
                          (is_none o syntax_const) deresolve consts
                      |> intro_vars ((fold o Code_Thingol.fold_varnames)
                          (insert (op =)) ts []);
                  in
                    concat (
                      (if is_pseudo then [str "()"]
                        else map (print_term is_pseudo_fun thm vars BR) ts)
                      @ str "="
                      @@ print_term is_pseudo_fun thm vars NOBR t
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
                          (is_none o syntax_const) deresolve consts;
                    val dummy_parms = (map str o aux_params vars o map (fst o fst)) eqs;
                  in
                    Pretty.block (
                      Pretty.breaks dummy_parms
                      @ Pretty.brk 1
                      :: str "="
                      :: Pretty.brk 1
                      :: str "match"
                      :: Pretty.brk 1
                      :: (Pretty.block o Pretty.commas) dummy_parms
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
                else Pretty.strs [definer, deresolve name];
          in pair
            (print_val_decl print_typscheme (name, vs_ty))
            (concat (
              prolog
              :: print_dict_args vs
              @| print_eqns (is_pseudo_fun name) eqs
            ))
          end
      | print_def is_pseudo_fun _ definer (ML_Instance (inst, ((class, (tyco, vs)), (superinsts, classparams)))) =
          let
            fun print_superinst (_, (classrel, dss)) =
              concat [
                (str o deresolve) classrel,
                str "=",
                print_dict is_pseudo_fun NOBR (DictConst dss)
              ];
            fun print_classparam ((classparam, c_inst), (thm, _)) =
              concat [
                (str o deresolve) classparam,
                str "=",
                print_app (K false) thm reserved NOBR (c_inst, [])
              ];
          in pair
            (print_val_decl print_dicttypscheme
              (inst, (vs, (class, tyco `%% map (ITyVar o fst) vs))))
            (concat (
              str definer
              :: (str o deresolve) inst
              :: print_dict_args vs
              @ str "="
              @@ brackets [
                enum_default "()" ";" "{" "}" (map print_superinst superinsts
                  @ map print_classparam classparams),
                str ":",
                print_tyco_expr NOBR (class, [tyco `%% map (ITyVar o fst) vs])
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
            val ty_p = print_tyco_expr NOBR (tyco, map (ITyVar o fst) vs);
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
     | print_stmt (ML_Class (class, (v, (superclasses, classparams)))) =
          let
            fun print_field s p = concat [str s, str ":", p];
            fun print_superclass_field (superclass, classrel) =
              print_field (deresolve classrel) (print_dicttyp (superclass, ITyVar v));
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
                  map print_superclass_field superclasses
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

fun print_ocaml_module name some_decls body = Pretty.chunks2 (
    Pretty.chunks (
      str ("module " ^ name ^ (if is_some some_decls then " : sig" else " ="))
      :: (the_list o Option.map (Pretty.indent 2 o Pretty.chunks)) some_decls
      @| (if is_some some_decls then str "end = struct" else str "struct")
    )
    :: body
    @| str ("end;; (*struct " ^ name ^ "*)")
  );

val literals_ocaml = let
  fun chr i =
    let
      val xs = string_of_int i;
      val ys = replicate_string (3 - length (explode xs)) "0";
    in "\\" ^ ys ^ xs end;
  fun char_ocaml c =
    let
      val i = ord c;
      val s = if i < 32 orelse i = 34 orelse i = 39 orelse i = 92 orelse i > 126
        then chr i else c
    in s end;
  fun bignum_ocaml k = if k <= 1073741823
    then "(Big_int.big_int_of_int " ^ string_of_int k ^ ")"
    else "(Big_int.big_int_of_string " ^ quote (string_of_int k) ^ ")"
in Literals {
  literal_char = enclose "'" "'" o char_ocaml,
  literal_string = quote o translate_string char_ocaml,
  literal_numeral = fn unbounded => fn k => if k >= 0 then
      if unbounded then bignum_ocaml k
      else string_of_int k
    else
      if unbounded then "(Big_int.minus_big_int " ^ bignum_ocaml (~ k) ^ ")"
      else (enclose "(" ")" o prefix "-" o string_of_int o op ~) k,
  literal_list = Pretty.enum ";" "[" "]",
  infix_cons = (6, "::")
} end;



(** SML/OCaml generic part **)

local

datatype ml_node =
    Dummy of string
  | Stmt of string * ml_stmt
  | Module of string * ((Name.context * Name.context) * ml_node Graph.T);

in

fun ml_node_of_program labelled_name module_name reserved raw_module_alias program =
  let
    val module_alias = if is_some module_name then K module_name else raw_module_alias;
    val reserved = Name.make_context reserved;
    val empty_module = ((reserved, reserved), Graph.empty);
    fun map_node [] f = f
      | map_node (m::ms) f =
          Graph.default_node (m, Module (m, empty_module))
          #> Graph.map_node m (fn (Module (module_name, (nsp, nodes))) =>
               Module (module_name, (nsp, map_node ms f nodes)));
    fun map_nsp_yield [] f (nsp, nodes) =
          let
            val (x, nsp') = f nsp
          in (x, (nsp', nodes)) end
      | map_nsp_yield (m::ms) f (nsp, nodes) =
          let
            val (x, nodes') =
              nodes
              |> Graph.default_node (m, Module (m, empty_module))
              |> Graph.map_node_yield m (fn Module (d_module_name, nsp_nodes) => 
                  let
                    val (x, nsp_nodes') = map_nsp_yield ms f nsp_nodes
                  in (x, Module (d_module_name, nsp_nodes')) end)
          in (x, (nsp, nodes')) end;
    fun map_nsp_fun_yield f (nsp_fun, nsp_typ) =
      let
        val (x, nsp_fun') = f nsp_fun
      in (x, (nsp_fun', nsp_typ)) end;
    fun map_nsp_typ_yield f (nsp_fun, nsp_typ) =
      let
        val (x, nsp_typ') = f nsp_typ
      in (x, (nsp_fun, nsp_typ')) end;
    val mk_name_module = mk_name_module reserved NONE module_alias program;
    fun mk_name_stmt upper name nsp =
      let
        val (_, base) = dest_name name;
        val base' = if upper then first_upper base else base;
        val ([base''], nsp') = Name.variants [base'] nsp;
      in (base'', nsp') end;
    fun ml_binding_of_stmt (name, Code_Thingol.Fun (_, (tysm as (vs, ty), raw_eqs))) =
          let
            val eqs = filter (snd o snd) raw_eqs;
            val (eqs', is_value) = if null (filter_out (null o snd) vs) then case eqs
               of [(([], t), thm)] => if (not o null o fst o Code_Thingol.unfold_fun) ty
                  then ([(([IVar (SOME "x")], t `$ IVar (SOME "x")), thm)], NONE)
                  else (eqs, SOME (name, member (op =) (Code_Thingol.add_constnames t []) name))
                | _ => (eqs, NONE)
              else (eqs, NONE)
          in (ML_Function (name, (tysm, eqs')), is_value) end
      | ml_binding_of_stmt (name, Code_Thingol.Classinst (stmt as ((_, (_, vs)), _))) =
          (ML_Instance (name, stmt), if forall (null o snd) vs then SOME (name, false) else NONE)
      | ml_binding_of_stmt (name, _) =
          error ("Binding block containing illegal statement: " ^ labelled_name name)
    fun add_fun (name, stmt) =
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
      in
        map_nsp_fun_yield (mk_name_stmt false name)
        #>> (fn name' => ([name'], ml_stmt))
      end;
    fun add_funs stmts =
      let
        val ml_stmt = ML_Funs (map_split ml_binding_of_stmt stmts |> (apsnd o map_filter o Option.map) fst);
      in
        fold_map (fn (name, _) => map_nsp_fun_yield (mk_name_stmt false name)) stmts
        #>> rpair ml_stmt
      end;
    fun add_datatypes stmts =
      fold_map
        (fn (name, Code_Thingol.Datatype (_, stmt)) =>
              map_nsp_typ_yield (mk_name_stmt false name) #>> rpair (SOME (name, stmt))
          | (name, Code_Thingol.Datatypecons _) =>
              map_nsp_fun_yield (mk_name_stmt true name) #>> rpair NONE
          | (name, _) =>
              error ("Datatype block containing illegal statement: " ^ labelled_name name)
        ) stmts
      #>> (split_list #> apsnd (map_filter I
        #> (fn [] => error ("Datatype block without data statement: "
                  ^ (commas o map (labelled_name o fst)) stmts)
             | stmts => ML_Datas stmts)));
    fun add_class stmts =
      fold_map
        (fn (name, Code_Thingol.Class (_, stmt)) =>
              map_nsp_typ_yield (mk_name_stmt false name) #>> rpair (SOME (name, stmt))
          | (name, Code_Thingol.Classrel _) =>
              map_nsp_fun_yield (mk_name_stmt false name) #>> rpair NONE
          | (name, Code_Thingol.Classparam _) =>
              map_nsp_fun_yield (mk_name_stmt false name) #>> rpair NONE
          | (name, _) =>
              error ("Class block containing illegal statement: " ^ labelled_name name)
        ) stmts
      #>> (split_list #> apsnd (map_filter I
        #> (fn [] => error ("Class block without class statement: "
                  ^ (commas o map (labelled_name o fst)) stmts)
             | [stmt] => ML_Class stmt)));
    fun add_stmts ([stmt as (name, Code_Thingol.Fun _)]) =
          add_fun stmt
      | add_stmts ((stmts as (_, Code_Thingol.Fun _)::_)) =
          add_funs stmts
      | add_stmts ((stmts as (_, Code_Thingol.Datatypecons _)::_)) =
          add_datatypes stmts
      | add_stmts ((stmts as (_, Code_Thingol.Datatype _)::_)) =
          add_datatypes stmts
      | add_stmts ((stmts as (_, Code_Thingol.Class _)::_)) =
          add_class stmts
      | add_stmts ((stmts as (_, Code_Thingol.Classrel _)::_)) =
          add_class stmts
      | add_stmts ((stmts as (_, Code_Thingol.Classparam _)::_)) =
          add_class stmts
      | add_stmts ([stmt as (_, Code_Thingol.Classinst _)]) =
          add_fun stmt
      | add_stmts ((stmts as (_, Code_Thingol.Classinst _)::_)) =
          add_funs stmts
      | add_stmts stmts = error ("Illegal mutual dependencies: " ^
          (commas o map (labelled_name o fst)) stmts);
    fun add_stmts' stmts nsp_nodes =
      let
        val names as (name :: names') = map fst stmts;
        val deps =
          []
          |> fold (fold (insert (op =)) o Graph.imm_succs program) names
          |> subtract (op =) names;
        val (module_names, _) = (split_list o map dest_name) names;
        val module_name = (the_single o distinct (op =) o map mk_name_module) module_names
          handle Empty =>
            error ("Different namespace prefixes for mutual dependencies:\n"
              ^ commas (map labelled_name names)
              ^ "\n"
              ^ commas module_names);
        val module_name_path = Long_Name.explode module_name;
        fun add_dep name name' =
          let
            val module_name' = (mk_name_module o fst o dest_name) name';
          in if module_name = module_name' then
            map_node module_name_path (Graph.add_edge (name, name'))
          else let
            val (common, (diff1 :: _, diff2 :: _)) = chop_prefix (op =)
              (module_name_path, Long_Name.explode module_name');
          in
            map_node common
              (fn node => Graph.add_edge_acyclic (diff1, diff2) node
                handle Graph.CYCLES _ => error ("Dependency "
                  ^ quote name ^ " -> " ^ quote name'
                  ^ " would result in module dependency cycle"))
          end end;
      in
        nsp_nodes
        |> map_nsp_yield module_name_path (add_stmts stmts)
        |-> (fn (base' :: bases', stmt') =>
           apsnd (map_node module_name_path (Graph.new_node (name, (Stmt (base', stmt')))
              #> fold2 (fn name' => fn base' =>
                   Graph.new_node (name', (Dummy base'))) names' bases')))
        |> apsnd (fold (fn name => fold (add_dep name) deps) names)
        |> apsnd (fold_product (curry (map_node module_name_path o Graph.add_edge)) names names)
      end;
    val (_, nodes) = empty_module
      |> fold add_stmts' (map (AList.make (Graph.get_node program))
          (rev (Graph.strong_conn program)));
    fun deresolver prefix name = 
      let
        val module_name = (fst o dest_name) name;
        val module_name' = (Long_Name.explode o mk_name_module) module_name;
        val (_, (_, remainder)) = chop_prefix (op =) (prefix, module_name');
        val stmt_name =
          nodes
          |> fold (fn name => fn node => case Graph.get_node node name
              of Module (_, (_, node)) => node) module_name'
          |> (fn node => case Graph.get_node node name of Stmt (stmt_name, _) => stmt_name
               | Dummy stmt_name => stmt_name);
      in
        Long_Name.implode (remainder @ [stmt_name])
      end handle Graph.UNDEF _ =>
        error ("Unknown statement name: " ^ labelled_name name);
  in (deresolver, nodes) end;

fun serialize_ml target compile print_module print_stmt raw_module_name with_signatures labelled_name
  reserved includes raw_module_alias _ syntax_tyco syntax_const program stmt_names destination =
  let
    val is_cons = Code_Thingol.is_cons program;
    val presentation_stmt_names = Code_Target.stmt_names_of_destination destination;
    val is_presentation = not (null presentation_stmt_names);
    val module_name = if is_presentation then SOME "Code" else raw_module_name;
    val (deresolver, nodes) = ml_node_of_program labelled_name module_name
      reserved raw_module_alias program;
    val reserved = make_vars reserved;
    fun print_node prefix (Dummy _) =
          NONE
      | print_node prefix (Stmt (_, stmt)) = if is_presentation andalso
          (null o filter (member (op =) presentation_stmt_names) o stmt_names_of) stmt
          then NONE
          else SOME (print_stmt labelled_name syntax_tyco syntax_const reserved is_cons (deresolver prefix) stmt)
      | print_node prefix (Module (module_name, (_, nodes))) =
          let
            val (decls, body) = print_nodes (prefix @ [module_name]) nodes;
            val p = if is_presentation then Pretty.chunks2 body
              else print_module module_name (if with_signatures then SOME decls else NONE) body;
          in SOME ([], p) end
    and print_nodes prefix nodes = (map_filter (print_node prefix o Graph.get_node nodes)
        o rev o flat o Graph.strong_conn) nodes
      |> split_list
      |> (fn (decls, body) => (flat decls, body))
    val stmt_names' = (map o try)
      (deresolver (if is_some module_name then the_list module_name else [])) stmt_names;
    val p = Pretty.chunks2 (map snd includes @ snd (print_nodes [] nodes));
  in
    Code_Target.mk_serialization target
      (case compile of SOME compile => SOME (compile o Code_Target.code_of_pretty) | NONE => NONE)
      (fn NONE => Code_Target.code_writeln | SOME file => File.write file o Code_Target.code_of_pretty)
      (rpair stmt_names' o Code_Target.code_of_pretty) p destination
  end;

end; (*local*)


(** for instrumentalization **)

fun evaluation_code_of thy target some_struct_name =
  let
    val serialize = if is_some some_struct_name then fn _ => fn [] =>
        serialize_ml target (SOME (K ())) print_sml_module print_sml_stmt some_struct_name true
      else fn _ => fn [] => 
        serialize_ml target (SOME (K ())) ((K o K) Pretty.chunks2) print_sml_stmt some_struct_name true;
  in Code_Target.serialize_custom thy (target, (serialize, literals_sml)) end;


(** Isar setup **)

fun isar_seri_sml module_name =
  Code_Target.parse_args (Scan.optional (Args.$$$ "no_signatures" >> K false) true
  >> (fn with_signatures => serialize_ml target_SML
      (SOME (use_text ML_Env.local_context (1, "generated code") false))
      print_sml_module print_sml_stmt module_name with_signatures));

fun isar_seri_ocaml module_name =
  Code_Target.parse_args (Scan.optional (Args.$$$ "no_signatures" >> K false) true
  >> (fn with_signatures => serialize_ml target_OCaml NONE
      print_ocaml_module print_ocaml_stmt module_name with_signatures));

val setup =
  Code_Target.add_target (target_SML, (isar_seri_sml, literals_sml))
  #> Code_Target.add_target (target_OCaml, (isar_seri_ocaml, literals_ocaml))
  #> Code_Target.add_syntax_tyco target_SML "fun" (SOME (2, fn print_typ => fn fxy => fn [ty1, ty2] =>
      brackify_infix (1, R) fxy [
        print_typ (INFX (1, X)) ty1,
        str "->",
        print_typ (INFX (1, R)) ty2
      ]))
  #> Code_Target.add_syntax_tyco target_OCaml "fun" (SOME (2, fn print_typ => fn fxy => fn [ty1, ty2] =>
      brackify_infix (1, R) fxy [
        print_typ (INFX (1, X)) ty1,
        str "->",
        print_typ (INFX (1, R)) ty2
      ]))
  #> fold (Code_Target.add_reserved target_SML) ML_Syntax.reserved_names
  #> fold (Code_Target.add_reserved target_SML)
      ["o" (*dictionary projections use it already*), "Fail", "div", "mod" (*standard infixes*)]
  #> fold (Code_Target.add_reserved target_OCaml) [
      "and", "as", "assert", "begin", "class",
      "constraint", "do", "done", "downto", "else", "end", "exception",
      "external", "false", "for", "fun", "function", "functor", "if",
      "in", "include", "inherit", "initializer", "lazy", "let", "match", "method",
      "module", "mutable", "new", "object", "of", "open", "or", "private", "rec",
      "sig", "struct", "then", "to", "true", "try", "type", "val",
      "virtual", "when", "while", "with"
    ]
  #> fold (Code_Target.add_reserved target_OCaml) ["failwith", "mod"];

end; (*struct*)
