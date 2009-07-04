(*  Title:      Tools/code/code_ml.ML
    Author:     Florian Haftmann, TU Muenchen

Serializer for SML and OCaml.
*)

signature CODE_ML =
sig
  val eval: string option -> string * (unit -> 'a) option ref
    -> ((term -> term) -> 'a -> 'a) -> theory -> term -> string list -> 'a
  val target_Eval: string
  val setup: theory -> theory
end;

structure Code_ML : CODE_ML =
struct

open Basic_Code_Thingol;
open Code_Printer;

infixr 5 @@;
infixr 5 @|;

val target_SML = "SML";
val target_OCaml = "OCaml";
val target_Eval = "Eval";

datatype ml_stmt =
    MLExc of string * int
  | MLVal of string * ((typscheme * iterm) * (thm * bool))
  | MLFuns of (string * (typscheme * ((iterm list * iterm) * (thm * bool)) list)) list * string list
  | MLDatas of (string * ((vname * sort) list * (string * itype list) list)) list
  | MLClass of string * (vname * ((class * string) list * (string * itype) list))
  | MLClassinst of string * ((class * (string * (vname * sort) list))
        * ((class * (string * (string * dict list list))) list
      * ((string * const) * (thm * bool)) list));

fun stmt_names_of (MLExc (name, _)) = [name]
  | stmt_names_of (MLVal (name, _)) = [name]
  | stmt_names_of (MLFuns (fs, _)) = map fst fs
  | stmt_names_of (MLDatas ds) = map fst ds
  | stmt_names_of (MLClass (name, _)) = [name]
  | stmt_names_of (MLClassinst (name, _)) = [name];


(** SML serailizer **)

fun pr_sml_stmt labelled_name syntax_tyco syntax_const reserved_names deresolve is_cons =
  let
    fun pr_dicts fxy ds =
      let
        fun pr_dictvar (v, (_, 1)) = Code_Printer.first_upper v ^ "_"
          | pr_dictvar (v, (i, _)) = Code_Printer.first_upper v ^ string_of_int (i+1) ^ "_";
        fun pr_proj [] p =
              p
          | pr_proj [p'] p =
              brackets [p', p]
          | pr_proj (ps as _ :: _) p =
              brackets [Pretty.enum " o" "(" ")" ps, p];
        fun pr_dict fxy (DictConst (inst, dss)) =
              brackify fxy ((str o deresolve) inst :: map (pr_dicts BR) dss)
          | pr_dict fxy (DictVar (classrels, v)) =
              pr_proj (map (str o deresolve) classrels) ((str o pr_dictvar) v)
      in case ds
       of [] => str "()"
        | [d] => pr_dict fxy d
        | _ :: _ => (Pretty.list "(" ")" o map (pr_dict NOBR)) ds
      end;
    fun pr_tyvar_dicts vs =
      vs
      |> map (fn (v, sort) => map_index (fn (i, _) =>
           DictVar ([], (v, (i, length sort)))) sort)
      |> map (pr_dicts BR);
    fun pr_tycoexpr fxy (tyco, tys) =
      let
        val tyco' = (str o deresolve) tyco
      in case map (pr_typ BR) tys
       of [] => tyco'
        | [p] => Pretty.block [p, Pretty.brk 1, tyco']
        | (ps as _::_) => Pretty.block [Pretty.list "(" ")" ps, Pretty.brk 1, tyco']
      end
    and pr_typ fxy (tyco `%% tys) = (case syntax_tyco tyco
         of NONE => pr_tycoexpr fxy (tyco, tys)
          | SOME (i, pr) => pr pr_typ fxy tys)
      | pr_typ fxy (ITyVar v) = str ("'" ^ v);
    fun pr_term is_closure thm vars fxy (IConst c) =
          pr_app is_closure thm vars fxy (c, [])
      | pr_term is_closure thm vars fxy (IVar NONE) =
          str "_"
      | pr_term is_closure thm vars fxy (IVar (SOME v)) =
          str (Code_Printer.lookup_var vars v)
      | pr_term is_closure thm vars fxy (t as t1 `$ t2) =
          (case Code_Thingol.unfold_const_app t
           of SOME c_ts => pr_app is_closure thm vars fxy c_ts
            | NONE => brackify fxy
               [pr_term is_closure thm vars NOBR t1, pr_term is_closure thm vars BR t2])
      | pr_term is_closure thm vars fxy (t as _ `|=> _) =
          let
            val (binds, t') = Code_Thingol.unfold_pat_abs t;
            fun pr (pat, ty) =
              pr_bind is_closure thm NOBR pat
              #>> (fn p => concat [str "fn", p, str "=>"]);
            val (ps, vars') = fold_map pr binds vars;
          in brackets (ps @ [pr_term is_closure thm vars' NOBR t']) end
      | pr_term is_closure thm vars fxy (ICase (cases as (_, t0))) =
          (case Code_Thingol.unfold_const_app t0
           of SOME (c_ts as ((c, _), _)) => if is_none (syntax_const c)
                then pr_case is_closure thm vars fxy cases
                else pr_app is_closure thm vars fxy c_ts
            | NONE => pr_case is_closure thm vars fxy cases)
    and pr_app' is_closure thm vars (app as ((c, ((_, iss), tys)), ts)) =
      if is_cons c then
        let
          val k = length tys
        in if k < 2 then 
          (str o deresolve) c :: map (pr_term is_closure thm vars BR) ts
        else if k = length ts then
          [(str o deresolve) c, Pretty.enum "," "(" ")" (map (pr_term is_closure thm vars NOBR) ts)]
        else [pr_term is_closure thm vars BR (Code_Thingol.eta_expand k app)] end
      else if is_closure c
        then (str o deresolve) c @@ str "()"
      else
        (str o deresolve) c
          :: (map (pr_dicts BR) o filter_out null) iss @ map (pr_term is_closure thm vars BR) ts
    and pr_app is_closure thm vars = gen_pr_app (pr_app' is_closure) (pr_term is_closure)
      syntax_const thm vars
    and pr_bind is_closure = gen_pr_bind (pr_term is_closure)
    and pr_case is_closure thm vars fxy (cases as ((_, [_]), _)) =
          let
            val (binds, body) = Code_Thingol.unfold_let (ICase cases);
            fun pr ((pat, ty), t) vars =
              vars
              |> pr_bind is_closure thm NOBR pat
              |>> (fn p => semicolon [str "val", p, str "=", pr_term is_closure thm vars NOBR t])
            val (ps, vars') = fold_map pr binds vars;
          in
            Pretty.chunks [
              [str ("let"), Pretty.fbrk, Pretty.chunks ps] |> Pretty.block,
              [str ("in"), Pretty.fbrk, pr_term is_closure thm vars' NOBR body] |> Pretty.block,
              str ("end")
            ]
          end
      | pr_case is_closure thm vars fxy (((t, ty), clause :: clauses), _) =
          let
            fun pr delim (pat, body) =
              let
                val (p, vars') = pr_bind is_closure thm NOBR pat vars;
              in
                concat [str delim, p, str "=>", pr_term is_closure thm vars' NOBR body]
              end;
          in
            brackets (
              str "case"
              :: pr_term is_closure thm vars NOBR t
              :: pr "of" clause
              :: map (pr "|") clauses
            )
          end
      | pr_case is_closure thm vars fxy ((_, []), _) =
          (concat o map str) ["raise", "Fail", "\"empty case\""];
    fun pr_stmt (MLExc (name, n)) =
          let
            val exc_str =
              (ML_Syntax.print_string o Long_Name.base_name o Long_Name.qualifier) name;
          in
            (concat o map str) (
              (if n = 0 then "val" else "fun")
              :: deresolve name
              :: replicate n "_"
              @ "="
              :: "raise"
              :: "Fail"
              @@ exc_str
            )
          end
      | pr_stmt (MLVal (name, (((vs, ty), t), (thm, _)))) =
          let
            val consts = map_filter
              (fn c => if (is_some o syntax_const) c
                then NONE else (SOME o Long_Name.base_name o deresolve) c)
                (Code_Thingol.add_constnames t []);
            val vars = reserved_names
              |> Code_Printer.intro_vars consts;
          in
            concat [
              str "val",
              (str o deresolve) name,
              str ":",
              pr_typ NOBR ty,
              str "=",
              pr_term (K false) thm vars NOBR t
            ]
          end
      | pr_stmt (MLFuns (funn :: funns, pseudo_funs)) =
          let
            fun pr_funn definer (name, ((vs, ty), eqs as eq :: eqs')) =
              let
                val vs_dict = filter_out (null o snd) vs;
                val shift = if null eqs' then I else
                  map (Pretty.block o single o Pretty.block o single);
                fun pr_eq definer ((ts, t), (thm, _)) =
                  let
                    val consts = map_filter
                      (fn c => if (is_some o syntax_const) c
                        then NONE else (SOME o Long_Name.base_name o deresolve) c)
                        (fold Code_Thingol.add_constnames (t :: ts) []);
                    val vars = reserved_names
                      |> Code_Printer.intro_vars consts
                      |> Code_Printer.intro_vars ((fold o Code_Thingol.fold_varnames)
                           (insert (op =)) ts []);
                  in
                    concat (
                      str definer
                      :: (str o deresolve) name
                      :: (if member (op =) pseudo_funs name then [str "()"]
                          else pr_tyvar_dicts vs_dict
                            @ map (pr_term (member (op =) pseudo_funs) thm vars BR) ts)
                      @ str "="
                      @@ pr_term (member (op =) pseudo_funs) thm vars NOBR t
                    )
                  end
              in
                (Pretty.block o Pretty.fbreaks o shift) (
                  pr_eq definer eq
                  :: map (pr_eq "|") eqs'
                )
              end;
            fun pr_pseudo_fun name = concat [
                str "val",
                (str o deresolve) name,
                str "=",
                (str o deresolve) name,
                str "();"
              ];
            val (ps, p) = split_last (pr_funn "fun" funn :: map (pr_funn "and") funns);
            val pseudo_ps = map pr_pseudo_fun pseudo_funs;
          in Pretty.chunks (ps @ Pretty.block ([p, str ";"]) :: pseudo_ps) end
     | pr_stmt (MLDatas (datas as (data :: datas'))) =
          let
            fun pr_co (co, []) =
                  str (deresolve co)
              | pr_co (co, tys) =
                  concat [
                    str (deresolve co),
                    str "of",
                    Pretty.enum " *" "" "" (map (pr_typ (INFX (2, X))) tys)
                  ];
            fun pr_data definer (tyco, (vs, [])) =
                  concat (
                    str definer
                    :: pr_tycoexpr NOBR (tyco, map (ITyVar o fst) vs)
                    :: str "="
                    @@ str "EMPTY__" 
                  )
              | pr_data definer (tyco, (vs, cos)) =
                  concat (
                    str definer
                    :: pr_tycoexpr NOBR (tyco, map (ITyVar o fst) vs)
                    :: str "="
                    :: separate (str "|") (map pr_co cos)
                  );
            val (ps, p) = split_last
              (pr_data "datatype" data :: map (pr_data "and") datas');
          in Pretty.chunks (ps @| Pretty.block ([p, str ";"])) end
     | pr_stmt (MLClass (class, (v, (superclasses, classparams)))) =
          let
            val w = Code_Printer.first_upper v ^ "_";
            fun pr_superclass_field (class, classrel) =
              (concat o map str) [
                deresolve classrel, ":", "'" ^ v, deresolve class
              ];
            fun pr_classparam_field (classparam, ty) =
              concat [
                (str o deresolve) classparam, str ":", pr_typ NOBR ty
              ];
            fun pr_classparam_proj (classparam, _) =
              semicolon [
                str "fun",
                (str o deresolve) classparam,
                Pretty.enclose "(" ")" [str (w ^ ":'" ^ v ^ " " ^ deresolve class)],
                str "=",
                str ("#" ^ deresolve classparam),
                str w
              ];
            fun pr_superclass_proj (_, classrel) =
              semicolon [
                str "fun",
                (str o deresolve) classrel,
                Pretty.enclose "(" ")" [str (w ^ ":'" ^ v ^ " " ^ deresolve class)],
                str "=",
                str ("#" ^ deresolve classrel),
                str w
              ];
          in
            Pretty.chunks (
              concat [
                str ("type '" ^ v),
                (str o deresolve) class,
                str "=",
                Pretty.enum "," "{" "};" (
                  map pr_superclass_field superclasses @ map pr_classparam_field classparams
                )
              ]
              :: map pr_superclass_proj superclasses
              @ map pr_classparam_proj classparams
            )
          end
     | pr_stmt (MLClassinst (inst, ((class, (tyco, arity)), (superarities, classparam_insts)))) =
          let
            fun pr_superclass (_, (classrel, dss)) =
              concat [
                (str o Long_Name.base_name o deresolve) classrel,
                str "=",
                pr_dicts NOBR [DictConst dss]
              ];
            fun pr_classparam ((classparam, c_inst), (thm, _)) =
              concat [
                (str o Long_Name.base_name o deresolve) classparam,
                str "=",
                pr_app (K false) thm reserved_names NOBR (c_inst, [])
              ];
          in
            semicolon ([
              str (if null arity then "val" else "fun"),
              (str o deresolve) inst ] @
              pr_tyvar_dicts arity @ [
              str "=",
              Pretty.enum "," "{" "}"
                (map pr_superclass superarities @ map pr_classparam classparam_insts),
              str ":",
              pr_tycoexpr NOBR (class, [tyco `%% map (ITyVar o fst) arity])
            ])
          end;
  in pr_stmt end;

fun pr_sml_module name content =
  Pretty.chunks (
    str ("structure " ^ name ^ " = ")
    :: str "struct"
    :: str ""
    :: content
    @ str ""
    @@ str ("end; (*struct " ^ name ^ "*)")
  );

val literals_sml = Literals {
  literal_char = prefix "#" o quote o ML_Syntax.print_char,
  literal_string = quote o translate_string ML_Syntax.print_char,
  literal_numeral = fn unbounded => fn k =>
    if unbounded then "(" ^ string_of_int k ^ " : IntInf.int)"
    else string_of_int k,
  literal_list = Pretty.enum "," "[" "]",
  infix_cons = (7, "::")
};


(** OCaml serializer **)

fun pr_ocaml_stmt labelled_name syntax_tyco syntax_const reserved_names deresolve is_cons =
  let
    fun pr_dicts fxy ds =
      let
        fun pr_dictvar (v, (_, 1)) = "_" ^ Code_Printer.first_upper v
          | pr_dictvar (v, (i, _)) = "_" ^ Code_Printer.first_upper v ^ string_of_int (i+1);
        fun pr_proj ps p =
          fold_rev (fn p2 => fn p1 => Pretty.block [p1, str ".", str p2]) ps p
        fun pr_dict fxy (DictConst (inst, dss)) =
              brackify fxy ((str o deresolve) inst :: map (pr_dicts BR) dss)
          | pr_dict fxy (DictVar (classrels, v)) =
              pr_proj (map deresolve classrels) ((str o pr_dictvar) v)
      in case ds
       of [] => str "()"
        | [d] => pr_dict fxy d
        | _ :: _ => (Pretty.list "(" ")" o map (pr_dict NOBR)) ds
      end;
    fun pr_tyvar_dicts vs =
      vs
      |> map (fn (v, sort) => map_index (fn (i, _) =>
           DictVar ([], (v, (i, length sort)))) sort)
      |> map (pr_dicts BR);
    fun pr_tycoexpr fxy (tyco, tys) =
      let
        val tyco' = (str o deresolve) tyco
      in case map (pr_typ BR) tys
       of [] => tyco'
        | [p] => Pretty.block [p, Pretty.brk 1, tyco']
        | (ps as _::_) => Pretty.block [Pretty.list "(" ")" ps, Pretty.brk 1, tyco']
      end
    and pr_typ fxy (tyco `%% tys) = (case syntax_tyco tyco
         of NONE => pr_tycoexpr fxy (tyco, tys)
          | SOME (i, pr) => pr pr_typ fxy tys)
      | pr_typ fxy (ITyVar v) = str ("'" ^ v);
    fun pr_term is_closure thm vars fxy (IConst c) =
          pr_app is_closure thm vars fxy (c, [])
      | pr_term is_closure thm vars fxy (IVar NONE) =
          str "_"
      | pr_term is_closure thm vars fxy (IVar (SOME v)) =
          str (Code_Printer.lookup_var vars v)
      | pr_term is_closure thm vars fxy (t as t1 `$ t2) =
          (case Code_Thingol.unfold_const_app t
           of SOME c_ts => pr_app is_closure thm vars fxy c_ts
            | NONE =>
                brackify fxy [pr_term is_closure thm vars NOBR t1, pr_term is_closure thm vars BR t2])
      | pr_term is_closure thm vars fxy (t as _ `|=> _) =
          let
            val (binds, t') = Code_Thingol.unfold_pat_abs t;
            val (ps, vars') = fold_map (pr_bind is_closure thm BR o fst) binds vars;
          in brackets (str "fun" :: ps @ str "->" @@ pr_term is_closure thm vars' NOBR t') end
      | pr_term is_closure thm vars fxy (ICase (cases as (_, t0))) = (case Code_Thingol.unfold_const_app t0
           of SOME (c_ts as ((c, _), _)) => if is_none (syntax_const c)
                then pr_case is_closure thm vars fxy cases
                else pr_app is_closure thm vars fxy c_ts
            | NONE => pr_case is_closure thm vars fxy cases)
    and pr_app' is_closure thm vars (app as ((c, ((_, iss), tys)), ts)) =
      if is_cons c then
        if length tys = length ts
        then case ts
         of [] => [(str o deresolve) c]
          | [t] => [(str o deresolve) c, pr_term is_closure thm vars BR t]
          | _ => [(str o deresolve) c, Pretty.enum "," "(" ")"
                    (map (pr_term is_closure thm vars NOBR) ts)]
        else [pr_term is_closure thm vars BR (Code_Thingol.eta_expand (length tys) app)]
      else if is_closure c
        then (str o deresolve) c @@ str "()"
      else (str o deresolve) c
        :: ((map (pr_dicts BR) o filter_out null) iss @ map (pr_term is_closure thm vars BR) ts)
    and pr_app is_closure = gen_pr_app (pr_app' is_closure) (pr_term is_closure)
      syntax_const
    and pr_bind is_closure = gen_pr_bind (pr_term is_closure)
    and pr_case is_closure thm vars fxy (cases as ((_, [_]), _)) =
          let
            val (binds, body) = Code_Thingol.unfold_let (ICase cases);
            fun pr ((pat, ty), t) vars =
              vars
              |> pr_bind is_closure thm NOBR pat
              |>> (fn p => concat
                  [str "let", p, str "=", pr_term is_closure thm vars NOBR t, str "in"])
            val (ps, vars') = fold_map pr binds vars;
          in
            brackify_block fxy (Pretty.chunks ps) []
              (pr_term is_closure thm vars' NOBR body)
          end
      | pr_case is_closure thm vars fxy (((t, ty), clause :: clauses), _) =
          let
            fun pr delim (pat, body) =
              let
                val (p, vars') = pr_bind is_closure thm NOBR pat vars;
              in concat [str delim, p, str "->", pr_term is_closure thm vars' NOBR body] end;
          in
            brackets (
              str "match"
              :: pr_term is_closure thm vars NOBR t
              :: pr "with" clause
              :: map (pr "|") clauses
            )
          end
      | pr_case is_closure thm vars fxy ((_, []), _) =
          (concat o map str) ["failwith", "\"empty case\""];
    fun fish_params vars eqs =
      let
        fun fish_param _ (w as SOME _) = w
          | fish_param (IVar (SOME v)) NONE = SOME v
          | fish_param _ NONE = NONE;
        fun fillup_param _ (_, SOME v) = v
          | fillup_param x (i, NONE) = x ^ string_of_int i;
        val fished1 = fold (map2 fish_param) eqs (replicate (length (hd eqs)) NONE);
        val x = Name.variant (map_filter I fished1) "x";
        val fished2 = map_index (fillup_param x) fished1;
        val (fished3, _) = Name.variants fished2 Name.context;
        val vars' = Code_Printer.intro_vars fished3 vars;
      in map (Code_Printer.lookup_var vars') fished3 end;
    fun pr_stmt (MLExc (name, n)) =
          let
            val exc_str =
              (ML_Syntax.print_string o Long_Name.base_name o Long_Name.qualifier) name;
          in
            (concat o map str) (
              "let"
              :: deresolve name
              :: replicate n "_"
              @ "="
              :: "failwith"
              @@ exc_str
            )
          end
      | pr_stmt (MLVal (name, (((vs, ty), t), (thm, _)))) =
          let
            val consts = map_filter
              (fn c => if (is_some o syntax_const) c
                then NONE else (SOME o Long_Name.base_name o deresolve) c)
                (Code_Thingol.add_constnames t []);
            val vars = reserved_names
              |> Code_Printer.intro_vars consts;
          in
            concat [
              str "let",
              (str o deresolve) name,
              str ":",
              pr_typ NOBR ty,
              str "=",
              pr_term (K false) thm vars NOBR t
            ]
          end
      | pr_stmt (MLFuns (funn :: funns, pseudo_funs)) =
          let
            fun pr_eq ((ts, t), (thm, _)) =
              let
                val consts = map_filter
                  (fn c => if (is_some o syntax_const) c
                    then NONE else (SOME o Long_Name.base_name o deresolve) c)
                    (fold Code_Thingol.add_constnames (t :: ts) []);
                val vars = reserved_names
                  |> Code_Printer.intro_vars consts
                  |> Code_Printer.intro_vars ((fold o Code_Thingol.fold_varnames)
                      (insert (op =)) ts []);
              in concat [
                (Pretty.block o Pretty.commas)
                  (map (pr_term (member (op =) pseudo_funs) thm vars NOBR) ts),
                str "->",
                pr_term (member (op =) pseudo_funs) thm vars NOBR t
              ] end;
            fun pr_eqs is_pseudo [((ts, t), (thm, _))] =
                  let
                    val consts = map_filter
                      (fn c => if (is_some o syntax_const) c
                        then NONE else (SOME o Long_Name.base_name o deresolve) c)
                        (fold Code_Thingol.add_constnames (t :: ts) []);
                    val vars = reserved_names
                      |> Code_Printer.intro_vars consts
                      |> Code_Printer.intro_vars ((fold o Code_Thingol.fold_varnames)
                          (insert (op =)) ts []);
                  in
                    concat (
                      (if is_pseudo then [str "()"]
                        else map (pr_term (member (op =) pseudo_funs) thm vars BR) ts)
                      @ str "="
                      @@ pr_term (member (op =) pseudo_funs) thm vars NOBR t
                    )
                  end
              | pr_eqs _ (eqs as (eq as (([_], _), _)) :: eqs') =
                  Pretty.block (
                    str "="
                    :: Pretty.brk 1
                    :: str "function"
                    :: Pretty.brk 1
                    :: pr_eq eq
                    :: maps (append [Pretty.fbrk, str "|", Pretty.brk 1]
                          o single o pr_eq) eqs'
                  )
              | pr_eqs _ (eqs as eq :: eqs') =
                  let
                    val consts = map_filter
                      (fn c => if (is_some o syntax_const) c
                        then NONE else (SOME o Long_Name.base_name o deresolve) c)
                        (fold Code_Thingol.add_constnames (map (snd o fst) eqs) []);
                    val vars = reserved_names
                      |> Code_Printer.intro_vars consts;
                    val dummy_parms = (map str o fish_params vars o map (fst o fst)) eqs;
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
                      :: pr_eq eq
                      :: maps (append [Pretty.fbrk, str "|", Pretty.brk 1]
                           o single o pr_eq) eqs'
                    )
                  end;
            fun pr_funn definer (name, ((vs, ty), eqs)) =
              concat (
                str definer
                :: (str o deresolve) name
                :: pr_tyvar_dicts (filter_out (null o snd) vs)
                @| pr_eqs (member (op =) pseudo_funs name) eqs
              );
            fun pr_pseudo_fun name = concat [
                str "let",
                (str o deresolve) name,
                str "=",
                (str o deresolve) name,
                str "();;"
              ];
            val (ps, p) = split_last (pr_funn "fun" funn :: map (pr_funn "and") funns);
            val (ps, p) = split_last
              (pr_funn "let rec" funn :: map (pr_funn "and") funns);
            val pseudo_ps = map pr_pseudo_fun pseudo_funs;
          in Pretty.chunks (ps @ Pretty.block ([p, str ";;"]) :: pseudo_ps) end
     | pr_stmt (MLDatas (datas as (data :: datas'))) =
          let
            fun pr_co (co, []) =
                  str (deresolve co)
              | pr_co (co, tys) =
                  concat [
                    str (deresolve co),
                    str "of",
                    Pretty.enum " *" "" "" (map (pr_typ (INFX (2, X))) tys)
                  ];
            fun pr_data definer (tyco, (vs, [])) =
                  concat (
                    str definer
                    :: pr_tycoexpr NOBR (tyco, map (ITyVar o fst) vs)
                    :: str "="
                    @@ str "EMPTY_"
                  )
              | pr_data definer (tyco, (vs, cos)) =
                  concat (
                    str definer
                    :: pr_tycoexpr NOBR (tyco, map (ITyVar o fst) vs)
                    :: str "="
                    :: separate (str "|") (map pr_co cos)
                  );
            val (ps, p) = split_last
              (pr_data "type" data :: map (pr_data "and") datas');
          in Pretty.chunks (ps @| Pretty.block ([p, str ";;"])) end
     | pr_stmt (MLClass (class, (v, (superclasses, classparams)))) =
          let
            val w = "_" ^ Code_Printer.first_upper v;
            fun pr_superclass_field (class, classrel) =
              (concat o map str) [
                deresolve classrel, ":", "'" ^ v, deresolve class
              ];
            fun pr_classparam_field (classparam, ty) =
              concat [
                (str o deresolve) classparam, str ":", pr_typ NOBR ty
              ];
            fun pr_classparam_proj (classparam, _) =
              concat [
                str "let",
                (str o deresolve) classparam,
                str w,
                str "=",
                str (w ^ "." ^ deresolve classparam ^ ";;")
              ];
          in Pretty.chunks (
            concat [
              str ("type '" ^ v),
              (str o deresolve) class,
              str "=",
              enum_default "unit;;" ";" "{" "};;" (
                map pr_superclass_field superclasses
                @ map pr_classparam_field classparams
              )
            ]
            :: map pr_classparam_proj classparams
          ) end
     | pr_stmt (MLClassinst (inst, ((class, (tyco, arity)), (superarities, classparam_insts)))) =
          let
            fun pr_superclass (_, (classrel, dss)) =
              concat [
                (str o deresolve) classrel,
                str "=",
                pr_dicts NOBR [DictConst dss]
              ];
            fun pr_classparam_inst ((classparam, c_inst), (thm, _)) =
              concat [
                (str o deresolve) classparam,
                str "=",
                pr_app (K false) thm reserved_names NOBR (c_inst, [])
              ];
          in
            concat (
              str "let"
              :: (str o deresolve) inst
              :: pr_tyvar_dicts arity
              @ str "="
              @@ (Pretty.enclose "(" ");;" o Pretty.breaks) [
                enum_default "()" ";" "{" "}" (map pr_superclass superarities
                  @ map pr_classparam_inst classparam_insts),
                str ":",
                pr_tycoexpr NOBR (class, [tyco `%% map (ITyVar o fst) arity])
              ]
            )
          end;
  in pr_stmt end;

fun pr_ocaml_module name content =
  Pretty.chunks (
    str ("module " ^ name ^ " = ")
    :: str "struct"
    :: str ""
    :: content
    @ str ""
    @@ str ("end;; (*struct " ^ name ^ "*)")
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

fun ml_node_of_program labelled_name module_name reserved_names raw_module_alias program =
  let
    val module_alias = if is_some module_name then K module_name else raw_module_alias;
    val reserved_names = Name.make_context reserved_names;
    val empty_module = ((reserved_names, reserved_names), Graph.empty);
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
    val mk_name_module = Code_Printer.mk_name_module reserved_names NONE module_alias program;
    fun mk_name_stmt upper name nsp =
      let
        val (_, base) = Code_Printer.dest_name name;
        val base' = if upper then Code_Printer.first_upper base else base;
        val ([base''], nsp') = Name.variants [base'] nsp;
      in (base'', nsp') end;
    fun rearrange_fun name (tysm as (vs, ty), raw_eqs) =
      let
        val eqs = filter (snd o snd) raw_eqs;
        val (eqs', is_value) = if null (filter_out (null o snd) vs) then case eqs
         of [(([], t), thm)] => if (not o null o fst o Code_Thingol.unfold_fun) ty
            then ([(([IVar (SOME "x")], t `$ IVar (SOME "x")), thm)], false)
            else (eqs, not (member (op =) (Code_Thingol.add_constnames t []) name))
          | _ => (eqs, false)
          else (eqs, false)
      in ((name, (tysm, eqs')), is_value) end;
    fun check_kind [((name, (tysm, [(([], t), thm)])), true)] = MLVal (name, ((tysm, t), thm))
      | check_kind [((name, ((vs, ty), [])), _)] =
          MLExc (name, (length o filter_out (null o snd)) vs + (length o fst o Code_Thingol.unfold_fun) ty)
      | check_kind funns =
          MLFuns (map fst funns, map_filter
            (fn ((name, ((vs, _), [(([], _), _)])), _) =>
                  if null (filter_out (null o snd) vs) then SOME name else NONE
              | _ => NONE) funns);
    fun add_funs stmts = fold_map
        (fn (name, Code_Thingol.Fun (_, stmt)) =>
              map_nsp_fun_yield (mk_name_stmt false name)
              #>> rpair (rearrange_fun name stmt)
          | (name, _) =>
              error ("Function block containing illegal statement: " ^ labelled_name name)
        ) stmts
      #>> (split_list #> apsnd check_kind);
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
             | stmts => MLDatas stmts)));
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
             | [stmt] => MLClass stmt)));
    fun add_inst [(name, Code_Thingol.Classinst stmt)] =
      map_nsp_fun_yield (mk_name_stmt false name)
      #>> (fn base => ([base], MLClassinst (name, stmt)));
    fun add_stmts ((stmts as (_, Code_Thingol.Fun _)::_)) =
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
      | add_stmts ((stmts as [(_, Code_Thingol.Classinst _)])) =
          add_inst stmts
      | add_stmts stmts = error ("Illegal mutual dependencies: " ^
          (commas o map (labelled_name o fst)) stmts);
    fun add_stmts' stmts nsp_nodes =
      let
        val names as (name :: names') = map fst stmts;
        val deps =
          []
          |> fold (fold (insert (op =)) o Graph.imm_succs program) names
          |> subtract (op =) names;
        val (module_names, _) = (split_list o map Code_Printer.dest_name) names;
        val module_name = (the_single o distinct (op =) o map mk_name_module) module_names
          handle Empty =>
            error ("Different namespace prefixes for mutual dependencies:\n"
              ^ commas (map labelled_name names)
              ^ "\n"
              ^ commas module_names);
        val module_name_path = Long_Name.explode module_name;
        fun add_dep name name' =
          let
            val module_name' = (mk_name_module o fst o Code_Printer.dest_name) name';
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
        val module_name = (fst o Code_Printer.dest_name) name;
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

fun serialize_ml target compile pr_module pr_stmt raw_module_name labelled_name reserved_names includes raw_module_alias
  _ syntax_tyco syntax_const program stmt_names destination =
  let
    val is_cons = Code_Thingol.is_cons program;
    val present_stmt_names = Code_Target.stmt_names_of_destination destination;
    val is_present = not (null present_stmt_names);
    val module_name = if is_present then SOME "Code" else raw_module_name;
    val (deresolver, nodes) = ml_node_of_program labelled_name module_name
      reserved_names raw_module_alias program;
    val reserved_names = Code_Printer.make_vars reserved_names;
    fun pr_node prefix (Dummy _) =
          NONE
      | pr_node prefix (Stmt (_, stmt)) = if is_present andalso
          (null o filter (member (op =) present_stmt_names) o stmt_names_of) stmt
          then NONE
          else SOME
            (pr_stmt labelled_name syntax_tyco syntax_const reserved_names
              (deresolver prefix) is_cons stmt)
      | pr_node prefix (Module (module_name, (_, nodes))) =
          separate (str "")
            ((map_filter (pr_node (prefix @ [module_name]) o Graph.get_node nodes)
              o rev o flat o Graph.strong_conn) nodes)
          |> (if is_present then Pretty.chunks else pr_module module_name)
          |> SOME;
    val stmt_names' = (map o try)
      (deresolver (if is_some module_name then the_list module_name else [])) stmt_names;
    val p = Pretty.chunks (separate (str "") (map snd includes @ (map_filter
      (pr_node [] o Graph.get_node nodes) o rev o flat o Graph.strong_conn) nodes));
  in
    Code_Target.mk_serialization target
      (case compile of SOME compile => SOME (compile o Code_Target.code_of_pretty) | NONE => NONE)
      (fn NONE => Code_Target.code_writeln | SOME file => File.write file o Code_Target.code_of_pretty)
      (rpair stmt_names' o Code_Target.code_of_pretty) p destination
  end;

end; (*local*)


(** ML (system language) code for evaluation and instrumentalization **)

fun eval_code_of some_target thy = Code_Target.serialize_custom thy (the_default target_Eval some_target,
    (fn _ => fn [] => serialize_ml target_SML (SOME (K ())) (K Pretty.chunks) pr_sml_stmt (SOME ""),
  literals_sml));


(* evaluation *)

fun eval some_target reff postproc thy t args =
  let
    val ctxt = ProofContext.init thy;
    fun evaluator naming program ((_, (_, ty)), t) deps =
      let
        val _ = if Code_Thingol.contains_dictvar t then
          error "Term to be evaluated contains free dictionaries" else ();
        val value_name = "Value.VALUE.value"
        val program' = program
          |> Graph.new_node (value_name,
              Code_Thingol.Fun (Term.dummy_patternN, (([], ty), [(([], t), (Drule.dummy_thm, true))])))
          |> fold (curry Graph.add_edge value_name) deps;
        val (value_code, [SOME value_name']) = eval_code_of some_target thy naming program' [value_name];
        val sml_code = "let\n" ^ value_code ^ "\nin " ^ value_name'
          ^ space_implode " " (map (enclose "(" ")") args) ^ " end";
      in ML_Context.evaluate ctxt false reff sml_code end;
  in Code_Thingol.eval thy I postproc evaluator t end;


(* instrumentalization by antiquotation *)

local

structure CodeAntiqData = ProofDataFun
(
  type T = (string list * string list) * (bool * (string
    * (string * ((string * string) list * (string * string) list)) lazy));
  fun init _ = (([], []), (true, ("", Lazy.value ("", ([], [])))));
);

val is_first_occ = fst o snd o CodeAntiqData.get;

fun delayed_code thy tycos consts () =
  let
    val (consts', (naming, program)) = Code_Thingol.consts_program thy consts;
    val tycos' = map (the o Code_Thingol.lookup_tyco naming) tycos;
    val (ml_code, target_names) = eval_code_of NONE thy naming program (consts' @ tycos');
    val (consts'', tycos'') = chop (length consts') target_names;
    val consts_map = map2 (fn const => fn NONE =>
        error ("Constant " ^ (quote o Code.string_of_const thy) const
          ^ "\nhas a user-defined serialization")
      | SOME const'' => (const, const'')) consts consts''
    val tycos_map = map2 (fn tyco => fn NONE =>
        error ("Type " ^ (quote o Sign.extern_type thy) tyco
          ^ "\nhas a user-defined serialization")
      | SOME tyco'' => (tyco, tyco'')) tycos tycos'';
  in (ml_code, (tycos_map, consts_map)) end;

fun register_code new_tycos new_consts ctxt =
  let
    val ((tycos, consts), (_, (struct_name, _))) = CodeAntiqData.get ctxt;
    val tycos' = fold (insert (op =)) new_tycos tycos;
    val consts' = fold (insert (op =)) new_consts consts;
    val (struct_name', ctxt') = if struct_name = ""
      then ML_Antiquote.variant "Code" ctxt
      else (struct_name, ctxt);
    val acc_code = Lazy.lazy (delayed_code (ProofContext.theory_of ctxt) tycos' consts');
  in CodeAntiqData.put ((tycos', consts'), (false, (struct_name', acc_code))) ctxt' end;

fun register_const const = register_code [] [const];

fun register_datatype tyco constrs = register_code [tyco] constrs;

fun print_const const all_struct_name tycos_map consts_map =
  (Long_Name.append all_struct_name o the o AList.lookup (op =) consts_map) const;

fun print_datatype tyco constrs all_struct_name tycos_map consts_map =
  let
    val upperize = implode o nth_map 0 Symbol.to_ascii_upper o explode;
    fun check_base name name'' =
      if upperize (Long_Name.base_name name) = upperize name''
      then () else error ("Name as printed " ^ quote name''
        ^ "\ndiffers from logical base name " ^ quote (Long_Name.base_name name) ^ "; sorry.");
    val tyco'' = (the o AList.lookup (op =) tycos_map) tyco;
    val constrs'' = map (the o AList.lookup (op =) consts_map) constrs;
    val _ = check_base tyco tyco'';
    val _ = map2 check_base constrs constrs'';
  in "datatype " ^ tyco'' ^ " = datatype " ^ Long_Name.append all_struct_name tyco'' end;

fun print_code struct_name is_first print_it ctxt =
  let
    val (_, (_, (struct_code_name, acc_code))) = CodeAntiqData.get ctxt;
    val (raw_ml_code, (tycos_map, consts_map)) = Lazy.force acc_code;
    val ml_code = if is_first then "\nstructure " ^ struct_code_name
        ^ " =\nstruct\n\n" ^ raw_ml_code ^ "\nend;\n\n"
      else "";
    val all_struct_name = Long_Name.append struct_name struct_code_name;
  in (ml_code, print_it all_struct_name tycos_map consts_map) end;

in

fun ml_code_antiq raw_const {struct_name, background} =
  let
    val const = Code.check_const (ProofContext.theory_of background) raw_const;
    val is_first = is_first_occ background;
    val background' = register_const const background;
  in (print_code struct_name is_first (print_const const), background') end;

fun ml_code_datatype_antiq (raw_tyco, raw_constrs) {struct_name, background} =
  let
    val thy = ProofContext.theory_of background;
    val tyco = Sign.intern_type thy raw_tyco;
    val constrs = map (Code.check_const thy) raw_constrs;
    val constrs' = (map fst o snd o Code.get_datatype thy) tyco;
    val _ = if gen_eq_set (op =) (constrs, constrs') then ()
      else error ("Type " ^ quote tyco ^ ": given constructors diverge from real constructors")
    val is_first = is_first_occ background;
    val background' = register_datatype tyco constrs background;
  in (print_code struct_name is_first (print_datatype tyco constrs), background') end;

end; (*local*)


(** Isar setup **)

val _ = ML_Context.add_antiq "code" (fn _ => Args.term >> ml_code_antiq);
val _ = ML_Context.add_antiq "code_datatype" (fn _ =>
  (Args.tyname --| Scan.lift (Args.$$$ "=")
    -- (Args.term ::: Scan.repeat (Scan.lift (Args.$$$ "|") |-- Args.term)))
      >> ml_code_datatype_antiq);

fun isar_seri_sml module_name =
  Code_Target.parse_args (Scan.succeed ())
  #> (fn () => serialize_ml target_SML
      (SOME (use_text ML_Env.local_context (1, "generated code") false))
      pr_sml_module pr_sml_stmt module_name);

fun isar_seri_ocaml module_name =
  Code_Target.parse_args (Scan.succeed ())
  #> (fn () => serialize_ml target_OCaml NONE
      pr_ocaml_module pr_ocaml_stmt module_name);

val setup =
  Code_Target.add_target (target_SML, (isar_seri_sml, literals_sml))
  #> Code_Target.add_target (target_OCaml, (isar_seri_ocaml, literals_ocaml))
  #> Code_Target.extend_target (target_Eval, (target_SML, K I))
  #> Code_Target.add_syntax_tyco target_SML "fun" (SOME (2, fn pr_typ => fn fxy => fn [ty1, ty2] =>
      brackify_infix (1, R) fxy [
        pr_typ (INFX (1, X)) ty1,
        str "->",
        pr_typ (INFX (1, R)) ty2
      ]))
  #> Code_Target.add_syntax_tyco target_OCaml "fun" (SOME (2, fn pr_typ => fn fxy => fn [ty1, ty2] =>
      brackify_infix (1, R) fxy [
        pr_typ (INFX (1, X)) ty1,
        str "->",
        pr_typ (INFX (1, R)) ty2
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
