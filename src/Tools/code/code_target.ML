(*  Title:      Tools/code/code_target.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Serializer from intermediate language ("Thin-gol")
to target languages (like SML or Haskell).
*)

signature CODE_TARGET =
sig
  include BASIC_CODE_THINGOL;

  val add_syntax_class: string -> class
    -> (string * (string * string) list) option -> theory -> theory;
  val add_syntax_inst: string -> string * class -> bool -> theory -> theory;
  val add_syntax_tycoP: string -> string -> OuterParse.token list
    -> (theory -> theory) * OuterParse.token list;
  val add_syntax_constP: string -> string -> OuterParse.token list
    -> (theory -> theory) * OuterParse.token list;

  val add_undefined: string -> string -> string -> theory -> theory;
  val add_pretty_list: string -> string -> string -> theory -> theory;
  val add_pretty_list_string: string -> string -> string
    -> string -> string list -> theory -> theory;
  val add_pretty_char: string -> string -> string list -> theory -> theory
  val add_pretty_numeral: string -> bool -> bool -> string -> string -> string
    -> string -> string -> theory -> theory;
  val add_pretty_message: string -> string -> string list -> string
    -> string -> string -> theory -> theory;

  val allow_abort: string -> theory -> theory;

  type serialization;
  type serializer;
  val add_target: string * serializer -> theory -> theory;
  val extend_target: string * (string * (CodeThingol.program -> CodeThingol.program))
    -> theory -> theory;
  val assert_target: theory -> string -> string;
  val serialize: theory -> string -> string option -> Args.T list
    -> CodeThingol.program -> string list -> serialization;
  val compile: serialization -> unit;
  val export: serialization -> unit;
  val file: Path.T -> serialization -> unit;
  val string: string list -> serialization -> string;

  val code_of: theory -> string -> string -> string list -> string list -> string;
  val eval_conv: string * (unit -> thm) option ref
    -> theory -> cterm -> string list -> thm;
  val eval_term: string * (unit -> 'a) option ref
    -> theory -> term -> string list -> 'a;
  val shell_command: string (*theory name*) -> string (*cg expr*) -> unit;

  val setup: theory -> theory;
  val code_width: int ref;

  val ml_code_of: theory -> CodeThingol.program -> string list -> string * string list;
end;

structure CodeTarget : CODE_TARGET =
struct

open BasicCodeThingol;

(** basics **)

infixr 5 @@;
infixr 5 @|;
fun x @@ y = [x, y];
fun xs @| y = xs @ [y];
val str = PrintMode.setmp [] Pretty.str;
val concat = Pretty.block o Pretty.breaks;
val brackets = Pretty.enclose "(" ")" o Pretty.breaks;
fun semicolon ps = Pretty.block [concat ps, str ";"];
fun enum_default default sep opn cls [] = str default
  | enum_default default sep opn cls xs = Pretty.enum sep opn cls xs;

datatype destination = Compile | Export | File of Path.T | String of string list;
type serialization = destination -> (string * string list) option;

val code_width = ref 80; (*FIXME after Pretty module no longer depends on print mode*)
fun code_setmp f = PrintMode.setmp [] (Pretty.setmp_margin (!code_width) f);
fun code_of_pretty p = code_setmp Pretty.string_of p ^ "\n";
fun code_writeln p = Pretty.setmp_margin (!code_width) Pretty.writeln p;

(*FIXME why another code_setmp?*)
fun compile f = (code_setmp f Compile; ());
fun export f = (code_setmp f Export; ());
fun file p f = (code_setmp f (File p); ());
fun string cs f = fst (the (code_setmp f (String cs)));

fun stmt_names_of_destination (String stmts) = stmts
  | stmt_names_of_destination _ = [];


(** generic syntax **)

datatype lrx = L | R | X;

datatype fixity =
    BR
  | NOBR
  | INFX of (int * lrx);

val APP = INFX (~1, L);

fun fixity_lrx L L = false
  | fixity_lrx R R = false
  | fixity_lrx _ _ = true;

fun fixity NOBR _ = false
  | fixity _ NOBR = false
  | fixity (INFX (pr, lr)) (INFX (pr_ctxt, lr_ctxt)) =
      pr < pr_ctxt
      orelse pr = pr_ctxt
        andalso fixity_lrx lr lr_ctxt
      orelse pr_ctxt = ~1
  | fixity BR (INFX _) = false
  | fixity _ _ = true;

fun gen_brackify _ [p] = p
  | gen_brackify true (ps as _::_) = Pretty.enclose "(" ")" ps
  | gen_brackify false (ps as _::_) = Pretty.block ps;

fun brackify fxy_ctxt =
  gen_brackify (fixity BR fxy_ctxt) o Pretty.breaks;

fun brackify_infix infx fxy_ctxt =
  gen_brackify (fixity (INFX infx) fxy_ctxt) o Pretty.breaks;

type class_syntax = string * (string -> string option);
type typ_syntax = int * ((fixity -> itype -> Pretty.T)
  -> fixity -> itype list -> Pretty.T);
type term_syntax = int * ((CodeName.var_ctxt -> fixity -> iterm -> Pretty.T)
  -> thm -> bool -> CodeName.var_ctxt -> fixity -> (iterm * itype) list -> Pretty.T);

datatype name_syntax_table = NameSyntaxTable of {
  class: class_syntax Symtab.table,
  inst: unit Symtab.table,
  tyco: typ_syntax Symtab.table,
  const: term_syntax Symtab.table
};


(** theory data **)

val target_SML = "SML";
val target_OCaml = "OCaml";
val target_Haskell = "Haskell";

fun mk_name_syntax_table ((class, inst), (tyco, const)) =
  NameSyntaxTable { class = class, inst = inst, tyco = tyco, const = const };
fun map_name_syntax_table f (NameSyntaxTable { class, inst, tyco, const }) =
  mk_name_syntax_table (f ((class, inst), (tyco, const)));
fun merge_name_syntax_table (NameSyntaxTable { class = class1, inst = inst1, tyco = tyco1, const = const1 },
    NameSyntaxTable { class = class2, inst = inst2, tyco = tyco2, const = const2 }) =
  mk_name_syntax_table (
    (Symtab.join (K snd) (class1, class2),
       Symtab.join (K snd) (inst1, inst2)),
    (Symtab.join (K snd) (tyco1, tyco2),
       Symtab.join (K snd) (const1, const2))
  );

type serializer =
  string option                         (*module name*)
  -> Args.T list                        (*arguments*)
  -> (string -> string)                 (*labelled_name*)
  -> string list                        (*reserved symbols*)
  -> (string * Pretty.T) list           (*includes*)
  -> (string -> string option)          (*module aliasses*)
  -> (string -> class_syntax option)
  -> (string -> typ_syntax option)
  -> (string -> term_syntax option)
  -> CodeThingol.program
  -> string list                        (*selected statements*)
  -> serialization;

datatype serializer_entry = Serializer of serializer
  | Extends of string * (CodeThingol.program -> CodeThingol.program);

datatype target = Target of {
  serial: serial,
  serializer: serializer_entry,
  reserved: string list,
  includes: Pretty.T Symtab.table,
  name_syntax_table: name_syntax_table,
  module_alias: string Symtab.table
};

fun mk_target ((serial, serializer), ((reserved, includes), (name_syntax_table, module_alias))) =
  Target { serial = serial, serializer = serializer, reserved = reserved, 
    includes = includes, name_syntax_table = name_syntax_table, module_alias = module_alias };
fun map_target f ( Target { serial, serializer, reserved, includes, name_syntax_table, module_alias } ) =
  mk_target (f ((serial, serializer), ((reserved, includes), (name_syntax_table, module_alias))));
fun merge_target strict target (Target { serial = serial1, serializer = serializer,
  reserved = reserved1, includes = includes1,
  name_syntax_table = name_syntax_table1, module_alias = module_alias1 },
    Target { serial = serial2, serializer = _,
      reserved = reserved2, includes = includes2,
      name_syntax_table = name_syntax_table2, module_alias = module_alias2 }) =
  if serial1 = serial2 orelse not strict then
    mk_target ((serial1, serializer),
      ((merge (op =) (reserved1, reserved2), Symtab.merge (op =) (includes1, includes2)),
        (merge_name_syntax_table (name_syntax_table1, name_syntax_table2),
          Symtab.join (K snd) (module_alias1, module_alias2))
    ))
  else
    error ("Incompatible serializers: " ^ quote target);

structure CodeTargetData = TheoryDataFun
(
  type T = target Symtab.table * string list;
  val empty = (Symtab.empty, []);
  val copy = I;
  val extend = I;
  fun merge _ ((target1, exc1) : T, (target2, exc2)) =
    (Symtab.join (merge_target true) (target1, target2), Library.merge (op =) (exc1, exc2));
);

fun the_serializer (Target { serializer, ... }) = serializer;
fun the_reserved (Target { reserved, ... }) = reserved;
fun the_includes (Target { includes, ... }) = includes;
fun the_name_syntax (Target { name_syntax_table = NameSyntaxTable x, ... }) = x;
fun the_module_alias (Target { module_alias , ... }) = module_alias;

val abort_allowed = snd o CodeTargetData.get;

fun assert_target thy target =
  case Symtab.lookup (fst (CodeTargetData.get thy)) target
   of SOME data => target
    | NONE => error ("Unknown code target language: " ^ quote target);

fun put_target (target, seri) thy =
  let
    val defined_target = is_some o Symtab.lookup (fst (CodeTargetData.get thy));
    val _ = case seri
     of Extends (super, _) => if defined_target super then ()
          else error ("Unknown code target language: " ^ quote super)
      | _ => ();
    val _ = if defined_target target
      then warning ("Overwriting existing target " ^ quote target)
      else ();
  in
    thy
    |> (CodeTargetData.map o apfst oo Symtab.map_default)
          (target, mk_target ((serial (), seri), (([], Symtab.empty),
            (mk_name_syntax_table ((Symtab.empty, Symtab.empty), (Symtab.empty, Symtab.empty)),
              Symtab.empty))))
          ((map_target o apfst o apsnd o K) seri)
  end;

fun add_target (target, seri) = put_target (target, Serializer seri);
fun extend_target (target, (super, modify)) =
  put_target (target, Extends (super, modify));

fun map_target_data target f thy =
  let
    val _ = assert_target thy target;
  in
    thy
    |> (CodeTargetData.map o apfst o Symtab.map_entry target o map_target) f
  end;

fun map_reserved target =
  map_target_data target o apsnd o apfst o apfst;
fun map_includes target =
  map_target_data target o apsnd o apfst o apsnd;
fun map_name_syntax target =
  map_target_data target o apsnd o apsnd o apfst o map_name_syntax_table;
fun map_module_alias target =
  map_target_data target o apsnd o apsnd o apsnd;

fun invoke_serializer thy modify abortable serializer reserved includes 
    module_alias class inst tyco const module args program1 cs1 =
  let
    val program2 = modify program1;
    val hidden = Symtab.keys class @ Symtab.keys inst @ Symtab.keys tyco @ Symtab.keys const;
    val cs2 = subtract (op =) hidden cs1;
    val program3 = Graph.subgraph (not o member (op =) hidden) program2;
    val all_cs = Graph.all_succs program2 cs2;
    val program4 = Graph.subgraph (member (op =) all_cs) program3;
    val empty_funs = filter_out (member (op =) abortable)
      (CodeThingol.empty_funs program3);
    val _ = if null empty_funs then () else error ("No defining equations for "
      ^ commas (map (CodeName.labelled_name thy) empty_funs));
  in
    serializer module args (CodeName.labelled_name thy) reserved includes
      (Symtab.lookup module_alias) (Symtab.lookup class)
      (Symtab.lookup tyco) (Symtab.lookup const)
      program4 cs2
  end;

fun mount_serializer thy alt_serializer target =
  let
    val (targets, abortable) = CodeTargetData.get thy;
    fun collapse_hierarchy target =
      let
        val data = case Symtab.lookup targets target
         of SOME data => data
          | NONE => error ("Unknown code target language: " ^ quote target);
      in case the_serializer data
       of Serializer _ => (I, data)
        | Extends (super, modify) => let
            val (modify', data') = collapse_hierarchy super
          in (modify' #> modify, merge_target false target (data', data)) end
      end;
    val (modify, data) = collapse_hierarchy target;
    val serializer = the_default (case the_serializer data
     of Serializer seri => seri) alt_serializer;
    val reserved = the_reserved data;
    val includes = Symtab.dest (the_includes data);
    val module_alias = the_module_alias data;
    val { class, inst, tyco, const } = the_name_syntax data;
  in
    invoke_serializer thy modify abortable serializer reserved
      includes module_alias class inst tyco const
  end;

fun serialize thy = mount_serializer thy NONE;

fun parse_args f args =
  case Scan.read Args.stopper f args
   of SOME x => x
    | NONE => error "Bad serializer arguments";


(** generic code combinators **)

(* list, char, string, numeral and monad abstract syntax transformations *)

fun nerror thm s = error (s ^ ",\nin equation " ^ Display.string_of_thm thm);

fun implode_list c_nil c_cons t =
  let
    fun dest_cons (IConst (c, _) `$ t1 `$ t2) =
          if c = c_cons
          then SOME (t1, t2)
          else NONE
      | dest_cons _ = NONE;
    val (ts, t') = CodeThingol.unfoldr dest_cons t;
  in case t'
   of IConst (c, _) => if c = c_nil then SOME ts else NONE
    | _ => NONE
  end;

fun decode_char c_nibbles (IConst (c1, _), IConst (c2, _)) =
      let
        fun idx c = find_index (curry (op =) c) c_nibbles;
        fun decode ~1 _ = NONE
          | decode _ ~1 = NONE
          | decode n m = SOME (chr (n * 16 + m));
      in decode (idx c1) (idx c2) end
  | decode_char _ _ = NONE;

fun implode_string c_char c_nibbles mk_char mk_string ts =
  let
    fun implode_char (IConst (c, _) `$ t1 `$ t2) =
          if c = c_char then decode_char c_nibbles (t1, t2) else NONE
      | implode_char _ = NONE;
    val ts' = map implode_char ts;
  in if forall is_some ts'
    then (SOME o str o mk_string o implode o map_filter I) ts'
    else NONE
  end;

fun implode_numeral thm negative c_pls c_min c_bit0 c_bit1 =
  let
    fun dest_bit (IConst (c, _)) = if c = c_bit0 then 0
          else if c = c_bit1 then 1
          else nerror thm "Illegal numeral expression: illegal bit"
      | dest_bit _ = nerror thm "Illegal numeral expression: illegal bit";
    fun dest_numeral (IConst (c, _)) = if c = c_pls then SOME 0
          else if c = c_min then
            if negative then SOME ~1 else NONE
          else nerror thm "Illegal numeral expression: illegal leading digit"
      | dest_numeral (t1 `$ t2) =
          let val (n, b) = (dest_numeral t2, dest_bit t1)
          in case n of SOME n => SOME (2 * n + b) | NONE => NONE end
      | dest_numeral _ = nerror thm "Illegal numeral expression: illegal term";
  in dest_numeral #> the_default 0 end;

fun implode_monad c_bind t =
  let
    fun dest_monad (IConst (c, _) `$ t1 `$ t2) =
          if c = c_bind
            then case CodeThingol.split_abs t2
             of SOME (((v, pat), ty), t') =>
                  SOME ((SOME (((SOME v, pat), ty), true), t1), t')
              | NONE => NONE
            else NONE
      | dest_monad t = case CodeThingol.split_let t
           of SOME (((pat, ty), tbind), t') =>
                SOME ((SOME (((NONE, SOME pat), ty), false), tbind), t')
            | NONE => NONE;
  in CodeThingol.unfoldr dest_monad t end;


(* applications and bindings *)

fun gen_pr_app pr_app pr_term syntax_const is_cons thm pat
    vars fxy (app as ((c, (_, tys)), ts)) =
  case syntax_const c
   of NONE => if pat andalso not (is_cons c) then
        nerror thm "Non-constructor in pattern"
        else brackify fxy (pr_app thm pat vars app)
    | SOME (i, pr) =>
        let
          val k = if i < 0 then length tys else i;
          fun pr' fxy ts = pr (pr_term thm pat) thm pat vars fxy (ts ~~ curry Library.take k tys);
        in if k = length ts
          then pr' fxy ts
        else if k < length ts
          then case chop k ts of (ts1, ts2) =>
            brackify fxy (pr' APP ts1 :: map (pr_term thm pat vars BR) ts2)
          else pr_term thm pat vars fxy (CodeThingol.eta_expand k app)
        end;

fun gen_pr_bind pr_bind pr_term thm (fxy : fixity) ((v, pat), ty : itype) vars =
  let
    val vs = case pat
     of SOME pat => CodeThingol.fold_varnames (insert (op =)) pat []
      | NONE => [];
    val vars' = CodeName.intro_vars (the_list v) vars;
    val vars'' = CodeName.intro_vars vs vars';
    val v' = Option.map (CodeName.lookup_var vars') v;
    val pat' = Option.map (pr_term thm true vars'' fxy) pat;
  in (pr_bind ((v', pat'), ty), vars'') end;


(* name auxiliary *)

val first_upper = implode o nth_map 0 Symbol.to_ascii_upper o explode;
val first_lower = implode o nth_map 0 Symbol.to_ascii_lower o explode;

val dest_name =
  apfst NameSpace.implode o split_last o fst o split_last o NameSpace.explode;

fun mk_name_module reserved_names module_prefix module_alias program =
  let
    fun mk_alias name = case module_alias name
     of SOME name' => name'
      | NONE => name
          |> NameSpace.explode
          |> map (fn name => (the_single o fst) (Name.variants [name] reserved_names))
          |> NameSpace.implode;
    fun mk_prefix name = case module_prefix
     of SOME module_prefix => NameSpace.append module_prefix name
      | NONE => name;
    val tab =
      Symtab.empty
      |> Graph.fold ((fn name => Symtab.default (name, (mk_alias #> mk_prefix) name))
           o fst o dest_name o fst)
             program
  in the o Symtab.lookup tab end;



(** SML/OCaml serializer **)

datatype ml_stmt =
    MLFuns of (string * (typscheme * ((iterm list * iterm) * thm) list)) list
  | MLDatas of (string * ((vname * sort) list * (string * itype list) list)) list
  | MLClass of string * (vname * ((class * string) list * (string * itype) list))
  | MLClassinst of string * ((class * (string * (vname * sort) list))
        * ((class * (string * (string * dict list list))) list
      * ((string * const) * thm) list));

fun stmt_names_of (MLFuns fs) = map fst fs
  | stmt_names_of (MLDatas ds) = map fst ds
  | stmt_names_of (MLClass (c, _)) = [c]
  | stmt_names_of (MLClassinst (i, _)) = [i];

fun pr_sml_stmt syntax_tyco syntax_const labelled_name reserved_names deresolve is_cons =
  let
    val pr_label_classrel = translate_string (fn "." => "__" | c => c)
      o NameSpace.qualifier;
    val pr_label_classparam = NameSpace.base o NameSpace.qualifier;
    fun pr_dicts fxy ds =
      let
        fun pr_dictvar (v, (_, 1)) = first_upper v ^ "_"
          | pr_dictvar (v, (i, _)) = first_upper v ^ string_of_int (i+1) ^ "_";
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
    fun pr_term thm pat vars fxy (IConst c) =
          pr_app thm pat vars fxy (c, [])
      | pr_term thm pat vars fxy (IVar v) =
          str (CodeName.lookup_var vars v)
      | pr_term thm pat vars fxy (t as t1 `$ t2) =
          (case CodeThingol.unfold_const_app t
           of SOME c_ts => pr_app thm pat vars fxy c_ts
            | NONE =>
                brackify fxy [pr_term thm pat vars NOBR t1, pr_term thm pat vars BR t2])
      | pr_term thm pat vars fxy (t as _ `|-> _) =
          let
            val (binds, t') = CodeThingol.unfold_abs t;
            fun pr ((v, pat), ty) =
              pr_bind thm NOBR ((SOME v, pat), ty)
              #>> (fn p => concat [str "fn", p, str "=>"]);
            val (ps, vars') = fold_map pr binds vars;
          in brackets (ps @ [pr_term thm pat vars' NOBR t']) end
      | pr_term thm pat vars fxy (ICase (cases as (_, t0))) =
          (case CodeThingol.unfold_const_app t0
           of SOME (c_ts as ((c, _), _)) => if is_none (syntax_const c)
                then pr_case thm vars fxy cases
                else pr_app thm pat vars fxy c_ts
            | NONE => pr_case thm vars fxy cases)
    and pr_app' thm pat vars (app as ((c, (iss, tys)), ts)) =
      if is_cons c then let
        val k = length tys
      in if k < 2 then 
        (str o deresolve) c :: map (pr_term thm pat vars BR) ts
      else if k = length ts then
        [(str o deresolve) c, Pretty.enum "," "(" ")" (map (pr_term thm pat vars NOBR) ts)]
      else [pr_term thm pat vars BR (CodeThingol.eta_expand k app)] end else
        (str o deresolve) c
          :: (map (pr_dicts BR) o filter_out null) iss @ map (pr_term thm pat vars BR) ts
    and pr_app thm pat vars = gen_pr_app pr_app' pr_term syntax_const is_cons thm pat vars
    and pr_bind' ((NONE, NONE), _) = str "_"
      | pr_bind' ((SOME v, NONE), _) = str v
      | pr_bind' ((NONE, SOME p), _) = p
      | pr_bind' ((SOME v, SOME p), _) = concat [str v, str "as", p]
    and pr_bind thm = gen_pr_bind pr_bind' pr_term thm
    and pr_case thm vars fxy (cases as ((_, [_]), _)) =
          let
            val (binds, t') = CodeThingol.unfold_let (ICase cases);
            fun pr ((pat, ty), t) vars =
              vars
              |> pr_bind thm NOBR ((NONE, SOME pat), ty)
              |>> (fn p => semicolon [str "val", p, str "=", pr_term thm false vars NOBR t])
            val (ps, vars') = fold_map pr binds vars;
          in
            Pretty.chunks [
              [str ("let"), Pretty.fbrk, Pretty.chunks ps] |> Pretty.block,
              [str ("in"), Pretty.fbrk, pr_term thm false vars' NOBR t'] |> Pretty.block,
              str ("end")
            ]
          end
      | pr_case thm vars fxy (((td, ty), b::bs), _) =
          let
            fun pr delim (pat, t) =
              let
                val (p, vars') = pr_bind thm NOBR ((NONE, SOME pat), ty) vars;
              in
                concat [str delim, p, str "=>", pr_term thm false vars' NOBR t]
              end;
          in
            (Pretty.enclose "(" ")" o single o brackify fxy) (
              str "case"
              :: pr_term thm false vars NOBR td
              :: pr "of" b
              :: map (pr "|") bs
            )
          end
      | pr_case thm vars fxy ((_, []), _) = str "raise Fail \"empty case\"";
    fun pr_stmt (MLFuns (funns as (funn :: funns'))) =
          let
            val definer =
              let
                fun no_args _ (((ts, _), _) :: _) = length ts
                  | no_args ty [] = (length o fst o CodeThingol.unfold_fun) ty;
                fun mk 0 [] = "val"
                  | mk 0 vs = if (null o filter_out (null o snd)) vs
                      then "val" else "fun"
                  | mk k _ = "fun";
                fun chk (_, ((vs, ty), eqs)) NONE = SOME (mk (no_args ty eqs) vs)
                  | chk (_, ((vs, ty), eqs)) (SOME defi) =
                      if defi = mk (no_args ty eqs) vs then SOME defi
                      else error ("Mixing simultaneous vals and funs not implemented: "
                        ^ commas (map (labelled_name o fst) funns));
              in the (fold chk funns NONE) end;
            fun pr_funn definer (name, ((vs, ty), [])) =
                  let
                    val vs_dict = filter_out (null o snd) vs;
                    val n = length vs_dict + (length o fst o CodeThingol.unfold_fun) ty;
                    val exc_str =
                      (ML_Syntax.print_string o NameSpace.base o NameSpace.qualifier) name;
                  in
                    concat (
                      str definer
                      :: (str o deresolve) name
                      :: map str (replicate n "_")
                      @ str "="
                      :: str "raise"
                      :: str "(Fail"
                      @@ str (exc_str ^ ")")
                    )
                  end
              | pr_funn definer (name, ((vs, ty), eqs as eq :: eqs')) =
                  let
                    val vs_dict = filter_out (null o snd) vs;
                    val shift = if null eqs' then I else
                      map (Pretty.block o single o Pretty.block o single);
                    fun pr_eq definer ((ts, t), thm) =
                      let
                        val consts = map_filter
                          (fn c => if (is_some o syntax_const) c
                            then NONE else (SOME o NameSpace.base o deresolve) c)
                            ((fold o CodeThingol.fold_constnames) (insert (op =)) (t :: ts) []);
                        val vars = reserved_names
                          |> CodeName.intro_vars consts
                          |> CodeName.intro_vars ((fold o CodeThingol.fold_unbound_varnames)
                               (insert (op =)) ts []);
                      in
                        concat (
                          [str definer, (str o deresolve) name]
                          @ (if null ts andalso null vs_dict
                             then [str ":", pr_typ NOBR ty]
                             else
                               pr_tyvar_dicts vs_dict
                               @ map (pr_term thm true vars BR) ts)
                       @ [str "=", pr_term thm false vars NOBR t]
                        )
                      end
                  in
                    (Pretty.block o Pretty.fbreaks o shift) (
                      pr_eq definer eq
                      :: map (pr_eq "|") eqs'
                    )
                  end;
            val (ps, p) = split_last (pr_funn definer funn :: map (pr_funn "and") funns');
          in Pretty.chunks (ps @ [Pretty.block ([p, str ";"])]) end
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
          in Pretty.chunks (ps @ [Pretty.block ([p, str ";"])]) end
     | pr_stmt (MLClass (class, (v, (superclasses, classparams)))) =
          let
            val w = first_upper v ^ "_";
            fun pr_superclass_field (class, classrel) =
              (concat o map str) [
                pr_label_classrel classrel, ":", "'" ^ v, deresolve class
              ];
            fun pr_classparam_field (classparam, ty) =
              concat [
                (str o pr_label_classparam) classparam, str ":", pr_typ NOBR ty
              ];
            fun pr_classparam_proj (classparam, _) =
              semicolon [
                str "fun",
                (str o deresolve) classparam,
                Pretty.enclose "(" ")" [str (w ^ ":'" ^ v ^ " " ^ deresolve class)],
                str "=",
                str ("#" ^ pr_label_classparam classparam),
                str w
              ];
            fun pr_superclass_proj (_, classrel) =
              semicolon [
                str "fun",
                (str o deresolve) classrel,
                Pretty.enclose "(" ")" [str (w ^ ":'" ^ v ^ " " ^ deresolve class)],
                str "=",
                str ("#" ^ pr_label_classrel classrel),
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
                (str o pr_label_classrel) classrel,
                str "=",
                pr_dicts NOBR [DictConst dss]
              ];
            fun pr_classparam ((classparam, c_inst), thm) =
              concat [
                (str o pr_label_classparam) classparam,
                str "=",
                pr_app thm false reserved_names NOBR (c_inst, [])
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

fun pr_ocaml_stmt syntax_tyco syntax_const labelled_name reserved_names deresolve is_cons =
  let
    fun pr_dicts fxy ds =
      let
        fun pr_dictvar (v, (_, 1)) = "_" ^ first_upper v
          | pr_dictvar (v, (i, _)) = "_" ^ first_upper v ^ string_of_int (i+1);
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
    fun pr_term thm pat vars fxy (IConst c) =
          pr_app thm pat vars fxy (c, [])
      | pr_term thm pat vars fxy (IVar v) =
          str (CodeName.lookup_var vars v)
      | pr_term thm pat vars fxy (t as t1 `$ t2) =
          (case CodeThingol.unfold_const_app t
           of SOME c_ts => pr_app thm pat vars fxy c_ts
            | NONE =>
                brackify fxy [pr_term thm pat vars NOBR t1, pr_term thm pat vars BR t2])
      | pr_term thm pat vars fxy (t as _ `|-> _) =
          let
            val (binds, t') = CodeThingol.unfold_abs t;
            fun pr ((v, pat), ty) = pr_bind thm BR ((SOME v, pat), ty);
            val (ps, vars') = fold_map pr binds vars;
          in brackets (str "fun" :: ps @ str "->" @@ pr_term thm pat vars' NOBR t') end
      | pr_term thm pat vars fxy (ICase (cases as (_, t0))) = (case CodeThingol.unfold_const_app t0
           of SOME (c_ts as ((c, _), _)) => if is_none (syntax_const c)
                then pr_case thm vars fxy cases
                else pr_app thm pat vars fxy c_ts
            | NONE => pr_case thm vars fxy cases)
    and pr_app' thm pat vars (app as ((c, (iss, tys)), ts)) =
      if is_cons c then
        if length tys = length ts
        then case ts
         of [] => [(str o deresolve) c]
          | [t] => [(str o deresolve) c, pr_term thm pat vars BR t]
          | _ => [(str o deresolve) c, Pretty.enum "," "(" ")"
                    (map (pr_term thm pat vars NOBR) ts)]
        else [pr_term thm pat vars BR (CodeThingol.eta_expand (length tys) app)]
      else (str o deresolve) c
        :: ((map (pr_dicts BR) o filter_out null) iss @ map (pr_term thm pat vars BR) ts)
    and pr_app thm pat vars = gen_pr_app pr_app' pr_term syntax_const is_cons thm pat vars
    and pr_bind' ((NONE, NONE), _) = str "_"
      | pr_bind' ((SOME v, NONE), _) = str v
      | pr_bind' ((NONE, SOME p), _) = p
      | pr_bind' ((SOME v, SOME p), _) = brackets [p, str "as", str v]
    and pr_bind thm = gen_pr_bind pr_bind' pr_term thm
    and pr_case thm vars fxy (cases as ((_, [_]), _)) =
          let
            val (binds, t') = CodeThingol.unfold_let (ICase cases);
            fun pr ((pat, ty), t) vars =
              vars
              |> pr_bind thm NOBR ((NONE, SOME pat), ty)
              |>> (fn p => concat
                  [str "let", p, str "=", pr_term thm false vars NOBR t, str "in"])
            val (ps, vars') = fold_map pr binds vars;
          in Pretty.chunks (ps @| pr_term thm false vars' NOBR t') end
      | pr_case thm vars fxy (((td, ty), b::bs), _) =
          let
            fun pr delim (pat, t) =
              let
                val (p, vars') = pr_bind thm NOBR ((NONE, SOME pat), ty) vars;
              in concat [str delim, p, str "->", pr_term thm false vars' NOBR t] end;
          in
            (Pretty.enclose "(" ")" o single o brackify fxy) (
              str "match"
              :: pr_term thm false vars NOBR td
              :: pr "with" b
              :: map (pr "|") bs
            )
          end
      | pr_case thm vars fxy ((_, []), _) = str "failwith \"empty case\"";
    fun fish_params vars eqs =
      let
        fun fish_param _ (w as SOME _) = w
          | fish_param (IVar v) NONE = SOME v
          | fish_param _ NONE = NONE;
        fun fillup_param _ (_, SOME v) = v
          | fillup_param x (i, NONE) = x ^ string_of_int i;
        val fished1 = fold (map2 fish_param) eqs (replicate (length (hd eqs)) NONE);
        val x = Name.variant (map_filter I fished1) "x";
        val fished2 = map_index (fillup_param x) fished1;
        val (fished3, _) = Name.variants fished2 Name.context;
        val vars' = CodeName.intro_vars fished3 vars;
      in map (CodeName.lookup_var vars') fished3 end;
    fun pr_stmt (MLFuns (funns as funn :: funns')) =
          let
            fun pr_eq ((ts, t), thm) =
              let
                val consts = map_filter
                  (fn c => if (is_some o syntax_const) c
                    then NONE else (SOME o NameSpace.base o deresolve) c)
                    ((fold o CodeThingol.fold_constnames) (insert (op =)) (t :: ts) []);
                val vars = reserved_names
                  |> CodeName.intro_vars consts
                  |> CodeName.intro_vars ((fold o CodeThingol.fold_unbound_varnames)
                      (insert (op =)) ts []);
              in concat [
                (Pretty.block o Pretty.commas) (map (pr_term thm true vars NOBR) ts),
                str "->",
                pr_term thm false vars NOBR t
              ] end;
            fun pr_eqs name ty [] =
                  let
                    val n = (length o fst o CodeThingol.unfold_fun) ty;
                    val exc_str =
                      (ML_Syntax.print_string o NameSpace.base o NameSpace.qualifier) name;
                  in
                    concat (
                      map str (replicate n "_")
                      @ str "="
                      :: str "failwith"
                      @@ str exc_str
                    )
                  end
              | pr_eqs _ _ [((ts, t), thm)] =
                  let
                    val consts = map_filter
                      (fn c => if (is_some o syntax_const) c
                        then NONE else (SOME o NameSpace.base o deresolve) c)
                        ((fold o CodeThingol.fold_constnames) (insert (op =)) (t :: ts) []);
                    val vars = reserved_names
                      |> CodeName.intro_vars consts
                      |> CodeName.intro_vars ((fold o CodeThingol.fold_unbound_varnames)
                          (insert (op =)) ts []);
                  in
                    concat (
                      map (pr_term thm true vars BR) ts
                      @ str "="
                      @@ pr_term thm false vars NOBR t
                    )
                  end
              | pr_eqs _ _ (eqs as (eq as (([_], _), _)) :: eqs') =
                  Pretty.block (
                    str "="
                    :: Pretty.brk 1
                    :: str "function"
                    :: Pretty.brk 1
                    :: pr_eq eq
                    :: maps (append [Pretty.fbrk, str "|", Pretty.brk 1]
                          o single o pr_eq) eqs'
                  )
              | pr_eqs _ _ (eqs as eq :: eqs') =
                  let
                    val consts = map_filter
                      (fn c => if (is_some o syntax_const) c
                        then NONE else (SOME o NameSpace.base o deresolve) c)
                        ((fold o CodeThingol.fold_constnames)
                          (insert (op =)) (map (snd o fst) eqs) []);
                    val vars = reserved_names
                      |> CodeName.intro_vars consts;
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
                @| pr_eqs name ty eqs
              );
            val (ps, p) = split_last
              (pr_funn "let rec" funn :: map (pr_funn "and") funns');
          in Pretty.chunks (ps @ [Pretty.block ([p, str ";;"])]) end
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
          in Pretty.chunks (ps @ [Pretty.block ([p, str ";;"])]) end
     | pr_stmt (MLClass (class, (v, (superclasses, classparams)))) =
          let
            val w = "_" ^ first_upper v;
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
              enum_default "();;" ";" "{" "};;" (
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
            fun pr_classparam_inst ((classparam, c_inst), thm) =
              concat [
                (str o deresolve) classparam,
                str "=",
                pr_app thm false reserved_names NOBR (c_inst, [])
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
    val mk_name_module = mk_name_module reserved_names NONE module_alias program;
    fun mk_name_stmt upper name nsp =
      let
        val (_, base) = dest_name name;
        val base' = if upper then first_upper base else base;
        val ([base''], nsp') = Name.variants [base'] nsp;
      in (base'', nsp') end;
    fun add_funs stmts =
      fold_map
        (fn (name, CodeThingol.Fun stmt) =>
              map_nsp_fun_yield (mk_name_stmt false name) #>>
                rpair (name, stmt)
          | (name, _) =>
              error ("Function block containing illegal statement: " ^ labelled_name name)
        ) stmts
      #>> (split_list #> apsnd MLFuns);
    fun add_datatypes stmts =
      fold_map
        (fn (name, CodeThingol.Datatype stmt) =>
              map_nsp_typ_yield (mk_name_stmt false name) #>> rpair (SOME (name, stmt))
          | (name, CodeThingol.Datatypecons _) =>
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
        (fn (name, CodeThingol.Class info) =>
              map_nsp_typ_yield (mk_name_stmt false name) #>> rpair (SOME (name, info))
          | (name, CodeThingol.Classrel _) =>
              map_nsp_fun_yield (mk_name_stmt false name) #>> rpair NONE
          | (name, CodeThingol.Classparam _) =>
              map_nsp_fun_yield (mk_name_stmt false name) #>> rpair NONE
          | (name, _) =>
              error ("Class block containing illegal statement: " ^ labelled_name name)
        ) stmts
      #>> (split_list #> apsnd (map_filter I
        #> (fn [] => error ("Class block without class statement: "
                  ^ (commas o map (labelled_name o fst)) stmts)
             | [stmt] => MLClass stmt)));
    fun add_inst [(name, CodeThingol.Classinst stmt)] =
      map_nsp_fun_yield (mk_name_stmt false name)
      #>> (fn base => ([base], MLClassinst (name, stmt)));
    fun add_stmts ((stmts as (_, CodeThingol.Fun _)::_)) =
          add_funs stmts
      | add_stmts ((stmts as (_, CodeThingol.Datatypecons _)::_)) =
          add_datatypes stmts
      | add_stmts ((stmts as (_, CodeThingol.Datatype _)::_)) =
          add_datatypes stmts
      | add_stmts ((stmts as (_, CodeThingol.Class _)::_)) =
          add_class stmts
      | add_stmts ((stmts as (_, CodeThingol.Classrel _)::_)) =
          add_class stmts
      | add_stmts ((stmts as (_, CodeThingol.Classparam _)::_)) =
          add_class stmts
      | add_stmts ((stmts as [(_, CodeThingol.Classinst _)])) =
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
        val (module_names, _) = (split_list o map dest_name) names;
        val module_name = (the_single o distinct (op =) o map mk_name_module) module_names
          handle Empty =>
            error ("Different namespace prefixes for mutual dependencies:\n"
              ^ commas (map labelled_name names)
              ^ "\n"
              ^ commas module_names);
        val module_name_path = NameSpace.explode module_name;
        fun add_dep name name' =
          let
            val module_name' = (mk_name_module o fst o dest_name) name';
          in if module_name = module_name' then
            map_node module_name_path (Graph.add_edge (name, name'))
          else let
            val (common, (diff1::_, diff2::_)) = chop_prefix (op =)
              (module_name_path, NameSpace.explode module_name');
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
        val module_name' = (NameSpace.explode o mk_name_module) module_name;
        val (_, (_, remainder)) = chop_prefix (op =) (prefix, module_name');
        val stmt_name =
          nodes
          |> fold (fn name => fn node => case Graph.get_node node name
              of Module (_, (_, node)) => node) module_name'
          |> (fn node => case Graph.get_node node name of Stmt (stmt_name, _) => stmt_name
               | Dummy stmt_name => stmt_name);
      in
        NameSpace.implode (remainder @ [stmt_name])
      end handle Graph.UNDEF _ =>
        error ("Unknown statement name: " ^ labelled_name name);
  in (deresolver, nodes) end;

fun serialize_ml compile pr_module pr_stmt raw_module_name labelled_name reserved_names includes raw_module_alias
  _ syntax_tyco syntax_const program cs destination =
  let
    val is_cons = CodeThingol.is_cons program;
    val stmt_names = stmt_names_of_destination destination;
    val module_name = if null stmt_names then raw_module_name else SOME "Code";
    val (deresolver, nodes) = ml_node_of_program labelled_name module_name
      reserved_names raw_module_alias program;
    val reserved_names = CodeName.make_vars reserved_names;
    fun pr_node prefix (Dummy _) =
          NONE
      | pr_node prefix (Stmt (_, stmt)) = if null stmt_names orelse
          (not o null o filter (member (op =) stmt_names) o stmt_names_of) stmt then SOME
            (pr_stmt syntax_tyco syntax_const labelled_name reserved_names
              (deresolver prefix) is_cons stmt)
          else NONE
      | pr_node prefix (Module (module_name, (_, nodes))) =
          let
            val ps = separate (str "")
              ((map_filter (pr_node (prefix @ [module_name]) o Graph.get_node nodes)
                o rev o flat o Graph.strong_conn) nodes)
          in SOME (case destination of String _ => Pretty.chunks ps
           | _ => pr_module module_name ps)
          end;
    val cs' = map_filter (try (deresolver (if is_some module_name then the_list module_name else [])))
      cs;
    val p = Pretty.chunks (separate (str "") (map snd includes @ (map_filter
      (pr_node [] o Graph.get_node nodes) o rev o flat o Graph.strong_conn) nodes));
    fun output Compile = K NONE o compile o code_of_pretty
      | output Export = K NONE o code_writeln
      | output (File file) = K NONE o File.write file o code_of_pretty
      | output (String _) = SOME o rpair cs' o code_of_pretty;
  in output destination p end;

end; (*local*)

(* ML (system language) code for evaluation and instrumentalization *)

fun ml_code_of thy program cs = mount_serializer thy
  (SOME (fn _ => fn [] => serialize_ml (K ()) (K Pretty.chunks) pr_sml_stmt (SOME "")))
    target_SML NONE [] program cs (String [])
  |> the;

(* generic entry points for SML/OCaml *)

fun isar_seri_sml module_name =
  parse_args (Scan.succeed ())
  #> (fn () => serialize_ml (use_text (1, "generated code") Output.ml_output false)
      pr_sml_module pr_sml_stmt module_name);

fun isar_seri_ocaml module_name =
  parse_args (Scan.succeed ())
  #> (fn () => serialize_ml (fn _ => error "OCaml: no internal compilation")
      pr_ocaml_module pr_ocaml_stmt module_name);


(** Haskell serializer **)

fun pr_haskell_bind pr_term =
  let
    fun pr_bind ((NONE, NONE), _) = str "_"
      | pr_bind ((SOME v, NONE), _) = str v
      | pr_bind ((NONE, SOME p), _) = p
      | pr_bind ((SOME v, SOME p), _) = brackets [str v, str "@", p];
  in gen_pr_bind pr_bind pr_term end;

fun pr_haskell_stmt syntax_class syntax_tyco syntax_const labelled_name
    init_syms deresolve is_cons contr_classparam_typs deriving_show =
  let
    val deresolve_base = NameSpace.base o deresolve;
    fun class_name class = case syntax_class class
     of NONE => deresolve class
      | SOME (class, _) => class;
    fun classparam_name class classparam = case syntax_class class
     of NONE => deresolve_base classparam
      | SOME (_, classparam_syntax) => case classparam_syntax classparam
         of NONE => (snd o dest_name) classparam
          | SOME classparam => classparam;
    fun pr_typcontext tyvars vs = case maps (fn (v, sort) => map (pair v) sort) vs
     of [] => []
      | classbinds => Pretty.enum "," "(" ")" (
          map (fn (v, class) =>
            str (class_name class ^ " " ^ CodeName.lookup_var tyvars v)) classbinds)
          @@ str " => ";
    fun pr_typforall tyvars vs = case map fst vs
     of [] => []
      | vnames => str "forall " :: Pretty.breaks
          (map (str o CodeName.lookup_var tyvars) vnames) @ str "." @@ Pretty.brk 1;
    fun pr_tycoexpr tyvars fxy (tyco, tys) =
      brackify fxy (str tyco :: map (pr_typ tyvars BR) tys)
    and pr_typ tyvars fxy (tycoexpr as tyco `%% tys) = (case syntax_tyco tyco
         of NONE => pr_tycoexpr tyvars fxy (deresolve tyco, tys)
          | SOME (i, pr) => pr (pr_typ tyvars) fxy tys)
      | pr_typ tyvars fxy (ITyVar v) = (str o CodeName.lookup_var tyvars) v;
    fun pr_typdecl tyvars (vs, tycoexpr) =
      Pretty.block (pr_typcontext tyvars vs @| pr_tycoexpr tyvars NOBR tycoexpr);
    fun pr_typscheme tyvars (vs, ty) =
      Pretty.block (pr_typforall tyvars vs @ pr_typcontext tyvars vs @| pr_typ tyvars NOBR ty);
    fun pr_term tyvars thm pat vars fxy (IConst c) =
          pr_app tyvars thm pat vars fxy (c, [])
      | pr_term tyvars thm pat vars fxy (t as (t1 `$ t2)) =
          (case CodeThingol.unfold_const_app t
           of SOME app => pr_app tyvars thm pat vars fxy app
            | _ =>
                brackify fxy [
                  pr_term tyvars thm pat vars NOBR t1,
                  pr_term tyvars thm pat vars BR t2
                ])
      | pr_term tyvars thm pat vars fxy (IVar v) =
          (str o CodeName.lookup_var vars) v
      | pr_term tyvars thm pat vars fxy (t as _ `|-> _) =
          let
            val (binds, t') = CodeThingol.unfold_abs t;
            fun pr ((v, pat), ty) = pr_bind tyvars thm BR ((SOME v, pat), ty);
            val (ps, vars') = fold_map pr binds vars;
          in brackets (str "\\" :: ps @ str "->" @@ pr_term tyvars thm pat vars' NOBR t') end
      | pr_term tyvars thm pat vars fxy (ICase (cases as (_, t0))) =
          (case CodeThingol.unfold_const_app t0
           of SOME (c_ts as ((c, _), _)) => if is_none (syntax_const c)
                then pr_case tyvars thm vars fxy cases
                else pr_app tyvars thm pat vars fxy c_ts
            | NONE => pr_case tyvars thm vars fxy cases)
    and pr_app' tyvars thm pat vars ((c, (_, tys)), ts) = case contr_classparam_typs c
     of [] => (str o deresolve) c :: map (pr_term tyvars thm pat vars BR) ts
      | fingerprint => let
          val ts_fingerprint = ts ~~ curry Library.take (length ts) fingerprint;
          val needs_annotation = forall (fn (_, NONE) => true | (t, SOME _) =>
            (not o CodeThingol.locally_monomorphic) t) ts_fingerprint;
          fun pr_term_anno (t, NONE) _ = pr_term tyvars thm pat vars BR t
            | pr_term_anno (t, SOME _) ty =
                brackets [pr_term tyvars thm pat vars NOBR t, str "::", pr_typ tyvars NOBR ty];
        in
          if needs_annotation then
            (str o deresolve) c :: map2 pr_term_anno ts_fingerprint (curry Library.take (length ts) tys)
          else (str o deresolve) c :: map (pr_term tyvars thm pat vars BR) ts
        end
    and pr_app tyvars = gen_pr_app (pr_app' tyvars) (pr_term tyvars) syntax_const is_cons
    and pr_bind tyvars = pr_haskell_bind (pr_term tyvars)
    and pr_case tyvars thm vars fxy (cases as ((_, [_]), _)) =
          let
            val (binds, t) = CodeThingol.unfold_let (ICase cases);
            fun pr ((pat, ty), t) vars =
              vars
              |> pr_bind tyvars thm BR ((NONE, SOME pat), ty)
              |>> (fn p => semicolon [p, str "=", pr_term tyvars thm false vars NOBR t])
            val (ps, vars') = fold_map pr binds vars;
          in
            Pretty.block_enclose (
              str "let {",
              concat [str "}", str "in", pr_term tyvars thm false vars' NOBR t]
            ) ps
          end
      | pr_case tyvars thm vars fxy (((td, ty), bs as _ :: _), _) =
          let
            fun pr (pat, t) =
              let
                val (p, vars') = pr_bind tyvars thm NOBR ((NONE, SOME pat), ty) vars;
              in semicolon [p, str "->", pr_term tyvars thm false vars' NOBR t] end;
          in
            Pretty.block_enclose (
              concat [str "(case", pr_term tyvars thm false vars NOBR td, str "of", str "{"],
              str "})"
            ) (map pr bs)
          end
      | pr_case tyvars thm vars fxy ((_, []), _) = str "error \"empty case\"";
    fun pr_stmt (name, CodeThingol.Fun ((vs, ty), [])) =
          let
            val tyvars = CodeName.intro_vars (map fst vs) init_syms;
            val n = (length o fst o CodeThingol.unfold_fun) ty;
          in
            Pretty.chunks [
              Pretty.block [
                (str o suffix " ::" o deresolve_base) name,
                Pretty.brk 1,
                pr_typscheme tyvars (vs, ty),
                str ";"
              ],
              concat (
                (str o deresolve_base) name
                :: map str (replicate n "_")
                @ str "="
                :: str "error"
                @@ (str o (fn s => s ^ ";") o ML_Syntax.print_string
                    o NameSpace.base o NameSpace.qualifier) name
              )
            ]
          end
      | pr_stmt (name, CodeThingol.Fun ((vs, ty), eqs)) =
          let
            val tyvars = CodeName.intro_vars (map fst vs) init_syms;
            fun pr_eq ((ts, t), thm) =
              let
                val consts = map_filter
                  (fn c => if (is_some o syntax_const) c
                    then NONE else (SOME o NameSpace.base o deresolve) c)
                    ((fold o CodeThingol.fold_constnames) (insert (op =)) (t :: ts) []);
                val vars = init_syms
                  |> CodeName.intro_vars consts
                  |> CodeName.intro_vars ((fold o CodeThingol.fold_unbound_varnames)
                       (insert (op =)) ts []);
              in
                semicolon (
                  (str o deresolve_base) name
                  :: map (pr_term tyvars thm true vars BR) ts
                  @ str "="
                  @@ pr_term tyvars thm false vars NOBR t
                )
              end;
          in
            Pretty.chunks (
              Pretty.block [
                (str o suffix " ::" o deresolve_base) name,
                Pretty.brk 1,
                pr_typscheme tyvars (vs, ty),
                str ";"
              ]
              :: map pr_eq eqs
            )
          end
      | pr_stmt (name, CodeThingol.Datatype (vs, [])) =
          let
            val tyvars = CodeName.intro_vars (map fst vs) init_syms;
          in
            semicolon [
              str "data",
              pr_typdecl tyvars (vs, (deresolve_base name, map (ITyVar o fst) vs))
            ]
          end
      | pr_stmt (name, CodeThingol.Datatype (vs, [(co, [ty])])) =
          let
            val tyvars = CodeName.intro_vars (map fst vs) init_syms;
          in
            semicolon (
              str "newtype"
              :: pr_typdecl tyvars (vs, (deresolve_base name, map (ITyVar o fst) vs))
              :: str "="
              :: (str o deresolve_base) co
              :: pr_typ tyvars BR ty
              :: (if deriving_show name then [str "deriving (Read, Show)"] else [])
            )
          end
      | pr_stmt (name, CodeThingol.Datatype (vs, co :: cos)) =
          let
            val tyvars = CodeName.intro_vars (map fst vs) init_syms;
            fun pr_co (co, tys) =
              concat (
                (str o deresolve_base) co
                :: map (pr_typ tyvars BR) tys
              )
          in
            semicolon (
              str "data"
              :: pr_typdecl tyvars (vs, (deresolve_base name, map (ITyVar o fst) vs))
              :: str "="
              :: pr_co co
              :: map ((fn p => Pretty.block [str "| ", p]) o pr_co) cos
              @ (if deriving_show name then [str "deriving (Read, Show)"] else [])
            )
          end
      | pr_stmt (name, CodeThingol.Class (v, (superclasses, classparams))) =
          let
            val tyvars = CodeName.intro_vars [v] init_syms;
            fun pr_classparam (classparam, ty) =
              semicolon [
                (str o classparam_name name) classparam,
                str "::",
                pr_typ tyvars NOBR ty
              ]
          in
            Pretty.block_enclose (
              Pretty.block [
                str "class ",
                Pretty.block (pr_typcontext tyvars [(v, map fst superclasses)]),
                str (deresolve_base name ^ " " ^ CodeName.lookup_var tyvars v),
                str " where {"
              ],
              str "};"
            ) (map pr_classparam classparams)
          end
      | pr_stmt (_, CodeThingol.Classinst ((class, (tyco, vs)), (_, classparam_insts))) =
          let
            val tyvars = CodeName.intro_vars (map fst vs) init_syms;
            fun pr_instdef ((classparam, c_inst), thm) =
              semicolon [
                (str o classparam_name class) classparam,
                str "=",
                pr_app tyvars thm false init_syms NOBR (c_inst, [])
              ];
          in
            Pretty.block_enclose (
              Pretty.block [
                str "instance ",
                Pretty.block (pr_typcontext tyvars vs),
                str (class_name class ^ " "),
                pr_typ tyvars BR (tyco `%% map (ITyVar o fst) vs),
                str " where {"
              ],
              str "};"
            ) (map pr_instdef classparam_insts)
          end;
  in pr_stmt end;

fun pretty_haskell_monad c_bind =
  let
    fun pretty pr thm pat vars fxy [(t, _)] =
      let
        val pr_bind = pr_haskell_bind (K (K pr)) thm;
        fun pr_monad (NONE, t) vars =
              (semicolon [pr vars NOBR t], vars)
          | pr_monad (SOME (bind, true), t) vars = vars
              |> pr_bind NOBR bind
              |>> (fn p => semicolon [p, str "<-", pr vars NOBR t])
          | pr_monad (SOME (bind, false), t) vars = vars
              |> pr_bind NOBR bind
              |>> (fn p => semicolon [str "let", p, str "=", pr vars NOBR t]);
        val (binds, t) = implode_monad c_bind t;
        val (ps, vars') = fold_map pr_monad binds vars;
        fun brack p = if fixity BR fxy then Pretty.block [str "(", p, str ")"] else p;
      in (brack o Pretty.block_enclose (str "do {", str "}")) (ps @| pr vars' NOBR t) end;
  in (1, pretty) end;

fun haskell_program_of_program labelled_name module_name module_prefix reserved_names raw_module_alias program =
  let
    val module_alias = if is_some module_name then K module_name else raw_module_alias;
    val reserved_names = Name.make_context reserved_names;
    val mk_name_module = mk_name_module reserved_names module_prefix module_alias program;
    fun add_stmt (name, (stmt, deps)) =
      let
        val (module_name, base) = dest_name name;
        val module_name' = mk_name_module module_name;
        val mk_name_stmt = yield_singleton Name.variants;
        fun add_fun upper (nsp_fun, nsp_typ) =
          let
            val (base', nsp_fun') =
              mk_name_stmt (if upper then first_upper base else base) nsp_fun
          in (base', (nsp_fun', nsp_typ)) end;
        fun add_typ (nsp_fun, nsp_typ) =
          let
            val (base', nsp_typ') = mk_name_stmt (first_upper base) nsp_typ
          in (base', (nsp_fun, nsp_typ')) end;
        val add_name = case stmt
         of CodeThingol.Fun _ => add_fun false
          | CodeThingol.Datatype _ => add_typ
          | CodeThingol.Datatypecons _ => add_fun true
          | CodeThingol.Class _ => add_typ
          | CodeThingol.Classrel _ => pair base
          | CodeThingol.Classparam _ => add_fun false
          | CodeThingol.Classinst _ => pair base;
        fun add_stmt' base' = case stmt
         of CodeThingol.Datatypecons _ =>
              cons (name, (NameSpace.append module_name' base', NONE))
          | CodeThingol.Classrel _ => I
          | CodeThingol.Classparam _ =>
              cons (name, (NameSpace.append module_name' base', NONE))
          | _ => cons (name, (NameSpace.append module_name' base', SOME stmt));
      in
        Symtab.map_default (module_name', ([], ([], (reserved_names, reserved_names))))
              (apfst (fold (insert (op = : string * string -> bool)) deps))
        #> `(fn program => add_name ((snd o snd o the o Symtab.lookup program) module_name'))
        #-> (fn (base', names) =>
              (Symtab.map_entry module_name' o apsnd) (fn (stmts, _) =>
              (add_stmt' base' stmts, names)))
      end;
    val hs_program = fold add_stmt (AList.make (fn name =>
      (Graph.get_node program name, Graph.imm_succs program name))
      (Graph.strong_conn program |> flat)) Symtab.empty;
    fun deresolver name =
      (fst o the o AList.lookup (op =) ((fst o snd o the
        o Symtab.lookup hs_program) ((mk_name_module o fst o dest_name) name))) name
        handle Option => error ("Unknown statement name: " ^ labelled_name name);
  in (deresolver, hs_program) end;

fun serialize_haskell module_prefix raw_module_name string_classes labelled_name
    reserved_names includes raw_module_alias
    syntax_class syntax_tyco syntax_const program cs destination =
  let
    val stmt_names = stmt_names_of_destination destination;
    val module_name = if null stmt_names then raw_module_name else SOME "Code";
    val (deresolver, hs_program) = haskell_program_of_program labelled_name
      module_name module_prefix reserved_names raw_module_alias program;
    val is_cons = CodeThingol.is_cons program;
    val contr_classparam_typs = CodeThingol.contr_classparam_typs program;
    fun deriving_show tyco =
      let
        fun deriv _ "fun" = false
          | deriv tycos tyco = member (op =) tycos tyco orelse
              case try (Graph.get_node program) tyco
                of SOME (CodeThingol.Datatype (_, cs)) => forall (deriv' (tyco :: tycos))
                    (maps snd cs)
                 | NONE => true
        and deriv' tycos (tyco `%% tys) = deriv tycos tyco
              andalso forall (deriv' tycos) tys
          | deriv' _ (ITyVar _) = true
      in deriv [] tyco end;
    val reserved_names = CodeName.make_vars reserved_names;
    fun pr_stmt qualified = pr_haskell_stmt syntax_class syntax_tyco
      syntax_const labelled_name reserved_names
      (if qualified then deresolver else NameSpace.base o deresolver)
      is_cons contr_classparam_typs
      (if string_classes then deriving_show else K false);
    fun pr_module name content =
      (name, Pretty.chunks [
        str ("module " ^ name ^ " where {"),
        str "",
        content,
        str "",
        str "}"
      ]);
    fun serialize_module1 (module_name', (deps, (stmts, _))) =
      let
        val stmt_names = map fst stmts;
        val deps' = subtract (op =) stmt_names deps
          |> distinct (op =)
          |> map_filter (try deresolver);
        val qualified = is_none module_name andalso
          map deresolver stmt_names @ deps'
          |> map NameSpace.base
          |> has_duplicates (op =);
        val imports = deps'
          |> map NameSpace.qualifier
          |> distinct (op =);
        fun pr_import_include (name, _) = str ("import " ^ name ^ ";");
        val pr_import_module = str o (if qualified
          then prefix "import qualified "
          else prefix "import ") o suffix ";";
        val content = Pretty.chunks (
            map pr_import_include includes
            @ map pr_import_module imports
            @ str ""
            :: separate (str "") (map_filter
              (fn (name, (_, SOME stmt)) => SOME (pr_stmt qualified (name, stmt))
                | (_, (_, NONE)) => NONE) stmts)
          )
      in pr_module module_name' content end;
    fun serialize_module2 (_, (_, (stmts, _))) = Pretty.chunks (
      separate (str "") (map_filter
        (fn (name, (_, SOME stmt)) => if null stmt_names
              orelse member (op =) stmt_names name
              then SOME (pr_stmt false (name, stmt))
              else NONE
          | (_, (_, NONE)) => NONE) stmts));
    val serialize_module = case destination of String _ => pair "" o serialize_module2
      | _ => serialize_module1;
    fun write_module destination (modlname, content) =
      let
        val filename = case modlname
         of "" => Path.explode "Main.hs"
          | _ => (Path.ext "hs" o Path.explode o implode o separate "/"
                o NameSpace.explode) modlname;
        val pathname = Path.append destination filename;
        val _ = File.mkdir (Path.dir pathname);
      in File.write pathname (code_of_pretty content) end
    fun output Compile = error ("Haskell: no internal compilation")
      | output Export = K NONE o map (code_writeln o snd)
      | output (File destination) = K NONE o map (write_module destination)
      | output (String _) = SOME o rpair [] o cat_lines o map (code_of_pretty o snd);
  in
    output destination (map (uncurry pr_module) includes
      @ map serialize_module (Symtab.dest hs_program))
  end;

fun isar_seri_haskell module =
  parse_args (Scan.option (Args.$$$ "root" -- Args.colon |-- Args.name)
    -- Scan.optional (Args.$$$ "string_classes" >> K true) false
    >> (fn (module_prefix, string_classes) =>
      serialize_haskell module_prefix module string_classes));


(** optional pretty serialization **)

local

fun ocaml_char c =
  let
    fun chr i =
      let
        val xs = string_of_int i;
        val ys = replicate_string (3 - length (explode xs)) "0";
      in "\\" ^ ys ^ xs end;
    val i = ord c;
    val s = if i < 32 orelse i = 34 orelse i = 39 orelse i = 92 orelse i > 126
      then chr i else c
  in s end;

fun haskell_char c =
  let
    val s = ML_Syntax.print_char c;
  in if s = "'" then "\\'" else s end;

val pretty : (string * {
    pretty_char: string -> string,
    pretty_string: string -> string,
    pretty_numeral: bool -> int -> string,
    pretty_list: Pretty.T list -> Pretty.T,
    infix_cons: int * string
  }) list = [
  ("SML", { pretty_char = prefix "#" o quote o ML_Syntax.print_char,
      pretty_string = quote o translate_string ML_Syntax.print_char,
      pretty_numeral = fn unbounded => fn k =>
        if unbounded then "(" ^ string_of_int k ^ " : IntInf.int)"
        else string_of_int k,
      pretty_list = Pretty.enum "," "[" "]",
      infix_cons = (7, "::")}),
  ("OCaml", { pretty_char = enclose "'" "'" o ocaml_char,
      pretty_string = quote o translate_string ocaml_char,
      pretty_numeral = fn unbounded => fn k => if k >= 0 then
            if unbounded then
              "(Big_int.big_int_of_int " ^ string_of_int k ^ ")"
            else string_of_int k
          else
            if unbounded then
              "(Big_int.big_int_of_int " ^ (enclose "(" ")" o prefix "-"
                o string_of_int o op ~) k ^ ")"
            else (enclose "(" ")" o prefix "-" o string_of_int o op ~) k,
      pretty_list = Pretty.enum ";" "[" "]",
      infix_cons = (6, "::")}),
  ("Haskell", { pretty_char = enclose "'" "'" o haskell_char,
      pretty_string = quote o translate_string haskell_char,
      pretty_numeral = fn unbounded => fn k => if k >= 0 then string_of_int k
          else enclose "(" ")" (signed_string_of_int k),
      pretty_list = Pretty.enum "," "[" "]",
      infix_cons = (5, ":")})
];

in

fun pr_pretty target = case AList.lookup (op =) pretty target
 of SOME x => x
  | NONE => error ("Unknown code target language: " ^ quote target);

fun default_list (target_fxy, target_cons) pr fxy t1 t2 =
  brackify_infix (target_fxy, R) fxy [
    pr (INFX (target_fxy, X)) t1,
    str target_cons,
    pr (INFX (target_fxy, R)) t2
  ];

fun pretty_list c_nil c_cons target =
  let
    val pretty_ops = pr_pretty target;
    val mk_list = #pretty_list pretty_ops;
    fun pretty pr thm pat vars fxy [(t1, _), (t2, _)] =
      case Option.map (cons t1) (implode_list c_nil c_cons t2)
       of SOME ts => mk_list (map (pr vars NOBR) ts)
        | NONE => default_list (#infix_cons pretty_ops) (pr vars) fxy t1 t2;
  in (2, pretty) end;

fun pretty_list_string c_nil c_cons c_char c_nibbles target =
  let
    val pretty_ops = pr_pretty target;
    val mk_list = #pretty_list pretty_ops;
    val mk_char = #pretty_char pretty_ops;
    val mk_string = #pretty_string pretty_ops;
    fun pretty pr thm pat vars fxy [(t1, _), (t2, _)] =
      case Option.map (cons t1) (implode_list c_nil c_cons t2)
       of SOME ts => (case implode_string c_char c_nibbles mk_char mk_string ts
           of SOME p => p
            | NONE => mk_list (map (pr vars NOBR) ts))
        | NONE => default_list (#infix_cons pretty_ops) (pr vars) fxy t1 t2;
  in (2, pretty) end;

fun pretty_char c_char c_nibbles target =
  let
    val mk_char = #pretty_char (pr_pretty target);
    fun pretty _ thm _ _ _ [(t1, _), (t2, _)] =
      case decode_char c_nibbles (t1, t2)
       of SOME c => (str o mk_char) c
        | NONE => nerror thm "Illegal character expression";
  in (2, pretty) end;

fun pretty_numeral unbounded negative c_pls c_min c_bit0 c_bit1 target =
  let
    val mk_numeral = #pretty_numeral (pr_pretty target);
    fun pretty _ thm _ _ _ [(t, _)] =
      (str o mk_numeral unbounded o implode_numeral thm negative c_pls c_min c_bit0 c_bit1) t;
  in (1, pretty) end;

fun pretty_message c_char c_nibbles c_nil c_cons target =
  let
    val pretty_ops = pr_pretty target;
    val mk_char = #pretty_char pretty_ops;
    val mk_string = #pretty_string pretty_ops;
    fun pretty _ thm _ _ _ [(t, _)] =
      case implode_list c_nil c_cons t
       of SOME ts => (case implode_string c_char c_nibbles mk_char mk_string ts
           of SOME p => p
            | NONE => nerror thm "Illegal message expression")
        | NONE => nerror thm "Illegal message expression";
  in (1, pretty) end;

end; (*local*)


(** serializer use cases **)

(* evaluation *)

fun eval eval'' term_of reff thy ct args =
  let
    val _ = if null (term_frees (term_of ct)) then () else error ("Term "
      ^ quote (Syntax.string_of_term_global thy (term_of ct))
      ^ " to be evaluated contains free variables");
    fun eval' program ((vs, ty), t) deps =
      let
        val _ = if CodeThingol.contains_dictvar t then
          error "Term to be evaluated constains free dictionaries" else ();
        val program' = program
          |> Graph.new_node (CodeName.value_name, CodeThingol.Fun (([], ty), [(([], t), Drule.dummy_thm)]))
          |> fold (curry Graph.add_edge CodeName.value_name) deps;
        val (value_code, [value_name']) = ml_code_of thy program' [CodeName.value_name];
        val sml_code = "let\n" ^ value_code ^ "\nin " ^ value_name'
          ^ space_implode " " (map (enclose "(" ")") args) ^ " end";
      in ML_Context.evaluate Output.ml_output false reff sml_code end;
  in eval'' thy (fn t => (t, eval')) ct end;

fun eval_conv reff = eval CodeThingol.eval_conv Thm.term_of reff;
fun eval_term reff = eval CodeThingol.eval_term I reff;


(* instrumentalization by antiquotation *)

local

structure CodeAntiqData = ProofDataFun
(
  type T = string list * (bool * (string * (string * (string * string) list) Susp.T));
  fun init _ = ([], (true, ("", Susp.value ("", []))));
);

val is_first_occ = fst o snd o CodeAntiqData.get;

fun delayed_code thy consts () =
  let
    val (consts', program) = CodeThingol.consts_program thy consts;
    val (ml_code, consts'') = ml_code_of thy program consts';
    val _ = if length consts <> length consts'' then
      error ("One of the constants " ^ commas (map (quote o CodeUnit.string_of_const thy) consts)
        ^ "\nhas a user-defined serialization") else ();
  in (ml_code, consts ~~ consts'') end;

fun register_const const ctxt =
  let
    val (consts, (_, (struct_name, _))) = CodeAntiqData.get ctxt;
    val consts' = insert (op =) const consts;
    val (struct_name', ctxt') = if struct_name = ""
      then ML_Antiquote.variant "Code" ctxt
      else (struct_name, ctxt);
    val acc_code = Susp.delay (delayed_code (ProofContext.theory_of ctxt) consts');
  in CodeAntiqData.put (consts', (false, (struct_name', acc_code))) ctxt' end;

fun print_code struct_name is_first const ctxt =
  let
    val (consts, (_, (struct_code_name, acc_code))) = CodeAntiqData.get ctxt;
    val (raw_ml_code, consts_map) = Susp.force acc_code;
    val const'' = NameSpace.append (NameSpace.append struct_name struct_code_name)
      ((the o AList.lookup (op =) consts_map) const);
    val ml_code = if is_first then "\nstructure " ^ struct_code_name
        ^ " =\nstruct\n\n" ^ raw_ml_code ^ "\nend;\n\n"
      else "";
  in (ml_code, const'') end;

in

fun ml_code_antiq raw_const {struct_name, background} =
  let
    val const = CodeUnit.check_const (ProofContext.theory_of background) raw_const;
    val is_first = is_first_occ background;
    val background' = register_const const background;
  in (print_code struct_name is_first const, background') end;

end; (*local*)


(* code presentation *)

fun code_of thy target module_name cs stmt_names =
  let
    val (cs', program) = CodeThingol.consts_program thy cs;
  in
    string stmt_names (serialize thy target (SOME module_name) [] program cs')
  end;


(* code generation *)

fun read_const_exprs thy cs =
  let
    val (cs1, cs2) = CodeName.read_const_exprs thy cs;
    val (cs3, program) = CodeThingol.consts_program thy cs2;
    val cs4 = CodeThingol.transitivly_non_empty_funs program (abort_allowed thy);
    val cs5 = map_filter
      (fn (c, c') => if member (op =) cs4 c' then SOME c else NONE) (cs2 ~~ cs3);
  in fold (insert (op =)) cs5 cs1 end;

fun cached_program thy = 
  let
    val program = CodeThingol.cached_program thy;
  in (CodeThingol.transitivly_non_empty_funs program (abort_allowed thy), program) end

fun export_code thy cs seris =
  let
    val (cs', program) = if null cs then cached_program thy
      else CodeThingol.consts_program thy cs;
    fun mk_seri_dest dest = case dest
     of NONE => compile
      | SOME "-" => export
      | SOME f => file (Path.explode f)
    val _ = map (fn (((target, module), dest), args) =>
      (mk_seri_dest dest (serialize thy target module args program cs'))) seris;
  in () end;

fun export_code_cmd raw_cs seris thy = export_code thy (read_const_exprs thy raw_cs) seris;


(** serializer data **)

(* infix syntax *)

datatype 'a mixfix =
    Arg of fixity
  | Pretty of Pretty.T;

fun mk_mixfix prep_arg (fixity_this, mfx) =
  let
    fun is_arg (Arg _) = true
      | is_arg _ = false;
    val i = (length o filter is_arg) mfx;
    fun fillin _ [] [] =
          []
      | fillin pr (Arg fxy :: mfx) (a :: args) =
          (pr fxy o prep_arg) a :: fillin pr mfx args
      | fillin pr (Pretty p :: mfx) args =
          p :: fillin pr mfx args;
  in
    (i, fn pr => fn fixity_ctxt => fn args =>
      gen_brackify (fixity fixity_this fixity_ctxt) (fillin pr mfx args))
  end;

fun parse_infix prep_arg (x, i) s =
  let
    val l = case x of L => INFX (i, L) | _ => INFX (i, X);
    val r = case x of R => INFX (i, R) | _ => INFX (i, X);
  in
    mk_mixfix prep_arg (INFX (i, x),
      [Arg l, (Pretty o Pretty.brk) 1, (Pretty o str) s, (Pretty o Pretty.brk) 1, Arg r])
  end;


(* data access *)

local

fun cert_class thy class =
  let
    val _ = AxClass.get_info thy class;
  in class end;

fun read_class thy = cert_class thy o Sign.intern_class thy;

fun cert_tyco thy tyco =
  let
    val _ = if Sign.declared_tyname thy tyco then ()
      else error ("No such type constructor: " ^ quote tyco);
  in tyco end;

fun read_tyco thy = cert_tyco thy o Sign.intern_type thy;

fun gen_add_syntax_class prep_class prep_const target raw_class raw_syn thy =
  let
    val class = prep_class thy raw_class;
    val class' = CodeName.class thy class;
    fun mk_classparam c = case AxClass.class_of_param thy c
     of SOME class'' => if class = class'' then CodeName.const thy c
          else error ("Not a class operation for class " ^ quote class ^ ": " ^ quote c)
      | NONE => error ("Not a class operation: " ^ quote c);
    fun mk_syntax_params raw_params = AList.lookup (op =)
      ((map o apfst) (mk_classparam o prep_const thy) raw_params);
  in case raw_syn
   of SOME (syntax, raw_params) =>
      thy
      |> (map_name_syntax target o apfst o apfst)
           (Symtab.update (class', (syntax, mk_syntax_params raw_params)))
    | NONE =>
      thy
      |> (map_name_syntax target o apfst o apfst)
           (Symtab.delete_safe class')
  end;

fun gen_add_syntax_inst prep_class prep_tyco target (raw_tyco, raw_class) add_del thy =
  let
    val inst = CodeName.instance thy (prep_class thy raw_class, prep_tyco thy raw_tyco);
  in if add_del then
    thy
    |> (map_name_syntax target o apfst o apsnd)
        (Symtab.update (inst, ()))
  else
    thy
    |> (map_name_syntax target o apfst o apsnd)
        (Symtab.delete_safe inst)
  end;

fun gen_add_syntax_tyco prep_tyco target raw_tyco raw_syn thy =
  let
    val tyco = prep_tyco thy raw_tyco;
    val tyco' = if tyco = "fun" then "fun" else CodeName.tyco thy tyco;
    fun check_args (syntax as (n, _)) = if n <> Sign.arity_number thy tyco
      then error ("Number of arguments mismatch in syntax for type constructor " ^ quote tyco)
      else syntax
  in case raw_syn
   of SOME syntax =>
      thy
      |> (map_name_syntax target o apsnd o apfst)
           (Symtab.update (tyco', check_args syntax))
   | NONE =>
      thy
      |> (map_name_syntax target o apsnd o apfst)
           (Symtab.delete_safe tyco')
  end;

fun simple_const_syntax x = (Option.map o apsnd)
  (fn pretty => fn pr => fn thm => fn pat => fn vars => pretty (pr vars)) x;

fun gen_add_syntax_const prep_const target raw_c raw_syn thy =
  let
    val c = prep_const thy raw_c;
    val c' = CodeName.const thy c;
    fun check_args (syntax as (n, _)) = if n > CodeUnit.no_args thy c
      then error ("Too many arguments in syntax for constant " ^ quote c)
      else syntax;
  in case raw_syn
   of SOME syntax =>
      thy
      |> (map_name_syntax target o apsnd o apsnd)
           (Symtab.update (c', check_args syntax))
   | NONE =>
      thy
      |> (map_name_syntax target o apsnd o apsnd)
           (Symtab.delete_safe c')
  end;

fun add_reserved target =
  let
    fun add sym syms = if member (op =) syms sym
      then error ("Reserved symbol " ^ quote sym ^ " already declared")
      else insert (op =) sym syms
  in map_reserved target o add end;

fun add_include target =
  let
    fun add (name, SOME content) incls =
          let
            val _ = if Symtab.defined incls name
              then warning ("Overwriting existing include " ^ name)
              else ();
          in Symtab.update (name, str content) incls end
      | add (name, NONE) incls =
          Symtab.delete name incls;
  in map_includes target o add end;

fun add_module_alias target =
  map_module_alias target o Symtab.update o apsnd CodeName.check_modulename;

fun add_monad target raw_c_run raw_c_bind thy =
  let
    val c_run = CodeUnit.read_const thy raw_c_run;
    val c_bind = CodeUnit.read_const thy raw_c_bind;
    val c_bind' = CodeName.const thy c_bind;
  in if target = target_Haskell then
    thy
    |> gen_add_syntax_const (K I) target_Haskell c_run
          (SOME (pretty_haskell_monad c_bind'))
    |> gen_add_syntax_const (K I) target_Haskell c_bind
          (simple_const_syntax (SOME (parse_infix fst (L, 1) ">>=")))
  else error "Only Haskell target allows for monad syntax" end;

fun gen_allow_abort prep_cs raw_c thy =
  let
    val c = prep_cs thy raw_c;
    val c' = CodeName.const thy c;
  in thy |> (CodeTargetData.map o apsnd) (insert (op =) c') end;

fun zip_list (x::xs) f g =
  f
  #-> (fn y =>
    fold_map (fn x => g |-- f >> pair x) xs
    #-> (fn xys => pair ((x, y) :: xys)));


(* concrete syntax *)

structure P = OuterParse
and K = OuterKeyword

fun parse_multi_syntax parse_thing parse_syntax =
  P.and_list1 parse_thing
  #-> (fn things => Scan.repeat1 (P.$$$ "(" |-- P.name --
        (zip_list things parse_syntax (P.$$$ "and")) --| P.$$$ ")"));

val (infixK, infixlK, infixrK) = ("infix", "infixl", "infixr");

fun parse_mixfix prep_arg s =
  let
    val sym_any = Scan.one Symbol.is_regular;
    val parse = Scan.optional ($$ "!" >> K true) false -- Scan.repeat (
         ($$ "(" -- $$ "_" -- $$ ")" >> K (Arg NOBR))
      || ($$ "_" >> K (Arg BR))
      || ($$ "/" |-- Scan.repeat ($$ " ") >> (Pretty o Pretty.brk o length))
      || (Scan.repeat1
           (   $$ "'" |-- sym_any
            || Scan.unless ($$ "_" || $$ "/" || $$ "(" |-- $$ "_" |-- $$ ")")
                 sym_any) >> (Pretty o str o implode)));
  in case Scan.finite Symbol.stopper parse (Symbol.explode s)
   of ((_, p as [_]), []) => mk_mixfix prep_arg (NOBR, p)
    | ((b, p as _ :: _ :: _), []) => mk_mixfix prep_arg (if b then NOBR else BR, p)
    | _ => Scan.!!
        (the_default ("malformed mixfix annotation: " ^ quote s) o snd) Scan.fail ()
  end;

fun parse_syntax prep_arg xs =
  Scan.option ((
      ((P.$$$ infixK  >> K X)
        || (P.$$$ infixlK >> K L)
        || (P.$$$ infixrK >> K R))
        -- P.nat >> parse_infix prep_arg
      || Scan.succeed (parse_mixfix prep_arg))
      -- P.string
      >> (fn (parse, s) => parse s)) xs;

in

val parse_syntax = parse_syntax;

val add_syntax_class = gen_add_syntax_class cert_class (K I);
val add_syntax_inst = gen_add_syntax_inst cert_class cert_tyco;
val add_syntax_tyco = gen_add_syntax_tyco cert_tyco;
val add_syntax_const = gen_add_syntax_const (K I);
val allow_abort = gen_allow_abort (K I);

val add_syntax_class_cmd = gen_add_syntax_class read_class CodeUnit.read_const;
val add_syntax_inst_cmd = gen_add_syntax_inst read_class read_tyco;
val add_syntax_tyco_cmd = gen_add_syntax_tyco read_tyco;
val add_syntax_const_cmd = gen_add_syntax_const CodeUnit.read_const;
val allow_abort_cmd = gen_allow_abort CodeUnit.read_const;

fun add_syntax_tycoP target tyco = parse_syntax I >> add_syntax_tyco_cmd target tyco;
fun add_syntax_constP target c = parse_syntax fst >> (add_syntax_const_cmd target c o simple_const_syntax);

fun add_undefined target undef target_undefined thy =
  let
    fun pr _ _ _ _ _ _ = str target_undefined;
  in
    thy
    |> add_syntax_const target undef (SOME (~1, pr))
  end;

fun add_pretty_list target nill cons thy =
  let
    val nil' = CodeName.const thy nill;
    val cons' = CodeName.const thy cons;
    val pr = pretty_list nil' cons' target;
  in
    thy
    |> add_syntax_const target cons (SOME pr)
  end;

fun add_pretty_list_string target nill cons charr nibbles thy =
  let
    val nil' = CodeName.const thy nill;
    val cons' = CodeName.const thy cons;
    val charr' = CodeName.const thy charr;
    val nibbles' = map (CodeName.const thy) nibbles;
    val pr = pretty_list_string nil' cons' charr' nibbles' target;
  in
    thy
    |> add_syntax_const target cons (SOME pr)
  end;

fun add_pretty_char target charr nibbles thy =
  let
    val charr' = CodeName.const thy charr;
    val nibbles' = map (CodeName.const thy) nibbles;
    val pr = pretty_char charr' nibbles' target;
  in
    thy
    |> add_syntax_const target charr (SOME pr)
  end;

fun add_pretty_numeral target unbounded negative number_of pls min bit0 bit1 thy =
  let
    val pls' = CodeName.const thy pls;
    val min' = CodeName.const thy min;
    val bit0' = CodeName.const thy bit0;
    val bit1' = CodeName.const thy bit1;
    val pr = pretty_numeral unbounded negative pls' min' bit0' bit1' target;
  in
    thy
    |> add_syntax_const target number_of (SOME pr)
  end;

fun add_pretty_message target charr nibbles nill cons str thy =
  let
    val charr' = CodeName.const thy charr;
    val nibbles' = map (CodeName.const thy) nibbles;
    val nil' = CodeName.const thy nill;
    val cons' = CodeName.const thy cons;
    val pr = pretty_message charr' nibbles' nil' cons' target;
  in
    thy
    |> add_syntax_const target str (SOME pr)
  end;



(** Isar setup **)

val (inK, module_nameK, fileK) = ("in", "module_name", "file");

fun code_exprP cmd =
  (Scan.repeat P.term_group
  -- Scan.repeat (P.$$$ inK |-- P.name
     -- Scan.option (P.$$$ module_nameK |-- P.name)
     -- Scan.option (P.$$$ fileK |-- P.name)
     -- Scan.optional (P.$$$ "(" |-- P.arguments --| P.$$$ ")") []
  ) >> (fn (raw_cs, seris) => cmd raw_cs seris));

val _ = List.app OuterKeyword.keyword [infixK, infixlK, infixrK, inK, module_nameK, fileK];

val _ =
  OuterSyntax.command "code_class" "define code syntax for class" K.thy_decl (
    parse_multi_syntax P.xname
      (Scan.option (P.string -- Scan.optional (P.$$$ "where" |-- Scan.repeat1
        (P.term_group --| (P.$$$ "\<equiv>" || P.$$$ "==") -- P.string)) []))
    >> (Toplevel.theory oo fold) (fn (target, syns) =>
          fold (fn (raw_class, syn) => add_syntax_class_cmd target raw_class syn) syns)
  );

val _ =
  OuterSyntax.command "code_instance" "define code syntax for instance" K.thy_decl (
    parse_multi_syntax (P.xname --| P.$$$ "::" -- P.xname)
      ((P.minus >> K true) || Scan.succeed false)
    >> (Toplevel.theory oo fold) (fn (target, syns) =>
          fold (fn (raw_inst, add_del) => add_syntax_inst_cmd target raw_inst add_del) syns)
  );

val _ =
  OuterSyntax.command "code_type" "define code syntax for type constructor" K.thy_decl (
    parse_multi_syntax P.xname (parse_syntax I)
    >> (Toplevel.theory oo fold) (fn (target, syns) =>
          fold (fn (raw_tyco, syn) => add_syntax_tyco_cmd target raw_tyco syn) syns)
  );

val _ =
  OuterSyntax.command "code_const" "define code syntax for constant" K.thy_decl (
    parse_multi_syntax P.term_group (parse_syntax fst)
    >> (Toplevel.theory oo fold) (fn (target, syns) =>
          fold (fn (raw_const, syn) => add_syntax_const_cmd target raw_const (simple_const_syntax syn)) syns)
  );

val _ =
  OuterSyntax.command "code_monad" "define code syntax for monads" K.thy_decl (
    P.term_group -- P.term_group -- P.name
    >> (fn ((raw_run, raw_bind), target) => Toplevel.theory 
          (add_monad target raw_run raw_bind))
  );

val _ =
  OuterSyntax.command "code_reserved" "declare words as reserved for target language" K.thy_decl (
    P.name -- Scan.repeat1 P.name
    >> (fn (target, reserveds) => (Toplevel.theory o fold (add_reserved target)) reserveds)
  );

val _ =
  OuterSyntax.command "code_include" "declare piece of code to be included in generated code" K.thy_decl (
    P.name -- P.name -- (P.text >> (fn "-" => NONE | s => SOME s))
    >> (fn ((target, name), content) => (Toplevel.theory o add_include target)
      (name, content))
  );

val _ =
  OuterSyntax.command "code_modulename" "alias module to other name" K.thy_decl (
    P.name -- Scan.repeat1 (P.name -- P.name)
    >> (fn (target, modlnames) => (Toplevel.theory o fold (add_module_alias target)) modlnames)
  );

val _ =
  OuterSyntax.command "code_abort" "permit constant to be implemented as program abort" K.thy_decl (
    Scan.repeat1 P.term_group >> (Toplevel.theory o fold allow_abort_cmd)
  );

val _ =
  OuterSyntax.command "export_code" "generate executable code for constants"
    K.diag (P.!!! (code_exprP export_code_cmd) >> (fn f => Toplevel.keep (f o Toplevel.theory_of)));

fun shell_command thyname cmd = Toplevel.program (fn _ =>
  (use_thy thyname; case Scan.read OuterLex.stopper (P.!!! (code_exprP export_code_cmd)) ((filter OuterLex.is_proper o OuterSyntax.scan) cmd)
   of SOME f => (writeln "Now generating code..."; f (theory thyname))
    | NONE => error ("Bad directive " ^ quote cmd)))
  handle TOPLEVEL_ERROR => OS.Process.exit OS.Process.failure;

val _ = ML_Context.add_antiq "code" (Args.term >> ml_code_antiq);


(* serializer setup, including serializer defaults *)

val setup =
  add_target (target_SML, isar_seri_sml)
  #> add_target (target_OCaml, isar_seri_ocaml)
  #> add_target (target_Haskell, isar_seri_haskell)
  #> add_syntax_tyco "SML" "fun" (SOME (2, fn pr_typ => fn fxy => fn [ty1, ty2] =>
      brackify_infix (1, R) fxy [
        pr_typ (INFX (1, X)) ty1,
        str "->",
        pr_typ (INFX (1, R)) ty2
      ]))
  #> add_syntax_tyco "OCaml" "fun" (SOME (2, fn pr_typ => fn fxy => fn [ty1, ty2] =>
      brackify_infix (1, R) fxy [
        pr_typ (INFX (1, X)) ty1,
        str "->",
        pr_typ (INFX (1, R)) ty2
      ]))
  #> add_syntax_tyco "Haskell" "fun" (SOME (2, fn pr_typ => fn fxy => fn [ty1, ty2] =>
      brackify_infix (1, R) fxy [
        pr_typ (INFX (1, X)) ty1,
        str "->",
        pr_typ (INFX (1, R)) ty2
      ]))
  #> fold (add_reserved "SML") ML_Syntax.reserved_names
  #> fold (add_reserved "SML")
      ["o" (*dictionary projections use it already*), "Fail", "div", "mod" (*standard infixes*)]
  #> fold (add_reserved "OCaml") [
      "and", "as", "assert", "begin", "class",
      "constraint", "do", "done", "downto", "else", "end", "exception",
      "external", "false", "for", "fun", "function", "functor", "if",
      "in", "include", "inherit", "initializer", "lazy", "let", "match", "method",
      "module", "mutable", "new", "object", "of", "open", "or", "private", "rec",
      "sig", "struct", "then", "to", "true", "try", "type", "val",
      "virtual", "when", "while", "with"
    ]
  #> fold (add_reserved "OCaml") ["failwith", "mod"]
  #> fold (add_reserved "Haskell") [
      "hiding", "deriving", "where", "case", "of", "infix", "infixl", "infixr",
      "import", "default", "forall", "let", "in", "class", "qualified", "data",
      "newtype", "instance", "if", "then", "else", "type", "as", "do", "module"
    ]
  #> fold (add_reserved "Haskell") [
      "Prelude", "Main", "Bool", "Maybe", "Either", "Ordering", "Char", "String", "Int",
      "Integer", "Float", "Double", "Rational", "IO", "Eq", "Ord", "Enum", "Bounded",
      "Num", "Real", "Integral", "Fractional", "Floating", "RealFloat", "Monad", "Functor",
      "AlreadyExists", "ArithException", "ArrayException", "AssertionFailed", "AsyncException",
      "BlockedOnDeadMVar", "Deadlock", "Denormal", "DivideByZero", "DotNetException", "DynException",
      "Dynamic", "EOF", "EQ", "EmptyRec", "ErrorCall", "ExitException", "ExitFailure",
      "ExitSuccess", "False", "GT", "HeapOverflow",
      "IOError", "IOException", "IllegalOperation",
      "IndexOutOfBounds", "Just", "Key", "LT", "Left", "LossOfPrecision", "NoMethodError",
      "NoSuchThing", "NonTermination", "Nothing", "Obj", "OtherError", "Overflow",
      "PatternMatchFail", "PermissionDenied", "ProtocolError", "RecConError", "RecSelError",
      "RecUpdError", "ResourceBusy", "ResourceExhausted", "Right", "StackOverflow",
      "ThreadKilled", "True", "TyCon", "TypeRep", "UndefinedElement", "Underflow",
      "UnsupportedOperation", "UserError", "abs", "absReal", "acos", "acosh", "all",
      "and", "any", "appendFile", "asTypeOf", "asciiTab", "asin", "asinh", "atan",
      "atan2", "atanh", "basicIORun", "blockIO", "boundedEnumFrom", "boundedEnumFromThen",
      "boundedEnumFromThenTo", "boundedEnumFromTo", "boundedPred", "boundedSucc", "break",
      "catch", "catchException", "ceiling", "compare", "concat", "concatMap", "const",
      "cos", "cosh", "curry", "cycle", "decodeFloat", "denominator", "div", "divMod",
      "doubleToRatio", "doubleToRational", "drop", "dropWhile", "either", "elem",
      "emptyRec", "encodeFloat", "enumFrom", "enumFromThen", "enumFromThenTo",
      "enumFromTo", "error", "even", "exp", "exponent", "fail", "filter", "flip",
      "floatDigits", "floatProperFraction", "floatRadix", "floatRange", "floatToRational",
      "floor", "fmap", "foldl", "foldl'", "foldl1", "foldr", "foldr1", "fromDouble",
      "fromEnum", "fromEnum_0", "fromInt", "fromInteger", "fromIntegral", "fromObj",
      "fromRational", "fst", "gcd", "getChar", "getContents", "getLine", "head",
      "id", "inRange", "index", "init", "intToRatio", "interact", "ioError", "isAlpha",
      "isAlphaNum", "isDenormalized", "isDigit", "isHexDigit", "isIEEE", "isInfinite",
      "isLower", "isNaN", "isNegativeZero", "isOctDigit", "isSpace", "isUpper", "iterate", "iterate'",
      "last", "lcm", "length", "lex", "lexDigits", "lexLitChar", "lexmatch", "lines", "log",
      "logBase", "lookup", "loop", "map", "mapM", "mapM_", "max", "maxBound", "maximum",
      "maybe", "min", "minBound", "minimum", "mod", "negate", "nonnull", "not", "notElem",
      "null", "numerator", "numericEnumFrom", "numericEnumFromThen", "numericEnumFromThenTo",
      "numericEnumFromTo", "odd", "or", "otherwise", "pi", "pred", 
      "print", "product", "properFraction", "protectEsc", "putChar", "putStr", "putStrLn",
      "quot", "quotRem", "range", "rangeSize", "rationalToDouble", "rationalToFloat",
      "rationalToRealFloat", "read", "readDec", "readField", "readFieldName", "readFile",
      "readFloat", "readHex", "readIO", "readInt", "readList", "readLitChar", "readLn",
      "readOct", "readParen", "readSigned", "reads", "readsPrec", "realFloatToRational",
      "realToFrac", "recip", "reduce", "rem", "repeat", "replicate", "return", "reverse",
      "round", "scaleFloat", "scanl", "scanl1", "scanr", "scanr1", "seq", "sequence",
      "sequence_", "show", "showChar", "showException", "showField", "showList",
      "showLitChar", "showParen", "showString", "shows", "showsPrec", "significand",
      "signum", "signumReal", "sin", "sinh", "snd", "span", "splitAt", "sqrt", "subtract",
      "succ", "sum", "tail", "take", "takeWhile", "takeWhile1", "tan", "tanh", "threadToIOResult",
      "throw", "toEnum", "toInt", "toInteger", "toObj", "toRational", "truncate", "uncurry",
      "undefined", "unlines", "unsafeCoerce", "unsafeIndex", "unsafeRangeSize", "until", "unwords",
      "unzip", "unzip3", "userError", "words", "writeFile", "zip", "zip3", "zipWith", "zipWith3"
    ] (*due to weird handling of ':', we can't do anything else than to import *all* prelude symbols*);

end; (*local*)

end; (*struct*)
