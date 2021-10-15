(*  Title:      HOL/Tools/Ctr_Sugar/case_translation.ML
    Author:     Konrad Slind, Cambridge University Computer Laboratory
    Author:     Stefan Berghofer, TU Muenchen
    Author:     Dmitriy Traytel, TU Muenchen

Nested case expressions via a generic data slot for case combinators and constructors.
*)

signature CASE_TRANSLATION =
sig
  val indexify_names: string list -> string list
  val make_tnames: typ list -> string list

  datatype config = Error | Warning | Quiet
  val case_tr: bool -> Proof.context -> term list -> term
  val lookup_by_constr: Proof.context -> string * typ -> (term * term list) option
  val lookup_by_constr_permissive: Proof.context -> string * typ -> (term * term list) option
  val lookup_by_case: Proof.context -> string -> (term * term list) option
  val make_case:  Proof.context -> config -> Name.context -> term -> (term * term) list -> term
  val print_case_translations: Proof.context -> unit
  val strip_case: Proof.context -> bool -> term -> (term * (term * term) list) option
  val strip_case_full: Proof.context -> bool -> term -> term
  val show_cases: bool Config.T
  val register: term -> term list -> Context.generic -> Context.generic
end;

structure Case_Translation: CASE_TRANSLATION =
struct

(** general utilities **)

fun indexify_names names =
  let
    fun index (x :: xs) tab =
        (case AList.lookup (op =) tab x of
          NONE =>
            if member (op =) xs x
            then (x ^ "1") :: index xs ((x, 2) :: tab)
            else x :: index xs tab
        | SOME i => (x ^ string_of_int i) :: index xs ((x, i + 1) :: tab))
      | index [] _ = [];
  in index names [] end;

fun make_tnames Ts =
  let
    fun type_name (TFree (name, _)) = unprefix "'" name
      | type_name (TVar ((name, idx), _)) =
          unprefix "'" name ^ (if idx = 0 then "" else string_of_int idx)
      | type_name (Type (name, _)) =
          let val name' = Long_Name.base_name name
          in if Symbol_Pos.is_identifier name' then name' else "x" end;
  in indexify_names (map type_name Ts) end;



(** data management **)

datatype data = Data of
  {constrs: (string * (term * term list)) list Symtab.table,
   cases: (term * term list) Symtab.table};

fun make_data (constrs, cases) = Data {constrs = constrs, cases = cases};

structure Data = Generic_Data
(
  type T = data;
  val empty = make_data (Symtab.empty, Symtab.empty);
  val extend = I;
  fun merge
    (Data {constrs = constrs1, cases = cases1},
     Data {constrs = constrs2, cases = cases2}) =
    make_data
      (Symtab.join (K (AList.merge (op =) (K true))) (constrs1, constrs2),
      Symtab.merge (K true) (cases1, cases2));
);

fun map_data f =
  Data.map (fn Data {constrs, cases} => make_data (f (constrs, cases)));
fun map_constrs f = map_data (fn (constrs, cases) => (f constrs, cases));
fun map_cases f = map_data (fn (constrs, cases) => (constrs, f cases));

val rep_data = (fn Data args => args) o Data.get o Context.Proof;

fun T_of_data (comb, constrs : term list) =
  fastype_of comb
  |> funpow (length constrs) range_type
  |> domain_type;

val Tname_of_data = fst o dest_Type o T_of_data;

val constrs_of = #constrs o rep_data;
val cases_of = #cases o rep_data;

fun lookup_by_constr ctxt (c, T) =
  let
    val tab = Symtab.lookup_list (constrs_of ctxt) c;
  in
    (case body_type T of
      Type (tyco, _) => AList.lookup (op =) tab tyco
    | _ => NONE)
  end;

fun lookup_by_constr_permissive ctxt (c, T) =
  let
    val tab = Symtab.lookup_list (constrs_of ctxt) c;
    val hint = (case body_type T of Type (tyco, _) => SOME tyco | _ => NONE);
    val default = if null tab then NONE else SOME (snd (List.last tab));
    (*conservative wrt. overloaded constructors*)
  in
    (case hint of
      NONE => default
    | SOME tyco =>
        (case AList.lookup (op =) tab tyco of
          NONE => default (*permissive*)
        | SOME info => SOME info))
  end;

val lookup_by_case = Symtab.lookup o cases_of;



(** installation **)

fun case_error s = error ("Error in case expression:\n" ^ s);

val name_of = try (dest_Const #> fst);


(* parse translation *)

fun constrain_Abs tT t = Syntax.const \<^syntax_const>\<open>_constrainAbs\<close> $ t $ tT;

fun case_tr err ctxt [t, u] =
      let
        val consts = Proof_Context.consts_of ctxt;
        fun is_const s = can (Consts.the_constraint consts) (Consts.intern consts s);

        fun variant_free x used =
          let val (x', used') = Name.variant x used
          in if is_const x' then variant_free x' used' else (x', used') end;

        fun abs p tTs t =
          Syntax.const \<^const_syntax>\<open>case_abs\<close> $
            fold constrain_Abs tTs (absfree p t);

        fun abs_pat (Const (\<^syntax_const>\<open>_constrain\<close>, _) $ t $ tT) tTs =
              abs_pat t (tT :: tTs)
          | abs_pat (Free (p as (x, _))) tTs =
              if is_const x then I else abs p tTs
          | abs_pat (t $ u) _ = abs_pat u [] #> abs_pat t []
          | abs_pat _ _ = I;

        (* replace occurrences of dummy_pattern by distinct variables *)
        fun replace_dummies (Const (\<^const_syntax>\<open>Pure.dummy_pattern\<close>, T)) used =
              let val (x, used') = variant_free "x" used
              in (Free (x, T), used') end
          | replace_dummies (t $ u) used =
              let
                val (t', used') = replace_dummies t used;
                val (u', used'') = replace_dummies u used';
              in (t' $ u', used'') end
          | replace_dummies t used = (t, used);

        fun dest_case1 (t as Const (\<^syntax_const>\<open>_case1\<close>, _) $ l $ r) =
              let val (l', _) = replace_dummies l (Term.declare_term_frees t Name.context) in
                abs_pat l' []
                  (Syntax.const \<^const_syntax>\<open>case_elem\<close> $ Term_Position.strip_positions l' $ r)
              end
          | dest_case1 _ = case_error "dest_case1";

        fun dest_case2 (Const (\<^syntax_const>\<open>_case2\<close>, _) $ t $ u) = t :: dest_case2 u
          | dest_case2 t = [t];

        val errt = Syntax.const (if err then \<^const_syntax>\<open>True\<close> else \<^const_syntax>\<open>False\<close>);
      in
        Syntax.const \<^const_syntax>\<open>case_guard\<close> $ errt $ t $
          (fold_rev
            (fn t => fn u => Syntax.const \<^const_syntax>\<open>case_cons\<close> $ dest_case1 t $ u)
            (dest_case2 u)
            (Syntax.const \<^const_syntax>\<open>case_nil\<close>))
      end
  | case_tr _ _ _ = case_error "case_tr";

val _ = Theory.setup (Sign.parse_translation [(\<^syntax_const>\<open>_case_syntax\<close>, case_tr true)]);


(* print translation *)

fun case_tr' (_ :: x :: t :: ts) =
      let
        fun mk_clause (Const (\<^const_syntax>\<open>case_abs\<close>, _) $ Abs (s, T, t)) xs used =
              let val (s', used') = Name.variant s used
              in mk_clause t ((s', T) :: xs) used' end
          | mk_clause (Const (\<^const_syntax>\<open>case_elem\<close>, _) $ pat $ rhs) xs _ =
              Syntax.const \<^syntax_const>\<open>_case1\<close> $
                subst_bounds (map Syntax_Trans.mark_bound_abs xs, pat) $
                subst_bounds (map Syntax_Trans.mark_bound_body xs, rhs)
          | mk_clause _ _ _ = raise Match;

        fun mk_clauses (Const (\<^const_syntax>\<open>case_nil\<close>, _)) = []
          | mk_clauses (Const (\<^const_syntax>\<open>case_cons\<close>, _) $ t $ u) =
              mk_clause t [] (Term.declare_term_frees t Name.context) :: mk_clauses u
          | mk_clauses _ = raise Match;
      in
        list_comb (Syntax.const \<^syntax_const>\<open>_case_syntax\<close> $ x $
          foldr1 (fn (t, u) => Syntax.const \<^syntax_const>\<open>_case2\<close> $ t $ u)
            (mk_clauses t), ts)
      end
  | case_tr' _ = raise Match;

val _ = Theory.setup (Sign.print_translation [(\<^const_syntax>\<open>case_guard\<close>, K case_tr')]);


(* declarations *)

fun register raw_case_comb raw_constrs context =
  let
    val ctxt = Context.proof_of context;
    val case_comb = singleton (Variable.polymorphic ctxt) raw_case_comb;
    val constrs = Variable.polymorphic ctxt raw_constrs;
    val case_key = case_comb |> dest_Const |> fst;
    val constr_keys = map (fst o dest_Const) constrs;
    val data = (case_comb, constrs);
    val Tname = Tname_of_data data;
    val update_constrs = fold (fn key => Symtab.cons_list (key, (Tname, data))) constr_keys;
    val update_cases = Symtab.update (case_key, data);
  in
    context
    |> map_constrs update_constrs
    |> map_cases update_cases
  end;

val _ = Theory.setup
  (Attrib.setup \<^binding>\<open>case_translation\<close>
    (Args.term -- Scan.repeat1 Args.term >>
      (fn (t, ts) => Thm.declaration_attribute (K (register t ts))))
    "declaration of case combinators and constructors");


(* (Un)check phases *)

datatype config = Error | Warning | Quiet;

exception CASE_ERROR of string * int;


(*Each pattern carries with it a tag i, which denotes the clause it
  came from. i = ~1 indicates that the clause was added by pattern
  completion.*)

fun add_row_used ((prfx, pats), (tm, _)) =
  fold Term.declare_term_frees (tm :: pats @ map Free prfx);

(*try to preserve names given by user*)
fun default_name "" (Free (name', _)) = name'
  | default_name name _ = name;


(*Produce an instance of a constructor, plus fresh variables for its arguments.*)
fun fresh_constr colty used c =
  let
    val (_, T) = dest_Const c;
    val Ts = binder_types T;
    val (names, _) = fold_map Name.variant (make_tnames Ts) used;
    val ty = body_type T;
    val ty_theta = Type.raw_match (ty, colty) Vartab.empty
      handle Type.TYPE_MATCH => raise CASE_ERROR ("type mismatch", ~1);
    val c' = Envir.subst_term_types ty_theta c;
    val gvars = map (Envir.subst_term_types ty_theta o Free) (names ~~ Ts);
  in (c', gvars) end;

(*Go through a list of rows and pick out the ones beginning with a
  pattern with constructor = name.*)
fun mk_group (name, T) rows =
  let val k = length (binder_types T) in
    fold (fn (row as ((prfx, p :: ps), rhs as (_, i))) =>
      fn ((in_group, not_in_group), names) =>
        (case strip_comb p of
          (Const (name', _), args) =>
            if name = name' then
              if length args = k then
                ((((prfx, args @ ps), rhs) :: in_group, not_in_group),
                 map2 default_name names args)
              else raise CASE_ERROR ("Wrong number of arguments for constructor " ^ quote name, i)
            else ((in_group, row :: not_in_group), names)
        | _ => raise CASE_ERROR ("Not a constructor pattern", i)))
    rows (([], []), replicate k "") |>> apply2 rev
  end;


(* Partitioning *)

fun partition _ _ _ _ [] = raise CASE_ERROR ("partition: no rows", ~1)
  | partition used constructors colty res_ty (rows as (((prfx, _ :: ps), _) :: _)) =
      let
        fun part [] [] = []
          | part [] ((_, (_, i)) :: _) = raise CASE_ERROR ("Not a constructor pattern", i)
          | part (c :: cs) rows =
              let
                val ((in_group, not_in_group), names) = mk_group (dest_Const c) rows;
                val used' = fold add_row_used in_group used;
                val (c', gvars) = fresh_constr colty used' c;
                val in_group' =
                  if null in_group  (* Constructor not given *)
                  then
                    let
                      val Ts = map fastype_of ps;
                      val (xs, _) =
                        fold_map Name.variant
                          (replicate (length ps) "x")
                          (fold Term.declare_term_frees gvars used');
                    in
                      [((prfx, gvars @ map Free (xs ~~ Ts)),
                        (Const (\<^const_name>\<open>undefined\<close>, res_ty), ~1))]
                    end
                  else in_group;
              in
                {constructor = c',
                 new_formals = gvars,
                 names = names,
                 group = in_group'} :: part cs not_in_group
              end;
      in part constructors rows end;

fun v_to_prfx (prfx, Free v :: pats) = (v :: prfx, pats)
  | v_to_prfx _ = raise CASE_ERROR ("mk_case: v_to_prfx", ~1);


(* Translation of pattern terms into nested case expressions. *)

fun mk_case ctxt used range_ty =
  let
    val get_info = lookup_by_constr_permissive ctxt;

    fun expand _ _ _ ((_, []), _) = raise CASE_ERROR ("mk_case: expand", ~1)
      | expand constructors used ty (row as ((prfx, p :: ps), (rhs, tag))) =
          if is_Free p then
            let
              val used' = add_row_used row used;
              fun expnd c =
                let val capp = list_comb (fresh_constr ty used' c)
                in ((prfx, capp :: ps), (subst_free [(p, capp)] rhs, tag)) end;
            in map expnd constructors end
          else [row];

    val (name, _) = Name.variant "a" used;

    fun mk _ [] = raise CASE_ERROR ("no rows", ~1)
      | mk [] (((_, []), (tm, tag)) :: _) = ([tag], tm) (* Done *)
      | mk path ((row as ((_, [Free _]), _)) :: _ :: _) = mk path [row]
      | mk (u :: us) (rows as ((_, _ :: _), _) :: _) =
          let val col0 = map (fn ((_, p :: _), (_, i)) => (p, i)) rows in
            (case Option.map (apfst head_of) (find_first (not o is_Free o fst) col0) of
              NONE =>
                let
                  val rows' = map (fn ((v, _), row) => row ||>
                    apfst (subst_free [(v, u)]) |>> v_to_prfx) (col0 ~~ rows);
                in mk us rows' end
            | SOME (Const (cname, cT), i) =>
                (case get_info (cname, cT) of
                  NONE => raise CASE_ERROR ("Not a datatype constructor: " ^ quote cname, i)
                | SOME (case_comb, constructors) =>
                    let
                      val pty = body_type cT;
                      val used' = fold Term.declare_term_frees us used;
                      val nrows = maps (expand constructors used' pty) rows;
                      val subproblems = partition used' constructors pty range_ty nrows;
                      val (pat_rect, dtrees) =
                        split_list (map (fn {new_formals, group, ...} =>
                          mk (new_formals @ us) group) subproblems);
                      val case_functions =
                        map2 (fn {new_formals, names, ...} =>
                          fold_rev (fn (x as Free (_, T), s) => fn t =>
                            Abs (if s = "" then name else s, T, abstract_over (x, t)))
                              (new_formals ~~ names))
                        subproblems dtrees;
                      val types = map fastype_of (case_functions @ [u]);
                      val case_const = Const (name_of case_comb |> the, types ---> range_ty);
                      val tree = list_comb (case_const, case_functions @ [u]);
                    in (flat pat_rect, tree) end)
            | SOME (t, i) =>
                raise CASE_ERROR ("Not a datatype constructor: " ^ Syntax.string_of_term ctxt t, i))
          end
      | mk _ _ = raise CASE_ERROR ("Malformed row matrix", ~1)
  in mk end;


(*Repeated variable occurrences in a pattern are not allowed.*)
fun no_repeat_vars ctxt pat = fold_aterms
  (fn x as Free (s, _) =>
      (fn xs =>
        if member op aconv xs x then
          case_error (quote s ^ " occurs repeatedly in the pattern " ^
            quote (Syntax.string_of_term ctxt pat))
        else x :: xs)
    | _ => I) pat [];

fun make_case ctxt config used x clauses =
  let
    fun string_of_clause (pat, rhs) =
      Syntax.unparse_term ctxt
        (Term.list_comb (Syntax.const \<^syntax_const>\<open>_case1\<close>,
          Syntax.uncheck_terms ctxt [pat, rhs]))
      |> Pretty.string_of;

    val _ = map (no_repeat_vars ctxt o fst) clauses;
    val rows = map_index (fn (i, (pat, rhs)) => (([], [pat]), (rhs, i))) clauses;
    val rangeT =
      (case distinct (op =) (map (fastype_of o snd) clauses) of
        [] => case_error "no clauses given"
      | [T] => T
      | _ => case_error "all cases must have the same result type");
    val used' = fold add_row_used rows used;
    val (tags, case_tm) =
      mk_case ctxt used' rangeT [x] rows
        handle CASE_ERROR (msg, i) =>
          case_error
            (msg ^ (if i < 0 then "" else "\nIn clause\n" ^ string_of_clause (nth clauses i)));
    val _ =
      (case subtract (op =) tags (map (snd o snd) rows) of
        [] => ()
      | is =>
          if config = Quiet then ()
          else
            (if config = Error then case_error else warning (*FIXME lack of syntactic context!?*))
              ("The following clauses are redundant (covered by preceding clauses):\n" ^
                cat_lines (map (string_of_clause o nth clauses) is)));
  in
    case_tm
  end;


(* term check *)

fun decode_clause (Const (\<^const_name>\<open>case_abs\<close>, _) $ Abs (s, T, t)) xs used =
      let val (s', used') = Name.variant s used
      in decode_clause t (Free (s', T) :: xs) used' end
  | decode_clause (Const (\<^const_name>\<open>case_elem\<close>, _) $ t $ u) xs _ =
      (subst_bounds (xs, t), subst_bounds (xs, u))
  | decode_clause _ _ _ = case_error "decode_clause";

fun decode_cases (Const (\<^const_name>\<open>case_nil\<close>, _)) = []
  | decode_cases (Const (\<^const_name>\<open>case_cons\<close>, _) $ t $ u) =
      decode_clause t [] (Term.declare_term_frees t Name.context) ::
      decode_cases u
  | decode_cases _ = case_error "decode_cases";

fun check_case ctxt =
  let
    fun decode_case (Const (\<^const_name>\<open>case_guard\<close>, _) $ b $ u $ t) =
          make_case ctxt (if b = \<^term>\<open>True\<close> then Error else Warning)
            Name.context (decode_case u) (decode_cases t)
      | decode_case (t $ u) = decode_case t $ decode_case u
      | decode_case (t as Abs _) =
          let val (v, t') = Term.dest_abs_global t;
          in Term.absfree v (decode_case t') end
      | decode_case t = t;
  in
    map decode_case
  end;

val _ = Context.>> (Syntax_Phases.term_check 1 "case" check_case);


(* Pretty printing of nested case expressions *)

(* destruct one level of pattern matching *)

fun dest_case ctxt d used t =
  (case apfst name_of (strip_comb t) of
    (SOME cname, ts as _ :: _) =>
      let
        val (fs, x) = split_last ts;
        fun strip_abs i t =
          let
            val zs = strip_abs_vars t;
            val j = length zs;
            val (xs, ys) =
              if j < i then (zs @
                map (pair "x") (drop j (take i (binder_types (fastype_of t)))), [])
              else chop i zs;
            val u = fold_rev Term.abs ys (strip_abs_body t);
            val xs' = map Free
              ((fold_map Name.variant (map fst xs)
                  (Term.declare_term_names u used) |> fst) ~~
               map snd xs);
            val (xs1, xs2) = chop j xs'
          in (xs', list_comb (subst_bounds (rev xs1, u), xs2)) end;
        fun is_dependent i t =
          let val k = length (strip_abs_vars t) - i
          in k < 0 orelse exists (fn j => j >= k) (loose_bnos (strip_abs_body t)) end;
        fun count_cases (_, _, true) = I
          | count_cases (c, (_, body), false) = AList.map_default op aconv (body, []) (cons c);
        val is_undefined = name_of #> equal (SOME \<^const_name>\<open>undefined\<close>);
        fun mk_case (c, (xs, body), _) = (list_comb (c, xs), body);
        val get_info = lookup_by_case ctxt;
      in
        (case get_info cname of
          SOME (_, constructors) =>
            if length fs = length constructors then
              let
                val R = fastype_of x;
                val cases = map (fn (Const (s, U), t) =>
                  let
                    val Us = binder_types U;
                    val k = length Us;
                    val p as (xs, _) = strip_abs k t;
                  in
                    (Const (s, map fastype_of xs ---> R), p, is_dependent k t)
                  end) (constructors ~~ fs);
                val cases' =
                  sort (int_ord o swap o apply2 (length o snd))
                    (fold_rev count_cases cases []);
                val dummy =
                  if d then Term.dummy_pattern R
                  else Free (Name.variant "x" used |> fst, R);
              in
                SOME (x,
                  map mk_case
                    (case find_first (is_undefined o fst) cases' of
                      SOME (_, cs) =>
                        if length cs = length constructors then [hd cases]
                        else filter_out (fn (_, (_, body), _) => is_undefined body) cases
                    | NONE =>
                        (case cases' of
                          [] => cases
                        | (default, cs) :: _ =>
                            if length cs = 1 then cases
                            else if length cs = length constructors then
                              [hd cases, (dummy, ([], default), false)]
                            else
                              filter_out (fn (c, _, _) => member op aconv cs c) cases @
                                [(dummy, ([], default), false)])))
              end
            else NONE
        | _ => NONE)
      end
  | _ => NONE);


(* destruct nested patterns *)

fun encode_clause recur S T (pat, rhs) =
  fold (fn x as (_, U) => fn t =>
    let val T = fastype_of t;
    in Const (\<^const_name>\<open>case_abs\<close>, (U --> T) --> T) $ Term.absfree x t end)
      (Term.add_frees pat [])
      (Const (\<^const_name>\<open>case_elem\<close>, S --> T --> S --> T) $ pat $ recur rhs);

fun encode_cases _ S T [] = Const (\<^const_name>\<open>case_nil\<close>, S --> T)
  | encode_cases recur S T (p :: ps) =
      Const (\<^const_name>\<open>case_cons\<close>, (S --> T) --> (S --> T) --> S --> T) $
        encode_clause recur S T p $ encode_cases recur S T ps;

fun encode_case recur (t, ps as (pat, rhs) :: _) =
      let
        val tT = fastype_of t;
        val T = fastype_of rhs;
      in
        Const (\<^const_name>\<open>case_guard\<close>, \<^typ>\<open>bool\<close> --> tT --> (tT --> T) --> T) $
          \<^term>\<open>True\<close> $ t $ (encode_cases recur (fastype_of pat) (fastype_of rhs) ps)
      end
  | encode_case _ _ = case_error "encode_case";

fun strip_case' ctxt d (pat, rhs) =
  (case dest_case ctxt d (Term.declare_term_frees pat Name.context) rhs of
    SOME (exp as Free _, clauses) =>
      if Term.exists_subterm (curry (op aconv) exp) pat andalso
        not (exists (fn (_, rhs') =>
          Term.exists_subterm (curry (op aconv) exp) rhs') clauses)
      then
        maps (strip_case' ctxt d) (map (fn (pat', rhs') =>
          (subst_free [(exp, pat')] pat, rhs')) clauses)
      else [(pat, rhs)]
  | _ => [(pat, rhs)]);

fun strip_case ctxt d t =
  (case dest_case ctxt d Name.context t of
    SOME (x, clauses) => SOME (x, maps (strip_case' ctxt d) clauses)
  | NONE => NONE);

fun strip_case_full ctxt d t =
  (case dest_case ctxt d Name.context t of
    SOME (x, clauses) =>
      encode_case (strip_case_full ctxt d)
        (strip_case_full ctxt d x, maps (strip_case' ctxt d) clauses)
  | NONE =>
      (case t of
        t $ u => strip_case_full ctxt d t $ strip_case_full ctxt d u
      | Abs _ =>
          let val (v, t') = Term.dest_abs_global t;
          in Term.absfree v (strip_case_full ctxt d t') end
      | _ => t));


(* term uncheck *)

val show_cases = Attrib.setup_config_bool \<^binding>\<open>show_cases\<close> (K true);

fun uncheck_case ctxt ts =
  if Config.get ctxt show_cases
  then map (fn t => if can Term.type_of t then strip_case_full ctxt true t else t) ts
  else ts;

val _ = Context.>> (Syntax_Phases.term_uncheck 1 "case" uncheck_case);


(* outer syntax commands *)

fun print_case_translations ctxt =
  let
    val cases = map snd (Symtab.dest (cases_of ctxt));
    val type_space = Proof_Context.type_space ctxt;

    val pretty_term = Syntax.pretty_term ctxt;

    fun pretty_data (data as (comb, ctrs)) =
      let
        val name = Tname_of_data data;
        val xname = Name_Space.extern ctxt type_space name;
        val markup = Name_Space.markup type_space name;
        val prt =
          (Pretty.block o Pretty.fbreaks)
           [Pretty.block [Pretty.mark_str (markup, xname), Pretty.str ":"],
            Pretty.block [Pretty.str "combinator:", Pretty.brk 1, pretty_term comb],
            Pretty.block (Pretty.str "constructors:" :: Pretty.brk 1 ::
              Pretty.commas (map pretty_term ctrs))];
      in (xname, prt) end;
  in
    Pretty.big_list "case translations:" (map #2 (sort_by #1 (map pretty_data cases)))
    |> Pretty.writeln
  end;

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_case_translations\<close>
    "print registered case combinators and constructors"
    (Scan.succeed (Toplevel.keep (print_case_translations o Toplevel.context_of)))

end;
