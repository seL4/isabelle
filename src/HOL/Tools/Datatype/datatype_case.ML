(*  Title:      HOL/Tools/Datatype/datatype_case.ML
    Author:     Konrad Slind, Cambridge University Computer Laboratory
    Author:     Stefan Berghofer, TU Muenchen

Datatype package: nested case expressions on datatypes.
*)

signature DATATYPE_CASE =
sig
  datatype config = Error | Warning | Quiet
  type info = Datatype_Aux.info
  val make_case: (string * typ -> info option) ->
    Proof.context -> config -> string list -> term -> (term * term) list ->
    term
  val dest_case: (string -> info option) -> bool ->
    string list -> term -> (term * (term * term) list) option
  val strip_case: (string -> info option) -> bool ->
    term -> (term * (term * term) list) option
  val case_tr: bool -> (theory -> string * typ -> info option) ->
    Proof.context -> term list -> term
  val case_tr': (theory -> string -> info option) ->
    string -> Proof.context -> term list -> term
end;

structure Datatype_Case : DATATYPE_CASE =
struct

datatype config = Error | Warning | Quiet;
type info = Datatype_Aux.info;

exception CASE_ERROR of string * int;

fun match_type thy pat ob = Sign.typ_match thy (pat, ob) Vartab.empty;

(* Get information about datatypes *)

fun ty_info tab sT =
  (case tab sT of
    SOME ({descr, case_name, index, ...} : info) =>
      let
        val (_, (tname, dts, constrs)) = nth descr index;
        val mk_ty = Datatype_Aux.typ_of_dtyp descr;
        val T = Type (tname, map mk_ty dts);
      in
        SOME {case_name = case_name,
          constructors = map (fn (cname, dts') =>
            Const (cname, Logic.varifyT_global (map mk_ty dts' ---> T))) constrs}
      end
  | NONE => NONE);


(*Each pattern carries with it a tag i, which denotes the clause it
came from. i = ~1 indicates that the clause was added by pattern
completion.*)

fun add_row_used ((prfx, pats), (tm, tag)) =
  fold Term.add_free_names (tm :: pats @ map Free prfx);

(*try to preserve names given by user*)
fun default_names names ts =
  map (fn ("", Free (name', _)) => name' | (name, _) => name) (names ~~ ts);

fun strip_constraints (Const (@{syntax_const "_constrain"}, _) $ t $ tT) =
      strip_constraints t ||> cons tT
  | strip_constraints t = (t, []);

fun mk_fun_constrain tT t =
  Syntax.const @{syntax_const "_constrain"} $ t $
    (Syntax.const @{type_syntax fun} $ tT $ Syntax.const @{type_syntax dummy});


(*Produce an instance of a constructor, plus fresh variables for its arguments.*)
fun fresh_constr ty_match ty_inst colty used c =
  let
    val (_, Ty) = dest_Const c;
    val Ts = binder_types Ty;
    val names =
      Name.variant_list used (Datatype_Prop.make_tnames (map Logic.unvarifyT_global Ts));
    val ty = body_type Ty;
    val ty_theta = ty_match ty colty
      handle Type.TYPE_MATCH => raise CASE_ERROR ("type mismatch", ~1);
    val c' = ty_inst ty_theta c;
    val gvars = map (ty_inst ty_theta o Free) (names ~~ Ts);
  in (c', gvars) end;


(*Go through a list of rows and pick out the ones beginning with a
  pattern with constructor = name.*)
fun mk_group (name, T) rows =
  let val k = length (binder_types T) in
    fold (fn (row as ((prfx, p :: ps), rhs as (_, i))) =>
      fn ((in_group, not_in_group), (names, cnstrts)) =>
        (case strip_comb p of
          (Const (name', _), args) =>
            if name = name' then
              if length args = k then
                let val (args', cnstrts') = split_list (map strip_constraints args) in
                  ((((prfx, args' @ ps), rhs) :: in_group, not_in_group),
                   (default_names names args', map2 append cnstrts cnstrts'))
                end
              else raise CASE_ERROR ("Wrong number of arguments for constructor " ^ name, i)
            else ((in_group, row :: not_in_group), (names, cnstrts))
        | _ => raise CASE_ERROR ("Not a constructor pattern", i)))
    rows (([], []), (replicate k "", replicate k [])) |>> pairself rev
  end;


(* Partitioning *)

fun partition _ _ _ _ _ _ _ [] = raise CASE_ERROR ("partition: no rows", ~1)
  | partition ty_match ty_inst type_of used constructors colty res_ty
        (rows as (((prfx, _ :: ps), _) :: _)) =
      let
        fun part [] [] = []
          | part [] ((_, (_, i)) :: _) = raise CASE_ERROR ("Not a constructor pattern", i)
          | part (c :: cs) rows =
              let
                val ((in_group, not_in_group), (names, cnstrts)) = mk_group (dest_Const c) rows;
                val used' = fold add_row_used in_group used;
                val (c', gvars) = fresh_constr ty_match ty_inst colty used' c;
                val in_group' =
                  if null in_group  (* Constructor not given *)
                  then
                    let
                      val Ts = map type_of ps;
                      val xs =
                        Name.variant_list
                          (fold Term.add_free_names gvars used')
                          (replicate (length ps) "x");
                    in
                      [((prfx, gvars @ map Free (xs ~~ Ts)),
                        (Const (@{const_syntax undefined}, res_ty), ~1))]
                    end
                  else in_group
              in
                {constructor = c',
                 new_formals = gvars,
                 names = names,
                 constraints = cnstrts,
                 group = in_group'} :: part cs not_in_group
              end
      in part constructors rows end;

fun v_to_prfx (prfx, Free v :: pats) = (v :: prfx, pats)
  | v_to_prfx _ = raise CASE_ERROR ("mk_case: v_to_prfx", ~1);


(* Translation of pattern terms into nested case expressions. *)

fun mk_case tab ctxt ty_match ty_inst type_of used range_ty =
  let
    val name = singleton (Name.variant_list used) "a";
    fun expand constructors used ty ((_, []), _) = raise CASE_ERROR ("mk_case: expand_var_row", ~1)
      | expand constructors used ty (row as ((prfx, p :: ps), (rhs, tag))) =
          if is_Free p then
            let
              val used' = add_row_used row used;
              fun expnd c =
                let val capp = list_comb (fresh_constr ty_match ty_inst ty used' c)
                in ((prfx, capp :: ps), (subst_free [(p, capp)] rhs, tag)) end
            in map expnd constructors end
          else [row]
    fun mk _ [] = raise CASE_ERROR ("no rows", ~1)
      | mk [] (((_, []), (tm, tag)) :: _) = ([tag], tm) (* Done *)
      | mk path (rows as ((row as ((_, [Free _]), _)) :: _ :: _)) = mk path [row]
      | mk (u :: us) (rows as ((_, _ :: _), _) :: _) =
          let val col0 = map (fn ((_, p :: _), (_, i)) => (p, i)) rows in
            (case Option.map (apfst head_of) (find_first (not o is_Free o fst) col0) of
              NONE =>
                let
                  val rows' = map (fn ((v, _), row) => row ||>
                    apfst (subst_free [(v, u)]) |>> v_to_prfx) (col0 ~~ rows);
                in mk us rows' end
            | SOME (Const (cname, cT), i) =>
                (case ty_info tab (cname, cT) of
                  NONE => raise CASE_ERROR ("Not a datatype constructor: " ^ cname, i)
                | SOME {case_name, constructors} =>
                    let
                      val pty = body_type cT;
                      val used' = fold Term.add_free_names us used;
                      val nrows = maps (expand constructors used' pty) rows;
                      val subproblems =
                        partition ty_match ty_inst type_of used'
                          constructors pty range_ty nrows;
                      val (pat_rect, dtrees) =
                        split_list (map (fn {new_formals, group, ...} =>
                          mk (new_formals @ us) group) subproblems);
                      val case_functions =
                        map2 (fn {new_formals, names, constraints, ...} =>
                          fold_rev (fn ((x as Free (_, T), s), cnstrts) => fn t =>
                            Abs (if s = "" then name else s, T, abstract_over (x, t))
                            |> fold mk_fun_constrain cnstrts) (new_formals ~~ names ~~ constraints))
                        subproblems dtrees;
                      val types = map type_of (case_functions @ [u]);
                      val case_const = Const (case_name, types ---> range_ty);
                      val tree = list_comb (case_const, case_functions @ [u]);
                    in (flat pat_rect, tree) end)
            | SOME (t, i) =>
                raise CASE_ERROR ("Not a datatype constructor: " ^ Syntax.string_of_term ctxt t, i))
          end
      | mk _ _ = raise CASE_ERROR ("Malformed row matrix", ~1)
  in mk end;

fun case_error s = error ("Error in case expression:\n" ^ s);

local

(*Repeated variable occurrences in a pattern are not allowed.*)
fun no_repeat_vars ctxt pat = fold_aterms
  (fn x as Free (s, _) =>
      (fn xs =>
        if member op aconv xs x then
          case_error (quote s ^ " occurs repeatedly in the pattern " ^
            quote (Syntax.string_of_term ctxt pat))
        else x :: xs)
    | _ => I) pat [];

fun gen_make_case ty_match ty_inst type_of tab ctxt config used x clauses =
  let
    fun string_of_clause (pat, rhs) =
      Syntax.string_of_term ctxt (Syntax.const @{syntax_const "_case1"} $ pat $ rhs);
    val _ = map (no_repeat_vars ctxt o fst) clauses;
    val rows = map_index (fn (i, (pat, rhs)) => (([], [pat]), (rhs, i))) clauses;
    val rangeT =
      (case distinct (op =) (map (type_of o snd) clauses) of
        [] => case_error "no clauses given"
      | [T] => T
      | _ => case_error "all cases must have the same result type");
    val used' = fold add_row_used rows used;
    val (tags, case_tm) =
      mk_case tab ctxt ty_match ty_inst type_of used' rangeT [x] rows
        handle CASE_ERROR (msg, i) =>
          case_error
            (msg ^ (if i < 0 then "" else "\nIn clause\n" ^ string_of_clause (nth clauses i)));
    val _ =
      (case subtract (op =) tags (map (snd o snd) rows) of
        [] => ()
      | is =>
          (case config of Error => case_error | Warning => warning | Quiet => fn _ => ())
            ("The following clauses are redundant (covered by preceding clauses):\n" ^
              cat_lines (map (string_of_clause o nth clauses) is)));
  in
    case_tm
  end;

in

fun make_case tab ctxt =
  gen_make_case (match_type (Proof_Context.theory_of ctxt))
    Envir.subst_term_types fastype_of tab ctxt;

val make_case_untyped =
  gen_make_case (K (K Vartab.empty)) (K (Term.map_types (K dummyT))) (K dummyT);

end;


(* parse translation *)

fun case_tr err tab_of ctxt [t, u] =
      let
        val thy = Proof_Context.theory_of ctxt;
        val intern_const_syntax = Consts.intern_syntax (Proof_Context.consts_of ctxt);

        (* replace occurrences of dummy_pattern by distinct variables *)
        (* internalize constant names                                 *)
        (* FIXME proper name context!? *)
        fun prep_pat ((c as Const (@{syntax_const "_constrain"}, _)) $ t $ tT) used =
              let val (t', used') = prep_pat t used
              in (c $ t' $ tT, used') end
          | prep_pat (Const (@{const_syntax dummy_pattern}, T)) used =
              let val x = singleton (Name.variant_list used) "x"
              in (Free (x, T), x :: used) end
          | prep_pat (Const (s, T)) used = (Const (intern_const_syntax s, T), used)
          | prep_pat (v as Free (s, T)) used =
              let val s' = Proof_Context.intern_const ctxt s in
                if Sign.declared_const thy s' then (Const (s', T), used)
                else (v, used)
              end
          | prep_pat (t $ u) used =
              let
                val (t', used') = prep_pat t used;
                val (u', used'') = prep_pat u used';
              in (t' $ u', used'') end
          | prep_pat t used = case_error ("Bad pattern: " ^ Syntax.string_of_term ctxt t);
        fun dest_case1 (t as Const (@{syntax_const "_case1"}, _) $ l $ r) =
              let val (l', cnstrts) = strip_constraints l
              in ((fst (prep_pat l' (Term.add_free_names t [])), r), cnstrts) end
          | dest_case1 t = case_error "dest_case1";
        fun dest_case2 (Const (@{syntax_const "_case2"}, _) $ t $ u) = t :: dest_case2 u
          | dest_case2 t = [t];
        val (cases, cnstrts) = split_list (map dest_case1 (dest_case2 u));
        val case_tm =
          make_case_untyped (tab_of thy) ctxt
            (if err then Error else Warning) []
            (fold (fn tT => fn t => Syntax.const @{syntax_const "_constrain"} $ t $ tT)
               (flat cnstrts) t) cases;
      in case_tm end
  | case_tr _ _ _ ts = case_error "case_tr";


(* Pretty printing of nested case expressions *)

(* destruct one level of pattern matching *)

local

(* FIXME proper name context!? *)
fun gen_dest_case name_of type_of tab d used t =
  (case apfst name_of (strip_comb t) of
    (SOME cname, ts as _ :: _) =>
      let
        val (fs, x) = split_last ts;
        fun strip_abs i t =
          let
            val zs = strip_abs_vars t;
            val _ = if length zs < i then raise CASE_ERROR ("", 0) else ();
            val (xs, ys) = chop i zs;
            val u = list_abs (ys, strip_abs_body t);
            val xs' =
              map Free
                (Name.variant_list (Misc_Legacy.add_term_names (u, used)) (map #1 xs) ~~ map #2 xs);
          in (xs', subst_bounds (rev xs', u)) end;
        fun is_dependent i t =
          let val k = length (strip_abs_vars t) - i
          in k < 0 orelse exists (fn j => j >= k) (loose_bnos (strip_abs_body t)) end;
        fun count_cases (_, _, true) = I
          | count_cases (c, (_, body), false) = AList.map_default op aconv (body, []) (cons c);
        val is_undefined = name_of #> equal (SOME @{const_name undefined});
        fun mk_case (c, (xs, body), _) = (list_comb (c, xs), body);
      in
        (case ty_info tab cname of
          SOME {constructors, case_name} =>
            if length fs = length constructors then
              let
                val cases = map (fn (Const (s, U), t) =>
                  let
                    val k = length (binder_types U);
                    val p as (xs, _) = strip_abs k t;
                  in
                    (Const (s, map type_of xs ---> type_of x), p, is_dependent k t)
                  end) (constructors ~~ fs);
                val cases' =
                  sort (int_ord o swap o pairself (length o snd))
                    (fold_rev count_cases cases []);
                val R = type_of t;
                val dummy =
                  if d then Term.dummy_pattern R
                  else Free (singleton (Name.variant_list used) "x", R);
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
              end handle CASE_ERROR _ => NONE
            else NONE
        | _ => NONE)
      end
  | _ => NONE);

in

val dest_case = gen_dest_case (try (dest_Const #> fst)) fastype_of;
val dest_case' = gen_dest_case (try (dest_Const #> fst #> Lexicon.unmark_const)) (K dummyT);

end;


(* destruct nested patterns *)

local

fun strip_case'' dest (pat, rhs) =
  (case dest (Term.add_free_names pat []) rhs of
    SOME (exp as Free _, clauses) =>
      if Term.exists_subterm (curry (op aconv) exp) pat andalso
        not (exists (fn (_, rhs') =>
          Term.exists_subterm (curry (op aconv) exp) rhs') clauses)
      then
        maps (strip_case'' dest) (map (fn (pat', rhs') =>
          (subst_free [(exp, pat')] pat, rhs')) clauses)
      else [(pat, rhs)]
  | _ => [(pat, rhs)]);

fun gen_strip_case dest t =
  (case dest [] t of
    SOME (x, clauses) => SOME (x, maps (strip_case'' dest) clauses)
  | NONE => NONE);

in

val strip_case = gen_strip_case oo dest_case;
val strip_case' = gen_strip_case oo dest_case';

end;


(* print translation *)

fun case_tr' tab_of cname ctxt ts =
  let
    val thy = Proof_Context.theory_of ctxt;
    fun mk_clause (pat, rhs) =
      let val xs = Term.add_frees pat [] in
        Syntax.const @{syntax_const "_case1"} $
          map_aterms
            (fn Free p => Syntax_Trans.mark_boundT p
              | Const (s, _) => Syntax.const (Lexicon.mark_const s)
              | t => t) pat $
          map_aterms
            (fn x as Free (s, T) => if member (op =) xs (s, T) then Syntax_Trans.mark_bound s else x
              | t => t) rhs
      end;
  in
    (case strip_case' (tab_of thy) true (list_comb (Syntax.const cname, ts)) of
      SOME (x, clauses) =>
        Syntax.const @{syntax_const "_case_syntax"} $ x $
          foldr1 (fn (t, u) => Syntax.const @{syntax_const "_case2"} $ t $ u)
            (map mk_clause clauses)
    | NONE => raise Match)
  end;

end;
