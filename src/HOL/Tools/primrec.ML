(*  Title:      HOL/Tools/primrec.ML
    Author:     Norbert Voelker, FernUni Hagen
    Author:     Stefan Berghofer, TU Muenchen
    Author:     Florian Haftmann, TU Muenchen

Primitive recursive functions on datatypes.
*)

signature PRIMREC =
sig
  val add_primrec: (binding * typ option * mixfix) list ->
    (Attrib.binding * term) list -> local_theory -> (term list * thm list) * local_theory
  val add_primrec_cmd: (binding * string option * mixfix) list ->
    (Attrib.binding * string) list -> local_theory -> (term list * thm list) * local_theory
  val add_primrec_global: (binding * typ option * mixfix) list ->
    (Attrib.binding * term) list -> theory -> (term list * thm list) * theory
  val add_primrec_overloaded: (string * (string * typ) * bool) list ->
    (binding * typ option * mixfix) list ->
    (Attrib.binding * term) list -> theory -> (term list * thm list) * theory
  val add_primrec_simple: ((binding * typ) * mixfix) list -> term list ->
    local_theory -> (string * (term list * thm list)) * local_theory
end;

structure Primrec : PRIMREC =
struct

open Datatype_Aux;

exception PrimrecError of string * term option;

fun primrec_error msg = raise PrimrecError (msg, NONE);
fun primrec_error_eqn msg eqn = raise PrimrecError (msg, SOME eqn);


(* preprocessing of equations *)

fun process_eqn is_fixed spec rec_fns =
  let
    val (vs, Ts) = split_list (strip_qnt_vars "all" spec);
    val body = strip_qnt_body "all" spec;
    val (vs', _) = fold_map Name.variant vs (Name.make_context (fold_aterms
      (fn Free (v, _) => insert (op =) v | _ => I) body []));
    val eqn = curry subst_bounds (map2 (curry Free) vs' Ts |> rev) body;
    val (lhs, rhs) = HOLogic.dest_eq (HOLogic.dest_Trueprop eqn)
      handle TERM _ => primrec_error "not a proper equation";
    val (recfun, args) = strip_comb lhs;
    val fname =
      (case recfun of
        Free (v, _) =>
          if is_fixed v then v
          else primrec_error "illegal head of function equation"
      | _ => primrec_error "illegal head of function equation");

    val (ls', rest)  = take_prefix is_Free args;
    val (middle, rs') = take_suffix is_Free rest;
    val rpos = length ls';

    val (constr, cargs') =
      if null middle then primrec_error "constructor missing"
      else strip_comb (hd middle);
    val (cname, T) = dest_Const constr
      handle TERM _ => primrec_error "ill-formed constructor";
    val (tname, _) = dest_Type (body_type T) handle TYPE _ =>
      primrec_error "cannot determine datatype associated with function"

    val (ls, cargs, rs) =
      (map dest_Free ls', map dest_Free cargs', map dest_Free rs')
      handle TERM _ => primrec_error "illegal argument in pattern";
    val lfrees = ls @ rs @ cargs;

    fun check_vars _ [] = ()
      | check_vars s vars = primrec_error (s ^ commas_quote (map fst vars)) eqn;
  in
    if length middle > 1 then
      primrec_error "more than one non-variable in pattern"
    else
     (check_vars "repeated variable names in pattern: " (duplicates (op =) lfrees);
      check_vars "extra variables on rhs: "
        (Term.add_frees rhs [] |> subtract (op =) lfrees
          |> filter_out (is_fixed o fst));
      (case AList.lookup (op =) rec_fns fname of
        NONE =>
          (fname, (tname, rpos, [(cname, (ls, cargs, rs, rhs, eqn))])) :: rec_fns
      | SOME (_, rpos', eqns) =>
          if AList.defined (op =) eqns cname then
            primrec_error "constructor already occurred as pattern"
          else if rpos <> rpos' then
            primrec_error "position of recursive argument inconsistent"
          else
            AList.update (op =)
              (fname, (tname, rpos, (cname, (ls, cargs, rs, rhs, eqn)) :: eqns))
              rec_fns))
  end handle PrimrecError (msg, NONE) => primrec_error_eqn msg spec;

fun process_fun descr eqns (i, fname) (fnames, fnss) =
  let
    val (_, (tname, _, constrs)) = nth descr i;

    (* substitute "fname ls x rs" by "y ls rs" for (x, (_, y)) in subs *)

    fun subst [] t fs = (t, fs)
      | subst subs (Abs (a, T, t)) fs =
          fs
          |> subst subs t
          |-> (fn t' => pair (Abs (a, T, t')))
      | subst subs (t as (_ $ _)) fs =
          let
            val (f, ts) = strip_comb t;
          in
            if is_Free f
              andalso member (fn ((v, _), (w, _)) => v = w) eqns (dest_Free f) then
              let
                val (fname', _) = dest_Free f;
                val (_, rpos, _) = the (AList.lookup (op =) eqns fname');
                val (ls, rs) = chop rpos ts
                val (x', rs') =
                  (case rs of
                    x' :: rs => (x', rs)
                  | [] => primrec_error ("not enough arguments in recursive application\n" ^
                      "of function " ^ quote fname' ^ " on rhs"));
                val (x, xs) = strip_comb x';
              in
                (case AList.lookup (op =) subs x of
                  NONE =>
                    fs
                    |> fold_map (subst subs) ts
                    |-> (fn ts' => pair (list_comb (f, ts')))
                | SOME (i', y) =>
                    fs
                    |> fold_map (subst subs) (xs @ ls @ rs')
                    ||> process_fun descr eqns (i', fname')
                    |-> (fn ts' => pair (list_comb (y, ts'))))
              end
            else
              fs
              |> fold_map (subst subs) (f :: ts)
              |-> (fn f' :: ts' => pair (list_comb (f', ts')))
          end
      | subst _ t fs = (t, fs);

    (* translate rec equations into function arguments suitable for rec comb *)

    fun trans eqns (cname, cargs) (fnames', fnss', fns) =
      (case AList.lookup (op =) eqns cname of
        NONE => (warning ("No equation for constructor " ^ quote cname ^
          "\nin definition of function " ^ quote fname);
            (fnames', fnss', (Const (@{const_name undefined}, dummyT)) :: fns))
      | SOME (ls, cargs', rs, rhs, eq) =>
          let
            val recs = filter (is_rec_type o snd) (cargs' ~~ cargs);
            val rargs = map fst recs;
            val subs = map (rpair dummyT o fst)
              (rev (Term.rename_wrt_term rhs rargs));
            val (rhs', (fnames'', fnss'')) = subst (map2 (fn (x, y) => fn z =>
              (Free x, (body_index y, Free z))) recs subs) rhs (fnames', fnss')
                handle PrimrecError (s, NONE) => primrec_error_eqn s eq
          in
            (fnames'', fnss'', fold_rev absfree (cargs' @ subs @ ls @ rs) rhs' :: fns)
          end)

  in
    (case AList.lookup (op =) fnames i of
      NONE =>
        if exists (fn (_, v) => fname = v) fnames then
          primrec_error ("inconsistent functions for datatype " ^ quote tname)
        else
          let
            val (_, _, eqns) = the (AList.lookup (op =) eqns fname);
            val (fnames', fnss', fns) = fold_rev (trans eqns) constrs
              ((i, fname) :: fnames, fnss, [])
          in
            (fnames', (i, (fname, #1 (snd (hd eqns)), fns)) :: fnss')
          end
    | SOME fname' =>
        if fname = fname' then (fnames, fnss)
        else primrec_error ("inconsistent functions for datatype " ^ quote tname))
  end;


(* prepare functions needed for definitions *)

fun get_fns fns ((i : int, (tname, _, constrs)), rec_name) (fs, defs) =
  (case AList.lookup (op =) fns i of
    NONE =>
      let
        val dummy_fns = map (fn (_, cargs) => Const (@{const_name undefined},
          replicate (length cargs + length (filter is_rec_type cargs))
            dummyT ---> HOLogic.unitT)) constrs;
        val _ = warning ("No function definition for datatype " ^ quote tname)
      in
        (dummy_fns @ fs, defs)
      end
  | SOME (fname, ls, fs') => (fs' @ fs, (fname, ls, rec_name, tname) :: defs));


(* make definition *)

fun make_def ctxt fixes fs (fname, ls, rec_name, tname) =
  let
    val SOME (var, varT) = get_first (fn ((b, T), mx) =>
      if Binding.name_of b = fname then SOME ((b, mx), T) else NONE) fixes;
    val def_name = Thm.def_name (Long_Name.base_name fname);
    val raw_rhs = fold_rev (fn T => fn t => Abs ("", T, t)) (map snd ls @ [dummyT])
      (list_comb (Const (rec_name, dummyT), fs @ map Bound (0 :: (length ls downto 1))))
    val rhs = singleton (Syntax.check_terms ctxt) (Type.constraint varT raw_rhs);
  in (var, ((Binding.conceal (Binding.name def_name), []), rhs)) end;


(* find datatypes which contain all datatypes in tnames' *)

fun find_dts (dt_info : info Symtab.table) _ [] = []
  | find_dts dt_info tnames' (tname :: tnames) =
      (case Symtab.lookup dt_info tname of
        NONE => primrec_error (quote tname ^ " is not a datatype")
      | SOME dt =>
          if subset (op =) (tnames', map (#1 o snd) (#descr dt)) then
            (tname, dt) :: (find_dts dt_info tnames' tnames)
          else find_dts dt_info tnames' tnames);


(* distill primitive definition(s) from primrec specification *)

fun distill lthy fixes eqs = 
  let
    val eqns = fold_rev (process_eqn (fn v => Variable.is_fixed lthy v
      orelse exists (fn ((w, _), _) => v = Binding.name_of w) fixes)) eqs [];
    val tnames = distinct (op =) (map (#1 o snd) eqns);
    val dts = find_dts (Datatype_Data.get_all (Proof_Context.theory_of lthy)) tnames tnames;
    val main_fns = map (fn (tname, {index, ...}) =>
      (index, (fst o the o find_first (fn (_, x) => #1 x = tname)) eqns)) dts;
    val {descr, rec_names, rec_rewrites, ...} =
      if null dts then primrec_error
        ("datatypes " ^ commas_quote tnames ^ "\nare not mutually recursive")
      else snd (hd dts);
    val (fnames, fnss) = fold_rev (process_fun descr eqns) main_fns ([], []);
    val (fs, raw_defs) = fold_rev (get_fns fnss) (descr ~~ rec_names) ([], []);
    val defs = map (make_def lthy fixes fs) raw_defs;
    val names = map snd fnames;
    val names_eqns = map fst eqns;
    val _ =
      if eq_set (op =) (names, names_eqns) then ()
      else primrec_error ("functions " ^ commas_quote names_eqns ^
        "\nare not mutually recursive");
    val rec_rewrites' = map mk_meta_eq rec_rewrites;
    val prefix = space_implode "_" (map (Long_Name.base_name o #1) raw_defs);
    fun prove lthy defs =
      let
        val frees = fold (Variable.add_free_names lthy) eqs [];
        val rewrites = rec_rewrites' @ map (snd o snd) defs;
        fun tac _ = EVERY [rewrite_goals_tac rewrites, rtac refl 1];
      in map (fn eq => Goal.prove lthy frees [] eq tac) eqs end;
  in ((prefix, (fs, defs)), prove) end
  handle PrimrecError (msg, some_eqn) =>
    error ("Primrec definition error:\n" ^ msg ^
      (case some_eqn of
        SOME eqn => "\nin\n" ^ quote (Syntax.string_of_term lthy eqn)
      | NONE => ""));


(* primrec definition *)

fun add_primrec_simple fixes ts lthy =
  let
    val ((prefix, (fs, defs)), prove) = distill lthy fixes ts;
  in
    lthy
    |> fold_map Local_Theory.define defs
    |-> (fn defs => `(fn lthy => (prefix, (map fst defs, prove lthy defs))))
  end;

local

fun gen_primrec prep_spec raw_fixes raw_spec lthy =
  let
    val (fixes, spec) = fst (prep_spec raw_fixes raw_spec lthy);
    fun attr_bindings prefix = map (fn ((b, attrs), _) =>
      (Binding.qualify false prefix b, Code.add_default_eqn_attrib :: attrs)) spec;
    fun simp_attr_binding prefix =
      (Binding.qualify true prefix (Binding.name "simps"), @{attributes [simp, nitpick_simp]});
  in
    lthy
    |> add_primrec_simple fixes (map snd spec)
    |-> (fn (prefix, (ts, simps)) =>
      Spec_Rules.add Spec_Rules.Equational (ts, simps)
      #> fold_map Local_Theory.note (attr_bindings prefix ~~ map single simps)
      #-> (fn simps' => Local_Theory.note (simp_attr_binding prefix, maps snd simps')
      #>> (fn (_, simps'') => (ts, simps''))))
  end;

in

val add_primrec = gen_primrec Specification.check_spec;
val add_primrec_cmd = gen_primrec Specification.read_spec;

end;

fun add_primrec_global fixes specs thy =
  let
    val lthy = Named_Target.theory_init thy;
    val ((ts, simps), lthy') = add_primrec fixes specs lthy;
    val simps' = Proof_Context.export lthy' lthy simps;
  in ((ts, simps'), Local_Theory.exit_global lthy') end;

fun add_primrec_overloaded ops fixes specs thy =
  let
    val lthy = Overloading.overloading ops thy;
    val ((ts, simps), lthy') = add_primrec fixes specs lthy;
    val simps' = Proof_Context.export lthy' lthy simps;
  in ((ts, simps'), Local_Theory.exit_global lthy') end;


(* outer syntax *)

val _ =
  Outer_Syntax.local_theory "primrec" "define primitive recursive functions on datatypes"
    Keyword.thy_decl
    (Parse.fixes -- Parse_Spec.where_alt_specs
      >> (fn (fixes, specs) => add_primrec_cmd fixes specs #> snd));

end;
