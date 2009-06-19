(*  Title:      HOL/Tools/old_primrec.ML
    Author:     Norbert Voelker, FernUni Hagen
    Author:     Stefan Berghofer, TU Muenchen

Package for defining functions on datatypes by primitive recursion.
*)

signature OLD_PRIMREC =
sig
  val unify_consts: theory -> term list -> term list -> term list * term list
  val add_primrec: string -> ((bstring * string) * Attrib.src list) list
    -> theory -> thm list * theory
  val add_primrec_unchecked: string -> ((bstring * string) * Attrib.src list) list
    -> theory -> thm list * theory
  val add_primrec_i: string -> ((bstring * term) * attribute list) list
    -> theory -> thm list * theory
  val add_primrec_unchecked_i: string -> ((bstring * term) * attribute list) list
    -> theory -> thm list * theory
end;

structure OldPrimrec : OLD_PRIMREC =
struct

open DatatypeAux;

exception RecError of string;

fun primrec_err s = error ("Primrec definition error:\n" ^ s);
fun primrec_eq_err thy s eq =
  primrec_err (s ^ "\nin\n" ^ quote (Syntax.string_of_term_global thy eq));


(*the following code ensures that each recursive set always has the
  same type in all introduction rules*)
fun unify_consts thy cs intr_ts =
  (let
    fun varify (t, (i, ts)) =
      let val t' = map_types (Logic.incr_tvar (i + 1)) (snd (Type.varify [] t))
      in (maxidx_of_term t', t'::ts) end;
    val (i, cs') = List.foldr varify (~1, []) cs;
    val (i', intr_ts') = List.foldr varify (i, []) intr_ts;
    val rec_consts = fold Term.add_consts cs' [];
    val intr_consts = fold Term.add_consts intr_ts' [];
    fun unify (cname, cT) =
      let val consts = map snd (filter (fn (c, _) => c = cname) intr_consts)
      in fold (Sign.typ_unify thy) ((replicate (length consts) cT) ~~ consts) end;
    val (env, _) = fold unify rec_consts (Vartab.empty, i');
    val subst = Type.freeze o map_types (Envir.norm_type env)

  in (map subst cs', map subst intr_ts')
  end) handle Type.TUNIFY =>
    (warning "Occurrences of recursive constant have non-unifiable types"; (cs, intr_ts));


(* preprocessing of equations *)

fun process_eqn thy eq rec_fns =
  let
    val (lhs, rhs) =
      if null (Term.add_vars eq []) then
        HOLogic.dest_eq (HOLogic.dest_Trueprop eq)
        handle TERM _ => raise RecError "not a proper equation"
      else raise RecError "illegal schematic variable(s)";

    val (recfun, args) = strip_comb lhs;
    val fnameT = dest_Const recfun handle TERM _ =>
      raise RecError "function is not declared as constant in theory";

    val (ls', rest)  = take_prefix is_Free args;
    val (middle, rs') = take_suffix is_Free rest;
    val rpos = length ls';

    val (constr, cargs') = if null middle then raise RecError "constructor missing"
      else strip_comb (hd middle);
    val (cname, T) = dest_Const constr
      handle TERM _ => raise RecError "ill-formed constructor";
    val (tname, _) = dest_Type (body_type T) handle TYPE _ =>
      raise RecError "cannot determine datatype associated with function"

    val (ls, cargs, rs) =
      (map dest_Free ls', map dest_Free cargs', map dest_Free rs')
      handle TERM _ => raise RecError "illegal argument in pattern";
    val lfrees = ls @ rs @ cargs;

    fun check_vars _ [] = ()
      | check_vars s vars = raise RecError (s ^ commas_quote (map fst vars))
  in
    if length middle > 1 then
      raise RecError "more than one non-variable in pattern"
    else
     (check_vars "repeated variable names in pattern: " (duplicates (op =) lfrees);
      check_vars "extra variables on rhs: "
        (map dest_Free (OldTerm.term_frees rhs) \\ lfrees);
      case AList.lookup (op =) rec_fns fnameT of
        NONE =>
          (fnameT, (tname, rpos, [(cname, (ls, cargs, rs, rhs, eq))]))::rec_fns
      | SOME (_, rpos', eqns) =>
          if AList.defined (op =) eqns cname then
            raise RecError "constructor already occurred as pattern"
          else if rpos <> rpos' then
            raise RecError "position of recursive argument inconsistent"
          else
            AList.update (op =) (fnameT, (tname, rpos, (cname, (ls, cargs, rs, rhs, eq))::eqns))
              rec_fns)
  end
  handle RecError s => primrec_eq_err thy s eq;

fun process_fun thy descr rec_eqns (i, fnameT as (fname, _)) (fnameTs, fnss) =
  let
    val (_, (tname, _, constrs)) = List.nth (descr, i);

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
            if is_Const f andalso dest_Const f mem map fst rec_eqns then
              let
                val fnameT' as (fname', _) = dest_Const f;
                val (_, rpos, _) = the (AList.lookup (op =) rec_eqns fnameT');
                val ls = Library.take (rpos, ts);
                val rest = Library.drop (rpos, ts);
                val (x', rs) = (hd rest, tl rest)
                  handle Empty => raise RecError ("not enough arguments\
                   \ in recursive application\nof function " ^ quote fname' ^ " on rhs");
                val (x, xs) = strip_comb x'
              in case AList.lookup (op =) subs x
               of NONE =>
                    fs
                    |> fold_map (subst subs) ts
                    |-> (fn ts' => pair (list_comb (f, ts')))
                | SOME (i', y) =>
                    fs
                    |> fold_map (subst subs) (xs @ ls @ rs)
                    ||> process_fun thy descr rec_eqns (i', fnameT')
                    |-> (fn ts' => pair (list_comb (y, ts')))
              end
            else
              fs
              |> fold_map (subst subs) (f :: ts)
              |-> (fn (f'::ts') => pair (list_comb (f', ts')))
          end
      | subst _ t fs = (t, fs);

    (* translate rec equations into function arguments suitable for rec comb *)

    fun trans eqns (cname, cargs) (fnameTs', fnss', fns) =
      (case AList.lookup (op =) eqns cname of
          NONE => (warning ("No equation for constructor " ^ quote cname ^
            "\nin definition of function " ^ quote fname);
              (fnameTs', fnss', (Const ("HOL.undefined", dummyT))::fns))
        | SOME (ls, cargs', rs, rhs, eq) =>
            let
              val recs = filter (is_rec_type o snd) (cargs' ~~ cargs);
              val rargs = map fst recs;
              val subs = map (rpair dummyT o fst)
                (rev (Term.rename_wrt_term rhs rargs));
              val (rhs', (fnameTs'', fnss'')) =
                  (subst (map (fn ((x, y), z) =>
                               (Free x, (body_index y, Free z)))
                          (recs ~~ subs)) rhs (fnameTs', fnss'))
                  handle RecError s => primrec_eq_err thy s eq
            in (fnameTs'', fnss'',
                (list_abs_free (cargs' @ subs @ ls @ rs, rhs'))::fns)
            end)

  in (case AList.lookup (op =) fnameTs i of
      NONE =>
        if exists (equal fnameT o snd) fnameTs then
          raise RecError ("inconsistent functions for datatype " ^ quote tname)
        else
          let
            val (_, _, eqns) = the (AList.lookup (op =) rec_eqns fnameT);
            val (fnameTs', fnss', fns) = fold_rev (trans eqns) constrs
              ((i, fnameT)::fnameTs, fnss, [])
          in
            (fnameTs', (i, (fname, #1 (snd (hd eqns)), fns))::fnss')
          end
    | SOME fnameT' =>
        if fnameT = fnameT' then (fnameTs, fnss)
        else raise RecError ("inconsistent functions for datatype " ^ quote tname))
  end;


(* prepare functions needed for definitions *)

fun get_fns fns ((i : int, (tname, _, constrs)), rec_name) (fs, defs) =
  case AList.lookup (op =) fns i of
     NONE =>
       let
         val dummy_fns = map (fn (_, cargs) => Const ("HOL.undefined",
           replicate ((length cargs) + (length (List.filter is_rec_type cargs)))
             dummyT ---> HOLogic.unitT)) constrs;
         val _ = warning ("No function definition for datatype " ^ quote tname)
       in
         (dummy_fns @ fs, defs)
       end
   | SOME (fname, ls, fs') => (fs' @ fs, (fname, ls, rec_name, tname) :: defs);


(* make definition *)

fun make_def thy fs (fname, ls, rec_name, tname) =
  let
    val rhs = fold_rev (fn T => fn t => Abs ("", T, t))
                    ((map snd ls) @ [dummyT])
                    (list_comb (Const (rec_name, dummyT),
                                fs @ map Bound (0 ::(length ls downto 1))))
    val def_name = Long_Name.base_name fname ^ "_" ^ Long_Name.base_name tname ^ "_def";
    val def_prop =
      singleton (Syntax.check_terms (ProofContext.init thy))
        (Logic.mk_equals (Const (fname, dummyT), rhs));
  in (def_name, def_prop) end;


(* find datatypes which contain all datatypes in tnames' *)

fun find_dts (dt_info : datatype_info Symtab.table) _ [] = []
  | find_dts dt_info tnames' (tname::tnames) =
      (case Symtab.lookup dt_info tname of
          NONE => primrec_err (quote tname ^ " is not a datatype")
        | SOME dt =>
            if tnames' subset (map (#1 o snd) (#descr dt)) then
              (tname, dt)::(find_dts dt_info tnames' tnames)
            else find_dts dt_info tnames' tnames);

fun prepare_induct ({descr, induction, ...}: datatype_info) rec_eqns =
  let
    fun constrs_of (_, (_, _, cs)) =
      map (fn (cname:string, (_, cargs, _, _, _)) => (cname, map fst cargs)) cs;
    val params_of = these o AList.lookup (op =) (List.concat (map constrs_of rec_eqns));
  in
    induction
    |> RuleCases.rename_params (map params_of (List.concat (map (map #1 o #3 o #2) descr)))
    |> RuleCases.save induction
  end;

local

fun gen_primrec_i note def alt_name eqns_atts thy =
  let
    val (eqns, atts) = split_list eqns_atts;
    val dt_info = Datatype.get_datatypes thy;
    val rec_eqns = fold_rev (process_eqn thy o snd) eqns [] ;
    val tnames = distinct (op =) (map (#1 o snd) rec_eqns);
    val dts = find_dts dt_info tnames tnames;
    val main_fns =
      map (fn (tname, {index, ...}) =>
        (index,
          (fst o the o find_first (fn f => (#1 o snd) f = tname)) rec_eqns))
      dts;
    val {descr, rec_names, rec_rewrites, ...} =
      if null dts then
        primrec_err ("datatypes " ^ commas_quote tnames ^ "\nare not mutually recursive")
      else snd (hd dts);
    val (fnameTs, fnss) =
      fold_rev (process_fun thy descr rec_eqns) main_fns ([], []);
    val (fs, defs) = fold_rev (get_fns fnss) (descr ~~ rec_names) ([], []);
    val defs' = map (make_def thy fs) defs;
    val nameTs1 = map snd fnameTs;
    val nameTs2 = map fst rec_eqns;
    val _ = if gen_eq_set (op =) (nameTs1, nameTs2) then ()
            else primrec_err ("functions " ^ commas_quote (map fst nameTs2) ^
              "\nare not mutually recursive");
    val primrec_name =
      if alt_name = "" then (space_implode "_" (map (Long_Name.base_name o #1) defs)) else alt_name;
    val (defs_thms', thy') =
      thy
      |> Sign.add_path primrec_name
      |> fold_map def (map (fn (name, t) => ((name, []), t)) defs');
    val rewrites = (map mk_meta_eq rec_rewrites) @ map snd defs_thms';
    val simps = map (fn (_, t) => Goal.prove_global thy' [] [] t
        (fn _ => EVERY [rewrite_goals_tac rewrites, rtac refl 1])) eqns;
    val (simps', thy'') =
      thy'
      |> fold_map note ((map fst eqns ~~ atts) ~~ map single simps);
    val simps'' = maps snd simps';
  in
    thy''
    |> note (("simps", [Simplifier.simp_add, Nitpick_Const_Simp_Thms.add,
                        Code.add_default_eqn_attribute]), simps'')
    |> snd
    |> note (("induct", []), [prepare_induct (#2 (hd dts)) rec_eqns])
    |> snd
    |> Sign.parent_path
    |> pair simps''
  end;

fun gen_primrec note def alt_name eqns thy =
  let
    val ((names, strings), srcss) = apfst split_list (split_list eqns);
    val atts = map (map (Attrib.attribute thy)) srcss;
    val eqn_ts = map (fn s => Syntax.read_prop_global thy s
      handle ERROR msg => cat_error msg ("The error(s) above occurred for " ^ s)) strings;
    val rec_ts = map (fn eq => head_of (fst (HOLogic.dest_eq (HOLogic.dest_Trueprop eq)))
      handle TERM _ => primrec_eq_err thy "not a proper equation" eq) eqn_ts;
    val (_, eqn_ts') = unify_consts thy rec_ts eqn_ts
  in
    gen_primrec_i note def alt_name (names ~~ eqn_ts' ~~ atts) thy
  end;

fun thy_note ((name, atts), thms) =
  PureThy.add_thmss [((Binding.name name, thms), atts)] #-> (fn [thms] => pair (name, thms));
fun thy_def false ((name, atts), t) =
      PureThy.add_defs false [((Binding.name name, t), atts)] #-> (fn [thm] => pair (name, thm))
  | thy_def true ((name, atts), t) =
      PureThy.add_defs_unchecked false [((Binding.name name, t), atts)] #-> (fn [thm] => pair (name, thm));

in

val add_primrec = gen_primrec thy_note (thy_def false);
val add_primrec_unchecked = gen_primrec thy_note (thy_def true);
val add_primrec_i = gen_primrec_i thy_note (thy_def false);
val add_primrec_unchecked_i = gen_primrec_i thy_note (thy_def true);
fun gen_primrec note def alt_name specs =
  gen_primrec_i note def alt_name (map (fn ((name, t), atts) => ((name, atts), t)) specs);

end;


(* see primrec.ML (* outer syntax *)

local structure P = OuterParse and K = OuterKeyword in

val opt_unchecked_name =
  Scan.optional (P.$$$ "(" |-- P.!!!
    (((P.$$$ "unchecked" >> K true) -- Scan.optional P.name "" ||
      P.name >> pair false) --| P.$$$ ")")) (false, "");

val primrec_decl =
  opt_unchecked_name -- Scan.repeat1 (SpecParse.opt_thm_name ":" -- P.prop);

val _ =
  OuterSyntax.command "primrec" "define primitive recursive functions on datatypes" K.thy_decl
    (primrec_decl >> (fn ((unchecked, alt_name), eqns) =>
      Toplevel.theory (snd o
        (if unchecked then add_primrec_unchecked else add_primrec) alt_name
          (map P.triple_swap eqns))));

end;*)

end;
