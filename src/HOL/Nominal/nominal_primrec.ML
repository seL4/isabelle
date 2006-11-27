(*  Title:      HOL/Nominal/nominal_primrec.ML
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen and Norbert Voelker, FernUni Hagen

Package for defining functions on nominal datatypes by primitive recursion.
Taken from HOL/Tools/primrec_package.ML
*)

signature NOMINAL_PRIMREC =
sig
  val quiet_mode: bool ref
  val add_primrec: string -> string list option -> string option ->
    ((bstring * string) * Attrib.src list) list -> theory -> Proof.state
  val add_primrec_unchecked: string -> string list option -> string option ->
    ((bstring * string) * Attrib.src list) list -> theory -> Proof.state
  val add_primrec_i: string -> term list option -> term option ->
    ((bstring * term) * attribute list) list -> theory -> Proof.state
  val add_primrec_unchecked_i: string -> term list option -> term option ->
    ((bstring * term) * attribute list) list -> theory -> Proof.state
end;

structure NominalPrimrec : NOMINAL_PRIMREC =
struct

open DatatypeAux;

exception RecError of string;

fun primrec_err s = error ("Nominal primrec definition error:\n" ^ s);
fun primrec_eq_err thy s eq =
  primrec_err (s ^ "\nin\n" ^ quote (Sign.string_of_term thy eq));


(* messages *)

val quiet_mode = ref false;
fun message s = if ! quiet_mode then () else writeln s;


(* preprocessing of equations *)

fun process_eqn thy eq rec_fns = 
  let
    val (lhs, rhs) = 
      if null (term_vars eq) then
        HOLogic.dest_eq (HOLogic.dest_Trueprop (Logic.strip_imp_concl eq))
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
        (map dest_Free (term_frees rhs) \\ lfrees);
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

val param_err = "Parameters must be the same for all recursive functions";

fun process_fun thy descr rec_eqns (i, fnameT as (fname, _)) (fnameTs, fnss) =
  let
    val (_, (tname, _, constrs)) = List.nth (descr, i);

    (* substitute "fname ls x rs" by "y" for (x, (_, y)) in subs *)

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
                val (_, rpos, eqns) = the (AList.lookup (op =) rec_eqns fnameT');
                val ls = Library.take (rpos, ts);
                val rest = Library.drop (rpos, ts);
                val (x', rs) = (hd rest, tl rest)
                  handle Empty => raise RecError ("not enough arguments\
                   \ in recursive application\nof function " ^ quote fname' ^ " on rhs");
                val _ = (case eqns of
                    (_, (ls', _, rs', _, _)) :: _ =>
                      if ls = map Free ls' andalso rs = map Free rs' then ()
                      else raise RecError param_err
                  | _ => ());
                val (x, xs) = strip_comb x'
              in case AList.lookup (op =) subs x
               of NONE =>
                    fs
                    |> fold_map (subst subs) ts
                    |-> (fn ts' => pair (list_comb (f, ts')))
                | SOME (i', y) =>
                    fs
                    |> fold_map (subst subs) xs
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
              (fnameTs', fnss', (Const ("arbitrary", dummyT))::fns))
        | SOME (ls, cargs', rs, rhs, eq) =>
            let
              val recs = filter (is_rec_type o snd) (cargs' ~~ cargs);
              val rargs = map fst recs;
              val subs = map (rpair dummyT o fst) 
                (rev (rename_wrt_term rhs rargs));
              val (rhs', (fnameTs'', fnss'')) = 
                  (subst (map (fn ((x, y), z) =>
                               (Free x, (body_index y, Free z)))
                          (recs ~~ subs)) rhs (fnameTs', fnss'))
                  handle RecError s => primrec_eq_err thy s eq
            in (fnameTs'', fnss'', 
                (list_abs_free (cargs' @ subs, rhs'))::fns)
            end)

  in (case AList.lookup (op =) fnameTs i of
      NONE =>
        if exists (equal fnameT o snd) fnameTs then
          raise RecError ("inconsistent functions for datatype " ^ quote tname)
        else
          let
            val SOME (_, _, eqns as (_, (ls, _, rs, _, _)) :: _) =
              AList.lookup (op =) rec_eqns fnameT;
            val (fnameTs', fnss', fns) = fold_rev (trans eqns) constrs
              ((i, fnameT)::fnameTs, fnss, []) 
          in
            (fnameTs', (i, (fname, ls, rs, fns))::fnss')
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
         val dummy_fns = map (fn (_, cargs) => Const ("arbitrary",
           replicate ((length cargs) + (length (List.filter is_rec_type cargs)))
             dummyT ---> HOLogic.unitT)) constrs;
         val _ = warning ("No function definition for datatype " ^ quote tname)
       in
         (dummy_fns @ fs, defs)
       end
   | SOME (fname, ls, rs, fs') => (fs' @ fs, (fname, ls, rs, rec_name, tname) :: defs);


(* make definition *)

fun make_def thy fs (fname, ls, rs, rec_name, tname) =
  let
    val used = map fst (fold Term.add_frees fs []);
    val x = (Name.variant used "x", dummyT);
    val frees = ls @ x :: rs;
    val rhs = list_abs_free (frees,
      list_comb (Const (rec_name, dummyT), fs @ [Free x]))
    val defpair = (Sign.base_name fname ^ "_" ^ Sign.base_name tname ^ "_def",
                   Logic.mk_equals (Const (fname, dummyT), rhs));
    val defpair' as (_, _ $ _ $ t) = Theory.inferT_axm thy defpair
  in (defpair', subst_bounds (rev (map Free frees), strip_abs_body t)) end;


(* find datatypes which contain all datatypes in tnames' *)

fun find_dts (dt_info : NominalPackage.nominal_datatype_info Symtab.table) _ [] = []
  | find_dts dt_info tnames' (tname::tnames) =
      (case Symtab.lookup dt_info tname of
          NONE => primrec_err (quote tname ^ " is not a nominal datatype")
        | SOME dt =>
            if tnames' subset (map (#1 o snd) (#descr dt)) then
              (tname, dt)::(find_dts dt_info tnames' tnames)
            else find_dts dt_info tnames' tnames);

fun common_prefix eq ([], _) = []
  | common_prefix eq (_, []) = []
  | common_prefix eq (x :: xs, y :: ys) =
      if eq (x, y) then x :: common_prefix eq (xs, ys) else [];

local

fun gen_primrec_i note def alt_name invs fctxt eqns_atts thy =
  let
    val (eqns, atts) = split_list eqns_atts;
    val dt_info = NominalPackage.get_nominal_datatypes thy;
    val rec_eqns = fold_rev (process_eqn thy o snd) eqns [];
    val lsrs :: lsrss = maps (fn (_, (_, _, eqns)) =>
      map (fn (_, (ls, _, rs, _, _)) => ls @ rs) eqns) rec_eqns
    val _ =
      (if forall (curry eq_set lsrs) lsrss andalso forall
         (fn (_, (_, _, (_, (ls, _, rs, _, _)) :: eqns)) =>
               forall (fn (_, (ls', _, rs', _, _)) =>
                 ls = ls' andalso rs = rs') eqns
           | _ => true) rec_eqns
       then () else raise RecError param_err);
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
      if alt_name = "" then (space_implode "_" (map (Sign.base_name o #1) defs)) else alt_name;
    val (defs_thms', thy') =
      thy
      |> Theory.add_path primrec_name
      |> fold_map def (map (fn ((name, t), _) => ((name, []), t)) defs');
    val cert = cterm_of thy';

    fun mk_idx eq =
      let
        val Const c = head_of (fst (HOLogic.dest_eq (HOLogic.dest_Trueprop
          (Logic.strip_imp_concl eq))));
        val SOME i = AList.lookup op = (map swap fnameTs) c;
        val SOME (_, _, constrs) = AList.lookup op = descr i;
        val SOME (_, _, eqns) = AList.lookup op = rec_eqns c;
        val SOME (cname, (_, cargs, _, _, _)) = find_first
          (fn (_, (_, _, _, _, eq')) => eq = eq') eqns
      in (i, find_index (fn (cname', _) => cname = cname') constrs, cargs) end;

    val rec_rewritess =
      unflat (map (fn (_, (_, _, constrs)) => constrs) descr) rec_rewrites;
    val fvars = rec_rewrites |> hd |> concl_of |> HOLogic.dest_Trueprop |>
      HOLogic.dest_eq |> fst |> strip_comb |> snd |> take_prefix is_Var |> fst;
    val (pvars, ctxtvars) = List.partition
      (equal HOLogic.boolT o body_type o snd)
      (fold Term.add_vars (map Logic.strip_assums_concl
        (prems_of (hd rec_rewrites))) [] \\ map dest_Var fvars);
    val cfs = defs' |> hd |> snd |> strip_comb |> snd |>
      curry (List.take o swap) (length fvars) |> map cert;
    val invs' = (case invs of
        NONE => map (fn (i, _) =>
          let
            val SOME (_, T) = AList.lookup op = fnameTs i
            val (Ts, U) = strip_type T
          in
            Abs ("x", List.drop (Ts, length lsrs + 1) ---> U, HOLogic.true_const)
          end) descr
      | SOME invs' => invs');
    val inst = (map cert fvars ~~ cfs) @
      (map (cert o Var) pvars ~~ map cert invs') @
      (case ctxtvars of
         [ctxtvar] => [(cert (Var ctxtvar), cert (the_default HOLogic.unit fctxt))]
       | _ => []);
    val rec_rewrites' = map (fn (_, eq) =>
      let
        val (i, j, cargs) = mk_idx eq
        val th = nth (nth rec_rewritess i) j;
        val cargs' = th |> concl_of |> HOLogic.dest_Trueprop |>
          HOLogic.dest_eq |> fst |> strip_comb |> snd |> split_last |> snd |>
          strip_comb |> snd
      in (cargs, Logic.strip_imp_prems eq,
        Drule.cterm_instantiate (inst @
          (map (cterm_of thy') cargs' ~~ map (cterm_of thy' o Free) cargs)) th)
      end) eqns;

    val prems = foldr1 (common_prefix op aconv) (map (prems_of o #3) rec_rewrites');
    val cprems = map cert prems;
    val asms = map Thm.assume cprems;
    val premss = map (fn (cargs, eprems, eqn) =>
      map (fn t => list_all_free (cargs, Logic.list_implies (eprems, t)))
        (List.drop (prems_of eqn, length prems))) rec_rewrites';
    val cpremss = map (map cert) premss;
    val asmss = map (map Thm.assume) cpremss;

    fun mk_eqn ((cargs, eprems, eqn), asms') =
      let
        val ceprems = map cert eprems;
        val asms'' = map Thm.assume ceprems;
        val ccargs = map (cert o Free) cargs;
        val asms''' = map (fn th => implies_elim_list
          (forall_elim_list ccargs th) asms'') asms'
      in
        implies_elim_list eqn (asms @ asms''') |>
        implies_intr_list ceprems |>
        forall_intr_list ccargs
      end;

    val rule_prems = cprems @ flat cpremss;
    val rule = implies_intr_list rule_prems
      (foldr1 (uncurry Conjunction.intr) (map mk_eqn (rec_rewrites' ~~ asmss)));

    val goals = map (fn ((cargs, _, _), (_, eqn)) =>
      (list_all_free (cargs, eqn), [])) (rec_rewrites' ~~ eqns);

  in
    thy' |>
    ProofContext.init |>
    Proof.theorem_i NONE
      (fn thss => ProofContext.theory (fn thy =>
         let
           val simps = flat thss;
           val (simps', thy') =
             fold_map note ((map fst eqns ~~ atts) ~~ map single simps) thy;
           val simps'' = maps snd simps'
         in
           thy'
           |> note (("simps", [Simplifier.simp_add]), simps'')
           |> snd
           |> Theory.parent_path
         end))
      [goals] |>
    Proof.apply (Method.Basic (fn ctxt => Method.RAW_METHOD (fn ths =>
      rewrite_goals_tac (map snd defs_thms') THEN
      compose_tac (false, rule, length rule_prems) 1))) |>
    Seq.hd
  end;

fun gen_primrec note def alt_name invs fctxt eqns thy =
  let
    fun readt T s = term_of (Thm.read_cterm thy (s, T));
    val ((names, strings), srcss) = apfst split_list (split_list eqns);
    val atts = map (map (Attrib.attribute thy)) srcss;
    val eqn_ts = map (fn s => readt propT s
      handle ERROR msg => cat_error msg ("The error(s) above occurred for " ^ s)) strings;
    val rec_ts = map (fn eq => head_of (fst (HOLogic.dest_eq
      (HOLogic.dest_Trueprop (Logic.strip_imp_concl eq))))
      handle TERM _ => primrec_eq_err thy "not a proper equation" eq) eqn_ts;
    val (_, eqn_ts') = OldInductivePackage.unify_consts thy rec_ts eqn_ts
  in
    gen_primrec_i note def alt_name
      (Option.map (map (readt TypeInfer.logicT)) invs)
      (Option.map (readt TypeInfer.logicT) fctxt)
      (names ~~ eqn_ts' ~~ atts) thy
  end;

fun thy_note ((name, atts), thms) =
  PureThy.add_thmss [((name, thms), atts)] #-> (fn [thms] => pair (name, thms));
fun thy_def false ((name, atts), t) =
      PureThy.add_defs_i false [((name, t), atts)] #-> (fn [thm] => pair (name, thm))
  | thy_def true ((name, atts), t) =
      PureThy.add_defs_unchecked_i false [((name, t), atts)] #-> (fn [thm] => pair (name, thm));

in

val add_primrec = gen_primrec thy_note (thy_def false);
val add_primrec_unchecked = gen_primrec thy_note (thy_def true);
val add_primrec_i = gen_primrec_i thy_note (thy_def false);
val add_primrec_unchecked_i = gen_primrec_i thy_note (thy_def true);

end; (*local*)


(* outer syntax *)

local structure P = OuterParse and K = OuterKeyword in

val parser1 = P.$$$ "freshness_context" |-- P.$$$ ":" |-- (P.term >> SOME);
val parser2 =
  P.$$$ "invariant" |-- P.$$$ ":" |--
    (Scan.repeat1 P.term >> SOME) -- Scan.optional parser1 NONE ||
  (parser1 >> pair NONE);
val parser3 =
  P.name -- Scan.optional parser2 (NONE, NONE) ||
  (parser2 >> pair "");
val parser4 =
  (P.$$$ "unchecked" >> K true) -- Scan.optional parser3 ("", (NONE, NONE)) ||
  (parser3 >> pair false);
val options =
  Scan.optional (P.$$$ "(" |-- P.!!!
    (parser4 --| P.$$$ ")")) (false, ("", (NONE, NONE)));

val primrec_decl =
  options -- Scan.repeat1 (P.opt_thm_name ":" -- P.prop);

val primrecP =
  OuterSyntax.command "nominal_primrec" "define primitive recursive functions on nominal datatypes" K.thy_goal
    (primrec_decl >> (fn ((unchecked, (alt_name, (invs, fctxt))), eqns) =>
      Toplevel.theory_to_proof
        ((if unchecked then add_primrec_unchecked else add_primrec) alt_name invs fctxt
          (map P.triple_swap eqns))));

val _ = OuterSyntax.add_parsers [primrecP];
val _ = OuterSyntax.add_keywords ["invariant", "freshness_context"];

end;


end;

