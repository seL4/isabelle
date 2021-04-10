(*  Title:      HOL/Eisbach/eisbach_rule_insts.ML
    Author:     Daniel Matichuk, NICTA/UNSW

Eisbach-aware variants of the "where" and "of" attributes.

Alternate syntax for rule_insts.ML participates in token closures by
examining the behaviour of Rule_Insts.where_rule and instantiating token
values accordingly. Instantiations in re-interpretation are done with
infer_instantiate.
*)

structure Eisbach_Rule_Insts: sig end =
struct

fun restore_tags thm = Thm.map_tags (K (Thm.get_tags thm));

val mk_term_type_internal = Logic.protect o Logic.mk_term o Logic.mk_type;

fun term_type_cases f g t = 
  (case \<^try>\<open>Logic.dest_type (Logic.dest_term (Logic.unprotect t))\<close> of
    SOME T => f T
  | NONE =>
      (case \<^try>\<open>Logic.dest_term t\<close> of
        SOME t => g t
      | NONE => raise Fail "Lost encoded instantiation"))

fun add_thm_insts ctxt thm =
  let
    val tyvars = Thm.fold_terms Term.add_tvars thm [];
    val tyvars' = tyvars |> map (mk_term_type_internal o TVar);

    val tvars = Thm.fold_terms Term.add_vars thm [];
    val tvars' = tvars  |> map (Logic.mk_term o Var);

    val conj =
      Logic.mk_conjunction_list (tyvars' @ tvars') |> Thm.cterm_of ctxt |> Drule.mk_term;
  in
    ((tyvars, tvars), Conjunction.intr thm conj)
  end;

fun get_thm_insts thm =
  let
    val (thm', insts) = Conjunction.elim thm;

    val insts' = insts
      |> Drule.dest_term
      |> Thm.term_of
      |> Logic.dest_conjunction_list
      |> (fn f => fold (fn t => fn (tys, ts) =>
          term_type_cases (fn T => (T :: tys, ts)) (fn t => (tys, t :: ts)) t) f ([], []))
      ||> rev
      |>> rev;
  in
    (thm', insts')
  end;

fun instantiate_xis ctxt insts thm =
  let
    val tyvars = Thm.fold_terms Term.add_tvars thm [];
    val tvars = Thm.fold_terms Term.add_vars thm [];

    fun add_inst (xi, t) (Ts, ts) =
      (case AList.lookup (op =) tyvars xi of
        SOME S => (((xi, S), Thm.ctyp_of ctxt (Logic.dest_type t)) :: Ts, ts)
      | NONE =>
          (case AList.lookup (op =) tvars xi of
            SOME _ => (Ts, (xi, Thm.cterm_of ctxt t) :: ts)
          | NONE => error "indexname not found in thm"));

    val (instT, inst) = fold add_inst insts ([], []);
  in
    (Thm.instantiate (instT, []) thm
    |> infer_instantiate ctxt inst
    COMP_INCR asm_rl)
    |> Thm.adjust_maxidx_thm ~1
    |> restore_tags thm
  end;


datatype rule_inst =
  Named_Insts of ((indexname * string) * (term -> unit)) list * (binding * string option * mixfix) list
| Term_Insts of (indexname * term) list
| Unchecked_Term_Insts of term option list * term option list;

fun mk_pair (t, t') = Logic.mk_conjunction (Logic.mk_term t, Logic.mk_term t');

fun dest_pair t = apply2 Logic.dest_term (Logic.dest_conjunction t);

fun embed_indexname ((xi, s), f) =
  let fun wrap_xi xi t = mk_pair (Var (xi, fastype_of t), t);
  in ((xi, s), f o wrap_xi xi) end;

fun unembed_indexname t = dest_pair t |> apfst (Term.dest_Var #> fst);

fun read_where_insts (insts, fixes) =
  let
    val insts' =
      if forall (fn (_, v) => Parse_Tools.is_real_val v) insts
      then Term_Insts (map (unembed_indexname o Parse_Tools.the_real_val o snd) insts)
      else
        Named_Insts (map (fn (xi, p) => embed_indexname
          ((xi, Parse_Tools.the_parse_val p), Parse_Tools.the_parse_fun p)) insts, fixes);
  in insts' end;

fun of_rule thm  (args, concl_args) =
  let
    fun zip_vars _ [] = []
      | zip_vars (_ :: xs) (NONE :: rest) = zip_vars xs rest
      | zip_vars ((x, _) :: xs) (SOME t :: rest) = (x, t) :: zip_vars xs rest
      | zip_vars [] _ = error "More instantiations than variables in theorem";
    val insts =
      zip_vars (rev (Term.add_vars (Thm.full_prop_of thm) [])) args @
      zip_vars (rev (Term.add_vars (Thm.concl_of thm) [])) concl_args;
  in insts end;

val inst =  Args.maybe Parse_Tools.name_term;
val concl = Args.$$$ "concl" -- Args.colon;

fun close_unchecked_insts context ((insts, concl_inst), fixes) =
  let
    val ctxt = Context.proof_of context;
    val ctxt1 = ctxt |> Proof_Context.add_fixes_cmd fixes |> #2;

    val insts' = insts @ concl_inst;

    val term_insts =
      map (the_list o (Option.map Parse_Tools.the_parse_val)) insts'
      |> burrow (Syntax.read_terms ctxt1 #> Variable.export_terms ctxt1 ctxt)
      |> map (try the_single);

    val _ =
      (insts', term_insts)
      |> ListPair.app (fn (SOME p, SOME t) => Parse_Tools.the_parse_fun p t | _ => ());
    val (insts'', concl_insts'') = chop (length insts) term_insts;
   in Unchecked_Term_Insts (insts'', concl_insts'') end;

fun read_of_insts checked context ((insts, concl_insts), fixes) =
  if forall (fn SOME t => Parse_Tools.is_real_val t | NONE => true) (insts @ concl_insts)
  then
    if checked
    then
      (fn _ =>
       Term_Insts
        (map (unembed_indexname o Parse_Tools.the_real_val) (map_filter I (insts @ concl_insts))))
    else
      (fn _ =>
        Unchecked_Term_Insts
          (map (Option.map Parse_Tools.the_real_val) insts,
            map (Option.map Parse_Tools.the_real_val) concl_insts))
  else
    if checked
    then
      (fn thm =>
        Named_Insts
          (apply2
            (map (Option.map (fn p => (Parse_Tools.the_parse_val p, Parse_Tools.the_parse_fun p))))
            (insts, concl_insts)
          |> of_rule thm |> map ((fn (xi, (nm, f)) => embed_indexname ((xi, nm), f))), fixes))
    else
      let val result = close_unchecked_insts context ((insts, concl_insts), fixes);
      in fn _ => result end;


fun read_instantiate_closed ctxt (Named_Insts (insts, fixes)) thm  =
      let
        val insts' = map (fn ((v, t), _) => ((v, Position.none), t)) insts;

        val (thm_insts, thm') = add_thm_insts ctxt thm;
        val (thm'', thm_insts') =
          Rule_Insts.where_rule ctxt insts' fixes thm'
          |> get_thm_insts;

        val tyinst =
          ListPair.zip (fst thm_insts, fst thm_insts') |> map (fn ((xi, _), typ) => (xi, typ));
        val tinst =
          ListPair.zip (snd thm_insts, snd thm_insts') |> map (fn ((xi, _), t) => (xi, t));

        val _ =
          map (fn ((xi, _), f) =>
            (case AList.lookup (op =) tyinst xi of
              SOME typ => f (Logic.mk_type typ)
            | NONE =>
                (case AList.lookup (op =) tinst xi of
                  SOME t => f t
                | NONE => error "Lost indexname in instantiated theorem"))) insts;
      in
        (thm'' |> restore_tags thm)
      end
  | read_instantiate_closed ctxt (Unchecked_Term_Insts insts) thm =
      let
        val (xis, ts) = ListPair.unzip (of_rule thm insts);
        val ctxt' = Variable.declare_maxidx (Thm.maxidx_of thm) ctxt;
        val (ts', ctxt'') = Variable.import_terms false ts ctxt';
        val ts'' = Variable.export_terms ctxt'' ctxt ts';
        val insts' = ListPair.zip (xis, ts'');
      in instantiate_xis ctxt insts' thm end
  | read_instantiate_closed ctxt (Term_Insts insts) thm =
      instantiate_xis ctxt insts thm;

val _ =
  Theory.setup
    (Attrib.setup \<^binding>\<open>where\<close>
      (Scan.lift
        (Parse.and_list1 (Args.var -- (Args.$$$ "=" |-- Parse_Tools.name_term)) -- Parse.for_fixes)
        >> (fn args =>
            let val args' = read_where_insts args in
              fn (context, thm) =>
                (NONE, SOME (read_instantiate_closed (Context.proof_of context) args' thm))
            end))
      "named instantiation of theorem");

val _ =
  Theory.setup
    (Attrib.setup \<^binding>\<open>of\<close>
      (Scan.lift
        (Args.mode "unchecked" --
          (Scan.repeat (Scan.unless concl inst) --
            Scan.optional (concl |-- Scan.repeat inst) [] --
            Parse.for_fixes)) -- Scan.state >>
      (fn ((unchecked, args), context) =>
        let
          val read_insts = read_of_insts (not unchecked) context args;
        in
          fn (context, thm) =>
            let val thm' =
              if Thm.is_free_dummy thm andalso unchecked
              then Drule.free_dummy_thm
              else read_instantiate_closed (Context.proof_of context) (read_insts thm) thm
            in (NONE, SOME thm') end
        end))
      "positional instantiation of theorem");

end;
