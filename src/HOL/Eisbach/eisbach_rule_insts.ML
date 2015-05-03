(*  Title:      HOL/Eisbach/eisbach_rule_insts.ML
    Author:     Daniel Matichuk, NICTA/UNSW

Eisbach-aware variants of the "where" and "of" attributes.

Alternate syntax for rule_insts.ML participates in token closures by
examining the behaviour of Rule_Insts.where_rule and instantiating token
values accordingly. Instantiations in re-interpretation are done with
Drule.cterm_instantiate.
*)

structure Eisbach_Rule_Insts : sig end =
struct

fun restore_tags thm = Thm.map_tags (K (Thm.get_tags thm));

fun add_thm_insts thm =
  let
    val thy = Thm.theory_of_thm thm;
    val tyvars = Thm.fold_terms Term.add_tvars thm [];
    val tyvars' = tyvars |> map (Logic.mk_term o Logic.mk_type o TVar);

    val tvars = Thm.fold_terms Term.add_vars thm [];
    val tvars' = tvars  |> map (Logic.mk_term o Var);

    val conj =
      Logic.mk_conjunction_list (tyvars' @ tvars') |> Thm.global_cterm_of thy |> Drule.mk_term;
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
      |> map Logic.dest_term
      |> (fn f => fold (fn t => fn (tys, ts) =>
          (case try Logic.dest_type t of
            SOME T => (T :: tys, ts)
          | NONE => (tys, t :: ts))) f ([], []))
      ||> rev
      |>> rev;
  in
    (thm', insts')
  end;

fun instantiate_xis insts thm =
  let
    val tyvars = Thm.fold_terms Term.add_tvars thm [];
    val tvars = Thm.fold_terms Term.add_vars thm [];
    val cert = Thm.global_cterm_of (Thm.theory_of_thm thm);
    val certT = Thm.global_ctyp_of (Thm.theory_of_thm thm);

    fun add_inst (xi, t) (Ts, ts) =
      (case AList.lookup (op =) tyvars xi of
        SOME S => ((certT (TVar (xi, S)), certT (Logic.dest_type t)) :: Ts, ts)
      | NONE =>
          (case AList.lookup (op =) tvars xi of
            SOME T => (Ts, (cert (Var (xi, T)), cert t) :: ts)
          | NONE => error "indexname not found in thm"));

    val (cTinsts, cinsts) = fold add_inst insts ([], []);
  in
    (Thm.instantiate (cTinsts, []) thm
    |> Drule.cterm_instantiate cinsts
    COMP_INCR asm_rl)
    |> Thm.adjust_maxidx_thm ~1
    |> restore_tags thm
  end;


datatype rule_inst =
  Named_Insts of ((indexname * string) * (term -> unit)) list
| Term_Insts of (indexname * term) list;

fun embed_indexname ((xi, s), f) =
  let
    fun wrap_xi xi t =
      Logic.mk_conjunction (Logic.mk_term (Var (xi, fastype_of t)), Logic.mk_term t);
  in ((xi, s), f o wrap_xi xi) end;

fun unembed_indexname t =
  let
    val (t, t') = apply2 Logic.dest_term (Logic.dest_conjunction t);
    val (xi, _) = Term.dest_Var t;
  in (xi, t') end;

fun read_where_insts toks =
  let
    val parser =
      Parse.!!!
        (Parse.and_list1 (Args.var -- (Args.$$$ "=" |-- Parse_Tools.name_term)) -- Parse.for_fixes)
          --| Scan.ahead Parse.eof;
    val (insts, fixes) = the (Scan.read Token.stopper parser toks);

    val insts' =
      if forall (fn (_, v) => Parse_Tools.is_real_val v) insts
      then Term_Insts (map (fn (_, t) => unembed_indexname (Parse_Tools.the_real_val t)) insts)
      else Named_Insts (map (fn (xi, p) => embed_indexname
            ((xi, Parse_Tools.the_parse_val p), Parse_Tools.the_parse_fun p)) insts);
  in
    (insts', fixes)
  end;

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

fun read_of_insts toks thm =
  let
    val parser =
      Parse.!!!
        ((Scan.repeat (Scan.unless concl inst) -- Scan.optional (concl |-- Scan.repeat inst) [])
          -- Parse.for_fixes) --| Scan.ahead Parse.eof;
    val ((insts, concl_insts), fixes) =
      the (Scan.read Token.stopper parser toks);

    val insts' =
      if forall (fn SOME t => Parse_Tools.is_real_val t | NONE => true) (insts @ concl_insts)
      then
        Term_Insts
          (map_filter
            (Option.map (Parse_Tools.the_real_val #> unembed_indexname)) (insts @ concl_insts))
      else
        Named_Insts
          (apply2
            (map (Option.map (fn p => (Parse_Tools.the_parse_val p, Parse_Tools.the_parse_fun p))))
            (insts, concl_insts)
          |> of_rule thm |> map ((fn (xi, (nm, tok)) => embed_indexname ((xi, nm), tok))));
  in
    (insts', fixes)
  end;

fun read_instantiate_closed ctxt ((Named_Insts insts), fixes) thm  =
      let
        val insts' = map (fn ((v, t), _) => ((v, Position.none), t)) insts;

        val (thm_insts, thm') = add_thm_insts thm
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
  | read_instantiate_closed _ ((Term_Insts insts), _) thm = instantiate_xis insts thm;

val parse_all : Token.T list context_parser = Scan.lift (Scan.many Token.not_eof);

val _ =
  Theory.setup
    (Attrib.setup @{binding "where"} (parse_all >>
      (fn toks => Thm.rule_attribute (fn context =>
        read_instantiate_closed (Context.proof_of context) (read_where_insts toks))))
      "named instantiation of theorem");

val _ =
  Theory.setup
    (Attrib.setup @{binding "of"} (parse_all >>
      (fn toks => Thm.rule_attribute (fn context => fn thm =>
        read_instantiate_closed (Context.proof_of context) (read_of_insts toks thm) thm)))
      "positional instantiation of theorem");

end;
