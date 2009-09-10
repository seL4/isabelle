(*  Title:	HOL/Tools/ntuple_support.ML
    Author:	Thomas Sewell, NICTA

Support for defining instances of tuple-like types and supplying
introduction rules needed by the record package.
*)


signature ISTUPLE_SUPPORT =
sig
  val add_istuple_type: bstring * string list -> (typ * typ) -> theory ->
            (term * term * theory);

  val mk_cons_tuple: term * term -> term;
  val dest_cons_tuple: term -> term * term;

  val istuple_intros_tac: theory -> int -> tactic;

  val named_cterm_instantiate: (string * cterm) list -> thm -> thm;
end;

structure IsTupleSupport : ISTUPLE_SUPPORT =
struct

val isomN = "_TupleIsom";
val defN = "_def";

val istuple_UNIV_I = @{thm "istuple_UNIV_I"};
val istuple_True_simp = @{thm "istuple_True_simp"};

val istuple_intro = @{thm "isomorphic_tuple_intro"};
val istuple_intros = build_net (@{thms "isomorphic_tuple.intros"});

val constname = fst o dest_Const;
val tuple_istuple = (constname @{term tuple_istuple}, @{thm tuple_istuple});

val istuple_constN = constname @{term isomorphic_tuple};
val istuple_consN = constname @{term istuple_cons};

val tup_isom_typeN = fst (dest_Type @{typ "('a, 'b, 'c) tuple_isomorphism"});

fun named_cterm_instantiate values thm = let
    fun match name (Var ((name', _), _)) = name = name'
      | match name _ = false;
    fun getvar name = case (find_first (match name)
                                    (OldTerm.term_vars (prop_of thm)))
      of SOME var => cterm_of (theory_of_thm thm) var
       | NONE => raise THM ("named_cterm_instantiate: " ^ name, 0, [thm])
  in
    cterm_instantiate (map (apfst getvar) values) thm
  end;

structure IsTupleThms = TheoryDataFun
(
  type T = thm Symtab.table;
  val empty = Symtab.make [tuple_istuple];
  val copy = I;
  val extend = I;
  val merge = K (Symtab.merge Thm.eq_thm_prop);
);

fun do_typedef name repT alphas thy =
  let
    fun get_thms thy name =
      let
        val SOME { Rep_inject=rep_inject, Abs_name=absN, abs_type=absT,
          Abs_inverse=abs_inverse, ...} = Typedef.get_info thy name;
        val rewrite_rule = MetaSimplifier.rewrite_rule [istuple_UNIV_I, istuple_True_simp];
      in (map rewrite_rule [rep_inject, abs_inverse],
            Const (absN, repT --> absT), absT) end;
  in
    thy
    |> Typecopy.typecopy (Binding.name name, alphas) repT NONE
    |-> (fn (name, _) => `(fn thy => get_thms thy name))
  end;

fun mk_cons_tuple (left, right) = let
    val (leftT, rightT) = (fastype_of left, fastype_of right);
    val prodT           = HOLogic.mk_prodT (leftT, rightT);
    val isomT           = Type (tup_isom_typeN, [prodT, leftT, rightT]);
  in
    Const (istuple_consN, isomT --> leftT --> rightT --> prodT)
      $ Const (fst tuple_istuple, isomT) $ left $ right
  end;

fun dest_cons_tuple (v as Const (ic, _) $ Const _ $ left $ right)
  = if ic = istuple_consN then (left, right)
    else raise TERM ("dest_cons_tuple", [v])
  | dest_cons_tuple v = raise TERM ("dest_cons_tuple", [v]);

fun add_istuple_type (name, alphas) (leftT, rightT) thy =
let
  val repT = HOLogic.mk_prodT (leftT, rightT);

  val (([rep_inject, abs_inverse], absC, absT), typ_thy) =
    thy
    |> do_typedef name repT alphas
    ||> Sign.add_path name;

  (* construct a type and body for the isomorphism constant by
     instantiating the theorem to which the definition will be applied *)
  val intro_inst = rep_inject RS
                   (named_cterm_instantiate [("abst", cterm_of typ_thy absC)]
                        istuple_intro);
  val (_, body)  = Logic.dest_equals (List.last (prems_of intro_inst));
  val isomT      = fastype_of body;
  val isomBind   = Binding.name (name ^ isomN);
  val isom       = Const (Sign.full_name typ_thy isomBind, isomT);
  val isom_spec  = (name ^ isomN ^ defN, Logic.mk_equals (isom, body));

  val ([isom_def], cdef_thy) =
    typ_thy
    |> Sign.add_consts_i [Syntax.no_syn (isomBind, isomT)]
    |> PureThy.add_defs false [Thm.no_attributes (apfst Binding.name isom_spec)];

  val istuple = isom_def RS (abs_inverse RS (rep_inject RS istuple_intro));
  val cons    = Const (istuple_consN, isomT --> leftT --> rightT --> absT)

  val thm_thy =
    cdef_thy
    |> IsTupleThms.map (Symtab.insert Thm.eq_thm_prop
                           (constname isom, istuple))
    |> Sign.parent_path;
in
  (isom, cons $ isom, thm_thy)
end;

fun istuple_intros_tac thy = let
    val isthms  = IsTupleThms.get thy;
    fun err s t = raise TERM ("istuple_intros_tac: " ^ s, [t]);
    val use_istuple_thm_tac = SUBGOAL (fn (goal, n) => let
        val goal' = Envir.beta_eta_contract goal;
        val isom  = case goal' of (Const tp $ (Const pr $ Const is))
                    => if fst tp = "Trueprop" andalso fst pr = istuple_constN
                       then Const is
                       else err "unexpected goal predicate" goal'
            | _ => err "unexpected goal format" goal';
        val isthm = case Symtab.lookup isthms (constname isom) of
                    SOME isthm => isthm
                  | NONE => err "no thm found for constant" isom;
      in rtac isthm n end);
  in
    fn n => resolve_from_net_tac istuple_intros n
            THEN use_istuple_thm_tac n
  end;

end;


