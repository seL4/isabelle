(*  Title:      ZF/Tools/datatype_package.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Datatype/Codatatype Definitions.

The functor will be instantiated for normal sums/products (datatype defs)
                         and non-standard sums/products (codatatype defs)

Sums are used only for mutual recursion;
Products are used only to derive "streamlined" induction rules for relations
*)

type datatype_result =
   {con_defs   : thm list,             (*definitions made in thy*)
    case_eqns  : thm list,             (*equations for case operator*)
    recursor_eqns : thm list,          (*equations for the recursor*)
    free_iffs  : thm list,             (*freeness rewrite rules*)
    free_SEs   : thm list,             (*freeness destruct rules*)
    mk_free    : string -> thm};       (*function to make freeness theorems*)

signature DATATYPE_ARG =
sig
  val intrs : thm list
  val elims : thm list
end;

signature DATATYPE_PACKAGE =
sig
  (*Insert definitions for the recursive sets, which
     must *already* be declared as constants in parent theory!*)
  val add_datatype_i: term * term list -> Ind_Syntax.constructor_spec list list ->
    thm list * thm list * thm list -> theory -> theory * inductive_result * datatype_result
  val add_datatype: string * string list -> (string * string list * mixfix) list list ->
    (Facts.ref * Attrib.src list) list * (Facts.ref * Attrib.src list) list *
    (Facts.ref * Attrib.src list) list -> theory -> theory * inductive_result * datatype_result
end;

functor Add_datatype_def_Fun
 (structure Fp: FP and Pr : PR and CP: CARTPROD and Su : SU
  and Ind_Package : INDUCTIVE_PACKAGE
  and Datatype_Arg : DATATYPE_ARG
  val coind : bool): DATATYPE_PACKAGE =
struct

(*con_ty_lists specifies the constructors in the form (name, prems, mixfix) *)

(*univ or quniv constitutes the sum domain for mutual recursion;
  it is applied to the datatype parameters and to Consts occurring in the
  definition other than Nat.nat and the datatype sets themselves.
  FIXME: could insert all constant set expressions, e.g. nat->nat.*)
fun data_domain co (rec_tms, con_ty_lists) =
    let val rec_hds = map head_of rec_tms
        val dummy = assert_all is_Const rec_hds
          (fn t => "Datatype set not previously declared as constant: " ^
                   Syntax.string_of_term_global @{theory IFOL} t);
        val rec_names = (*nat doesn't have to be added*)
            @{const_name nat} :: map (#1 o dest_Const) rec_hds
        val u = if co then @{const QUniv.quniv} else @{const Univ.univ}
        val cs = (fold o fold) (fn (_, _, _, prems) => prems |> (fold o fold_aterms)
          (fn t as Const (a, _) => if member (op =) rec_names a then I else insert (op =) t
            | _ => I)) con_ty_lists [];
    in  u $ Ind_Syntax.union_params (hd rec_tms, cs)  end;

fun add_datatype_i (dom_sum, rec_tms) con_ty_lists (monos, type_intrs, type_elims) thy =
 let
  val dummy = (*has essential ancestors?*)
    Theory.requires thy "Datatype_ZF" "(co)datatype definitions";

  val rec_hds = map head_of rec_tms;

  val dummy = assert_all is_Const rec_hds
          (fn t => "Datatype set not previously declared as constant: " ^
                   Syntax.string_of_term_global thy t);

  val rec_names = map (#1 o dest_Const) rec_hds
  val rec_base_names = map Long_Name.base_name rec_names
  val big_rec_base_name = space_implode "_" rec_base_names

  val thy_path = thy |> Sign.add_path big_rec_base_name

  val big_rec_name = Sign.intern_const thy_path big_rec_base_name;

  val intr_tms = Ind_Syntax.mk_all_intr_tms thy_path (rec_tms, con_ty_lists);

  val dummy =
    writeln ((if coind then "Codatatype" else "Datatype") ^ " definition " ^ quote big_rec_name);

  val case_varname = "f";                (*name for case variables*)

  (** Define the constructors **)

  (*The empty tuple is 0*)
  fun mk_tuple [] = @{const zero}
    | mk_tuple args = foldr1 (fn (t1, t2) => Pr.pair $ t1 $ t2) args;

  fun mk_inject n k u = Balanced_Tree.access
    {left = fn t => Su.inl $ t, right = fn t => Su.inr $ t, init = u} n k;

  val npart = length rec_names;  (*number of mutually recursive parts*)


  val full_name = Sign.full_bname thy_path;

  (*Make constructor definition;
    kpart is the number of this mutually recursive part*)
  fun mk_con_defs (kpart, con_ty_list) =
    let val ncon = length con_ty_list    (*number of constructors*)
        fun mk_def (((id,T,syn), name, args, prems), kcon) =
              (*kcon is index of constructor*)
            Misc_Legacy.mk_defpair (list_comb (Const (full_name name, T), args),
                        mk_inject npart kpart
                        (mk_inject ncon kcon (mk_tuple args)))
    in  ListPair.map mk_def (con_ty_list, 1 upto ncon)  end;


  (*** Define the case operator ***)

  (*Combine split terms using case; yields the case operator for one part*)
  fun call_case case_list =
    let fun call_f (free,[]) = Abs("null", @{typ i}, free)
          | call_f (free,args) =
                CP.ap_split (foldr1 CP.mk_prod (map (#2 o dest_Free) args))
                            @{typ i}
                            free
    in  Balanced_Tree.make (fn (t1, t2) => Su.elim $ t1 $ t2) (map call_f case_list)  end;

  (** Generating function variables for the case definition
      Non-identifiers (e.g. infixes) get a name of the form f_op_nnn. **)

  (*The function variable for a single constructor*)
  fun add_case ((_, T, _), name, args, _) (opno, cases) =
    if Lexicon.is_identifier name then
      (opno, (Free (case_varname ^ "_" ^ name, T), args) :: cases)
    else
      (opno + 1, (Free (case_varname ^ "_op_" ^ string_of_int opno, T), args)
       :: cases);

  (*Treatment of a list of constructors, for one part
    Result adds a list of terms, each a function variable with arguments*)
  fun add_case_list con_ty_list (opno, case_lists) =
    let val (opno', case_list) = fold_rev add_case con_ty_list (opno, [])
    in (opno', case_list :: case_lists) end;

  (*Treatment of all parts*)
  val (_, case_lists) = fold_rev add_case_list con_ty_lists (1, []);

  (*extract the types of all the variables*)
  val case_typ = maps (map (#2 o #1)) con_ty_lists ---> @{typ "i => i"};

  val case_base_name = big_rec_base_name ^ "_case";
  val case_name = full_name case_base_name;

  (*The list of all the function variables*)
  val case_args = maps (map #1) case_lists;

  val case_const = Const (case_name, case_typ);
  val case_tm = list_comb (case_const, case_args);

  val case_def = Misc_Legacy.mk_defpair
    (case_tm, Balanced_Tree.make (fn (t1, t2) => Su.elim $ t1 $ t2) (map call_case case_lists));


  (** Generating function variables for the recursor definition
      Non-identifiers (e.g. infixes) get a name of the form f_op_nnn. **)

  (*a recursive call for x is the application rec`x  *)
  val rec_call = @{const apply} $ Free ("rec", @{typ i});

  (*look back down the "case args" (which have been reversed) to
    determine the de Bruijn index*)
  fun make_rec_call ([], _) arg = error
          "Internal error in datatype (variable name mismatch)"
    | make_rec_call (a::args, i) arg =
           if a = arg then rec_call $ Bound i
           else make_rec_call (args, i+1) arg;

  (*creates one case of the "X_case" definition of the recursor*)
  fun call_recursor ((case_var, case_args), (recursor_var, recursor_args)) =
      let fun add_abs (Free(a,T), u) = Abs(a,T,u)
          val ncase_args = length case_args
          val bound_args = map Bound ((ncase_args - 1) downto 0)
          val rec_args = map (make_rec_call (rev case_args,0))
                         (List.drop(recursor_args, ncase_args))
      in
          List.foldr add_abs
            (list_comb (recursor_var,
                        bound_args @ rec_args)) case_args
      end

  (*Find each recursive argument and add a recursive call for it*)
  fun rec_args [] = []
    | rec_args ((Const(@{const_name mem},_)$arg$X)::prems) =
       (case head_of X of
            Const(a,_) => (*recursive occurrence?*)
                          if member (op =) rec_names a
                              then arg :: rec_args prems
                          else rec_args prems
          | _ => rec_args prems)
    | rec_args (_::prems) = rec_args prems;

  (*Add an argument position for each occurrence of a recursive set.
    Strictly speaking, the recursive arguments are the LAST of the function
    variable, but they all have type "i" anyway*)
  fun add_rec_args args' T = (map (fn _ => @{typ i}) args') ---> T

  (*Plug in the function variable type needed for the recursor
    as well as the new arguments (recursive calls)*)
  fun rec_ty_elem ((id, T, syn), name, args, prems) =
      let val args' = rec_args prems
      in ((id, add_rec_args args' T, syn),
          name, args @ args', prems)
      end;

  val rec_ty_lists = (map (map rec_ty_elem) con_ty_lists);

  (*Treatment of all parts*)
  val (_, recursor_lists) = fold_rev add_case_list rec_ty_lists (1, []);

  (*extract the types of all the variables*)
  val recursor_typ = maps (map (#2 o #1)) rec_ty_lists ---> @{typ "i => i"};

  val recursor_base_name = big_rec_base_name ^ "_rec";
  val recursor_name = full_name recursor_base_name;

  (*The list of all the function variables*)
  val recursor_args = maps (map #1) recursor_lists;

  val recursor_tm =
    list_comb (Const (recursor_name, recursor_typ), recursor_args);

  val recursor_cases = map call_recursor (flat case_lists ~~ flat recursor_lists);

  val recursor_def =
      Misc_Legacy.mk_defpair
        (recursor_tm,
         @{const Univ.Vrecursor} $
           absfree ("rec", @{typ i}) (list_comb (case_const, recursor_cases)));

  (* Build the new theory *)

  val need_recursor = (not coind andalso recursor_typ <> case_typ);

  fun add_recursor thy =
    if need_recursor then
      thy
      |> Sign.add_consts_i
        [(Binding.name recursor_base_name, recursor_typ, NoSyn)]
      |> (snd o Global_Theory.add_defs false [(Thm.no_attributes o apfst Binding.name) recursor_def])
    else thy;

  val (con_defs, thy0) = thy_path
             |> Sign.add_consts_i
                 (map (fn (c, T, mx) => (Binding.name c, T, mx))
                  ((case_base_name, case_typ, NoSyn) :: map #1 (flat con_ty_lists)))
             |> Global_Theory.add_defs false
                 (map (Thm.no_attributes o apfst Binding.name)
                  (case_def ::
                   flat (ListPair.map mk_con_defs (1 upto npart, con_ty_lists))))
             ||> add_recursor
             ||> Sign.parent_path

  val intr_names = map (Binding.name o #2) (flat con_ty_lists);
  val (thy1, ind_result) =
    thy0 |> Ind_Package.add_inductive_i
      false (rec_tms, dom_sum) (map Thm.no_attributes (intr_names ~~ intr_tms))
      (monos, con_defs, type_intrs @ Datatype_Arg.intrs, type_elims @ Datatype_Arg.elims);

  (**** Now prove the datatype theorems in this theory ****)


  (*** Prove the case theorems ***)

  (*Each equation has the form
    case(f_con1,...,f_conn)(coni(args)) = f_coni(args) *)
  fun mk_case_eqn (((_,T,_), name, args, _), case_free) =
    FOLogic.mk_Trueprop
      (FOLogic.mk_eq
       (case_tm $
         (list_comb (Const (Sign.intern_const thy1 name,T),
                     args)),
        list_comb (case_free, args)));

  val case_trans = hd con_defs RS @{thm def_trans}
  and split_trans = Pr.split_eq RS @{thm meta_eq_to_obj_eq} RS @{thm trans};

  fun prove_case_eqn (arg, con_def) =
    Goal.prove_global thy1 [] []
      (Ind_Syntax.traceIt "next case equation = " thy1 (mk_case_eqn arg))
      (*Proves a single case equation.  Could use simp_tac, but it's slower!*)
      (fn _ => EVERY
        [rewrite_goals_tac [con_def],
         rtac case_trans 1,
         REPEAT
           (resolve_tac [@{thm refl}, split_trans,
             Su.case_inl RS @{thm trans}, Su.case_inr RS @{thm trans}] 1)]);

  val free_iffs = map Drule.export_without_context (con_defs RL [@{thm def_swap_iff}]);

  val case_eqns = map prove_case_eqn (flat con_ty_lists ~~ case_args ~~ tl con_defs);

  (*** Prove the recursor theorems ***)

  val recursor_eqns = case try (Misc_Legacy.get_def thy1) recursor_base_name of
     NONE => (writeln "  [ No recursion operator ]";
              [])
   | SOME recursor_def =>
      let
        (*Replace subterms rec`x (where rec is a Free var) by recursor_tm(x) *)
        fun subst_rec (Const(@{const_name apply},_) $ Free _ $ arg) = recursor_tm $ arg
          | subst_rec tm =
              let val (head, args) = strip_comb tm
              in  list_comb (head, map subst_rec args)  end;

        (*Each equation has the form
          REC(coni(args)) = f_coni(args, REC(rec_arg), ...)
          where REC = recursor(f_con1,...,f_conn) and rec_arg is a recursive
          constructor argument.*)
        fun mk_recursor_eqn (((_,T,_), name, args, _), recursor_case) =
          FOLogic.mk_Trueprop
           (FOLogic.mk_eq
            (recursor_tm $
             (list_comb (Const (Sign.intern_const thy1 name,T),
                         args)),
             subst_rec (Term.betapplys (recursor_case, args))));

        val recursor_trans = recursor_def RS @{thm def_Vrecursor} RS @{thm trans};

        fun prove_recursor_eqn arg =
          Goal.prove_global thy1 [] []
            (Ind_Syntax.traceIt "next recursor equation = " thy1 (mk_recursor_eqn arg))
            (*Proves a single recursor equation.*)
            (fn _ => EVERY
              [rtac recursor_trans 1,
               simp_tac (rank_ss addsimps case_eqns) 1,
               IF_UNSOLVED (simp_tac (rank_ss addsimps tl con_defs) 1)]);
      in
         map prove_recursor_eqn (flat con_ty_lists ~~ recursor_cases)
      end

  val constructors =
      map (head_of o #1 o Logic.dest_equals o Thm.prop_of) (tl con_defs);

  val free_SEs = map Drule.export_without_context (Ind_Syntax.mk_free_SEs free_iffs);

  val {intrs, elim, induct, mutual_induct, ...} = ind_result

  (*Typical theorems have the form ~con1=con2, con1=con2==>False,
    con1(x)=con1(y) ==> x=y, con1(x)=con1(y) <-> x=y, etc.  *)
  fun mk_free s =
    let
      val thy = theory_of_thm elim;
      val ctxt = Proof_Context.init_global thy;
    in
      Goal.prove_global thy [] [] (Syntax.read_prop ctxt s)
        (fn _ => EVERY
         [rewrite_goals_tac con_defs,
          fast_tac (put_claset ZF_cs ctxt addSEs free_SEs @ Su.free_SEs) 1])
    end;

  val simps = case_eqns @ recursor_eqns;

  val dt_info =
        {inductive = true,
         constructors = constructors,
         rec_rewrites = recursor_eqns,
         case_rewrites = case_eqns,
         induct = induct,
         mutual_induct = mutual_induct,
         exhaustion = elim};

  val con_info =
        {big_rec_name = big_rec_name,
         constructors = constructors,
            (*let primrec handle definition by cases*)
         free_iffs = free_iffs,
         rec_rewrites = (case recursor_eqns of
                             [] => case_eqns | _ => recursor_eqns)};

  (*associate with each constructor the datatype name and rewrites*)
  val con_pairs = map (fn c => (#1 (dest_Const c), con_info)) constructors

 in
  (*Updating theory components: simprules and datatype info*)
  (thy1 |> Sign.add_path big_rec_base_name
        |> Global_Theory.add_thmss
         [((Binding.name "simps", simps), [Simplifier.simp_add]),
          ((Binding.empty, intrs), [Cla.safe_intro NONE]),
          ((Binding.name "con_defs", con_defs), []),
          ((Binding.name "case_eqns", case_eqns), []),
          ((Binding.name "recursor_eqns", recursor_eqns), []),
          ((Binding.name "free_iffs", free_iffs), []),
          ((Binding.name "free_elims", free_SEs), [])] |> snd
        |> DatatypesData.map (Symtab.update (big_rec_name, dt_info))
        |> ConstructorsData.map (fold Symtab.update con_pairs)
        |> Sign.parent_path,
   ind_result,
   {con_defs = con_defs,
    case_eqns = case_eqns,
    recursor_eqns = recursor_eqns,
    free_iffs = free_iffs,
    free_SEs = free_SEs,
    mk_free = mk_free})
  end;

fun add_datatype (sdom, srec_tms) scon_ty_lists (raw_monos, raw_type_intrs, raw_type_elims) thy =
  let
    val ctxt = Proof_Context.init_global thy;
    fun read_is strs =
      map (Syntax.parse_term ctxt #> Type.constraint @{typ i}) strs
      |> Syntax.check_terms ctxt;

    val rec_tms = read_is srec_tms;
    val con_ty_lists = Ind_Syntax.read_constructs ctxt scon_ty_lists;
    val dom_sum =
      if sdom = "" then data_domain coind (rec_tms, con_ty_lists)
      else singleton read_is sdom;
    val monos = Attrib.eval_thms ctxt raw_monos;
    val type_intrs = Attrib.eval_thms ctxt raw_type_intrs;
    val type_elims = Attrib.eval_thms ctxt raw_type_elims;
  in add_datatype_i (dom_sum, rec_tms) con_ty_lists (monos, type_intrs, type_elims) thy end;


(* outer syntax *)

fun mk_datatype ((((dom, dts), monos), type_intrs), type_elims) =
  #1 o add_datatype (dom, map fst dts) (map snd dts) (monos, type_intrs, type_elims);

val con_decl =
  Parse.name -- Scan.optional (@{keyword "("} |-- Parse.list1 Parse.term --| @{keyword ")"}) [] --
    Parse.opt_mixfix >> Parse.triple1;

val datatype_decl =
  (Scan.optional ((@{keyword "\<subseteq>"} || @{keyword "<="}) |-- Parse.!!! Parse.term) "") --
  Parse.and_list1 (Parse.term -- (@{keyword "="} |-- Parse.enum1 "|" con_decl)) --
  Scan.optional (@{keyword "monos"} |-- Parse.!!! Parse_Spec.xthms1) [] --
  Scan.optional (@{keyword "type_intros"} |-- Parse.!!! Parse_Spec.xthms1) [] --
  Scan.optional (@{keyword "type_elims"} |-- Parse.!!! Parse_Spec.xthms1) []
  >> (Toplevel.theory o mk_datatype);

val coind_prefix = if coind then "co" else "";

val _ =
  Outer_Syntax.command (coind_prefix ^ "datatype")
    ("define " ^ coind_prefix ^ "datatype") Keyword.thy_decl datatype_decl;

end;

