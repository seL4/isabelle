(*  Title:      ZF/Tools/datatype_package.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Datatype/Codatatype Definitions

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

(*Functor's result signature*)
signature DATATYPE_PACKAGE =
sig
  (*Insert definitions for the recursive sets, which
     must *already* be declared as constants in parent theory!*)
  val add_datatype_i: term * term list -> Ind_Syntax.constructor_spec list list ->
    thm list * thm list * thm list -> theory -> theory * inductive_result * datatype_result
  val add_datatype_x: string * string list -> (string * string list * mixfix) list list ->
    thm list * thm list * thm list -> theory -> theory * inductive_result * datatype_result
  val add_datatype: string * string list -> (string * string list * mixfix) list list ->
    (xstring * Args.src list) list * (xstring * Args.src list) list *
    (xstring * Args.src list) list -> theory -> theory * inductive_result * datatype_result
end;

functor Add_datatype_def_Fun
 (structure Fp: FP and Pr : PR and CP: CARTPROD and Su : SU
  and Ind_Package : INDUCTIVE_PACKAGE
  and Datatype_Arg : DATATYPE_ARG
  val coind : bool): DATATYPE_PACKAGE =
struct

(*con_ty_lists specifies the constructors in the form (name, prems, mixfix) *)

fun add_datatype_i (dom_sum, rec_tms) con_ty_lists (monos, type_intrs, type_elims) thy =
 let
  val dummy = (*has essential ancestors?*)
    Theory.requires thy "Datatype" "(co)datatype definitions";

  val rec_names = map (#1 o dest_Const o head_of) rec_tms
  val rec_base_names = map Sign.base_name rec_names
  val big_rec_base_name = space_implode "_" rec_base_names

  val thy_path = thy |> Theory.add_path big_rec_base_name
  val sign = sign_of thy_path

  val big_rec_name = Sign.intern_const sign big_rec_base_name;

  val intr_tms = Ind_Syntax.mk_all_intr_tms sign (rec_tms, con_ty_lists);

  val dummy =
    writeln ((if coind then "Codatatype" else "Datatype") ^ " definition " ^ quote big_rec_name);

  val case_varname = "f";                (*name for case variables*)

  (** Define the constructors **)

  (*The empty tuple is 0*)
  fun mk_tuple [] = Const("0",iT)
    | mk_tuple args = foldr1 (fn (t1, t2) => Pr.pair $ t1 $ t2) args;

  fun mk_inject n k u = access_bal (fn t => Su.inl $ t, fn t => Su.inr $ t, u) n k;

  val npart = length rec_names;  (*number of mutually recursive parts*)


  val full_name = Sign.full_name sign;

  (*Make constructor definition;
    kpart is the number of this mutually recursive part*)
  fun mk_con_defs (kpart, con_ty_list) =
    let val ncon = length con_ty_list    (*number of constructors*)
        fun mk_def (((id,T,syn), name, args, prems), kcon) =
              (*kcon is index of constructor*)
            Logic.mk_defpair (list_comb (Const (full_name name, T), args),
                        mk_inject npart kpart
                        (mk_inject ncon kcon (mk_tuple args)))
    in  ListPair.map mk_def (con_ty_list, 1 upto ncon)  end;


  (*** Define the case operator ***)

  (*Combine split terms using case; yields the case operator for one part*)
  fun call_case case_list =
    let fun call_f (free,[]) = Abs("null", iT, free)
          | call_f (free,args) =
                CP.ap_split (foldr1 CP.mk_prod (map (#2 o dest_Free) args))
                            Ind_Syntax.iT
                            free
    in  fold_bal (fn (t1, t2) => Su.elim $ t1 $ t2) (map call_f case_list)  end;

  (** Generating function variables for the case definition
      Non-identifiers (e.g. infixes) get a name of the form f_op_nnn. **)

  (*The function variable for a single constructor*)
  fun add_case (((_, T, _), name, args, _), (opno, cases)) =
    if Syntax.is_identifier name then
      (opno, (Free (case_varname ^ "_" ^ name, T), args) :: cases)
    else
      (opno + 1, (Free (case_varname ^ "_op_" ^ string_of_int opno, T), args)
       :: cases);

  (*Treatment of a list of constructors, for one part
    Result adds a list of terms, each a function variable with arguments*)
  fun add_case_list (con_ty_list, (opno, case_lists)) =
    let val (opno', case_list) = foldr add_case (con_ty_list, (opno, []))
    in (opno', case_list :: case_lists) end;

  (*Treatment of all parts*)
  val (_, case_lists) = foldr add_case_list (con_ty_lists, (1,[]));

  (*extract the types of all the variables*)
  val case_typ = flat (map (map (#2 o #1)) con_ty_lists) ---> (iT-->iT);

  val case_base_name = big_rec_base_name ^ "_case";
  val case_name = full_name case_base_name;

  (*The list of all the function variables*)
  val case_args = flat (map (map #1) case_lists);

  val case_const = Const (case_name, case_typ);
  val case_tm = list_comb (case_const, case_args);

  val case_def = Logic.mk_defpair
           (case_tm, fold_bal (fn (t1, t2) => Su.elim $ t1 $ t2) (map call_case case_lists));


  (** Generating function variables for the recursor definition
      Non-identifiers (e.g. infixes) get a name of the form f_op_nnn. **)

  (*a recursive call for x is the application rec`x  *)
  val rec_call = Ind_Syntax.apply_const $ Free ("rec", iT);

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
          foldr add_abs
            (case_args, list_comb (recursor_var,
                                   bound_args @ rec_args))
      end

  (*Find each recursive argument and add a recursive call for it*)
  fun rec_args [] = []
    | rec_args ((Const("op :",_)$arg$X)::prems) =
       (case head_of X of
            Const(a,_) => (*recursive occurrence?*)
                          if a mem_string rec_names
                              then arg :: rec_args prems
                          else rec_args prems
          | _ => rec_args prems)
    | rec_args (_::prems) = rec_args prems;

  (*Add an argument position for each occurrence of a recursive set.
    Strictly speaking, the recursive arguments are the LAST of the function
    variable, but they all have type "i" anyway*)
  fun add_rec_args args' T = (map (fn _ => iT) args') ---> T

  (*Plug in the function variable type needed for the recursor
    as well as the new arguments (recursive calls)*)
  fun rec_ty_elem ((id, T, syn), name, args, prems) =
      let val args' = rec_args prems
      in ((id, add_rec_args args' T, syn),
          name, args @ args', prems)
      end;

  val rec_ty_lists = (map (map rec_ty_elem) con_ty_lists);

  (*Treatment of all parts*)
  val (_, recursor_lists) = foldr add_case_list (rec_ty_lists, (1,[]));

  (*extract the types of all the variables*)
  val recursor_typ = flat (map (map (#2 o #1)) rec_ty_lists)
                         ---> (iT-->iT);

  val recursor_base_name = big_rec_base_name ^ "_rec";
  val recursor_name = full_name recursor_base_name;

  (*The list of all the function variables*)
  val recursor_args = flat (map (map #1) recursor_lists);

  val recursor_tm =
    list_comb (Const (recursor_name, recursor_typ), recursor_args);

  val recursor_cases = map call_recursor
                         (flat case_lists ~~ flat recursor_lists)

  val recursor_def =
      Logic.mk_defpair
        (recursor_tm,
         Ind_Syntax.Vrecursor_const $
           absfree ("rec", iT, list_comb (case_const, recursor_cases)));

  (* Build the new theory *)

  val need_recursor = (not coind andalso recursor_typ <> case_typ);

  fun add_recursor thy =
      if need_recursor then
           thy |> Theory.add_consts_i
                    [(recursor_base_name, recursor_typ, NoSyn)]
               |> (#1 o PureThy.add_defs_i false [Thm.no_attributes recursor_def])
      else thy;

  val (thy0, con_defs) = thy_path
             |> Theory.add_consts_i
                 ((case_base_name, case_typ, NoSyn) ::
                  map #1 (flat con_ty_lists))
             |> PureThy.add_defs_i false
                 (map Thm.no_attributes
                  (case_def ::
                   flat (ListPair.map mk_con_defs
                         (1 upto npart, con_ty_lists))))
             |>> add_recursor
             |>> Theory.parent_path

  val intr_names = map #2 (flat con_ty_lists);
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
         (list_comb (Const (Sign.intern_const (sign_of thy1) name,T),
                     args)),
        list_comb (case_free, args)));

  val case_trans = hd con_defs RS Ind_Syntax.def_trans
  and split_trans = Pr.split_eq RS meta_eq_to_obj_eq RS trans;

  (*Proves a single case equation.  Could use simp_tac, but it's slower!*)
  fun case_tacsf con_def _ =
    [rewtac con_def,
     rtac case_trans 1,
     REPEAT (resolve_tac [refl, split_trans,
                          Su.case_inl RS trans,
                          Su.case_inr RS trans] 1)];

  fun prove_case_eqn (arg,con_def) =
      prove_goalw_cterm []
        (Ind_Syntax.traceIt "next case equation = "
           (cterm_of (sign_of thy1) (mk_case_eqn arg)))
        (case_tacsf con_def);

  val free_iffs = map standard (con_defs RL [Ind_Syntax.def_swap_iff]);

  val case_eqns =
      map prove_case_eqn
         (flat con_ty_lists ~~ case_args ~~ tl con_defs);

  (*** Prove the recursor theorems ***)

  val recursor_eqns = case try (get_def thy1) recursor_base_name of
     None => (writeln "  [ No recursion operator ]";
              [])
   | Some recursor_def =>
      let
        (*Replace subterms rec`x (where rec is a Free var) by recursor_tm(x) *)
        fun subst_rec (Const("op `",_) $ Free _ $ arg) = recursor_tm $ arg
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
             (list_comb (Const (Sign.intern_const (sign_of thy1) name,T),
                         args)),
             subst_rec (foldl betapply (recursor_case, args))));

        val recursor_trans = recursor_def RS def_Vrecursor RS trans;

        (*Proves a single recursor equation.*)
        fun recursor_tacsf _ =
          [rtac recursor_trans 1,
           simp_tac (rank_ss addsimps case_eqns) 1,
           IF_UNSOLVED (simp_tac (rank_ss addsimps tl con_defs) 1)];

        fun prove_recursor_eqn arg =
            prove_goalw_cterm []
              (Ind_Syntax.traceIt "next recursor equation = "
                (cterm_of (sign_of thy1) (mk_recursor_eqn arg)))
              recursor_tacsf
      in
         map prove_recursor_eqn (flat con_ty_lists ~~ recursor_cases)
      end

  val constructors =
      map (head_of o #1 o Logic.dest_equals o #prop o rep_thm) (tl con_defs);

  val free_SEs = map standard (Ind_Syntax.mk_free_SEs free_iffs);

  val {intrs, elim, induct, mutual_induct, ...} = ind_result

  (*Typical theorems have the form ~con1=con2, con1=con2==>False,
    con1(x)=con1(y) ==> x=y, con1(x)=con1(y) <-> x=y, etc.  *)
  fun mk_free s =
      prove_goalw (theory_of_thm elim)   (*Don't use thy1: it will be stale*)
                  con_defs s
        (fn prems => [cut_facts_tac prems 1,
                      fast_tac (ZF_cs addSEs free_SEs @ Su.free_SEs) 1]);

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
  (thy1 |> Theory.add_path big_rec_base_name
        |> (#1 o PureThy.add_thmss
         [(("simps", simps), [Simplifier.simp_add_global]),
          (("", intrs), [Classical.safe_intro_global]),
          (("con_defs", con_defs), []),
          (("case_eqns", case_eqns), []),
          (("recursor_eqns", recursor_eqns), []),
          (("free_iffs", free_iffs), []),
          (("free_elims", free_SEs), [])])
        |> DatatypesData.map (fn tab => Symtab.update ((big_rec_name, dt_info), tab))
        |> ConstructorsData.map (fn tab => foldr Symtab.update (con_pairs, tab))
        |> Theory.parent_path,
   ind_result,
   {con_defs = con_defs,
    case_eqns = case_eqns,
    recursor_eqns = recursor_eqns,
    free_iffs = free_iffs,
    free_SEs = free_SEs,
    mk_free = mk_free})
  end;


fun add_datatype_x (sdom, srec_tms) scon_ty_lists (monos, type_intrs, type_elims) thy =
  let
    val sign = sign_of thy;
    val read_i = Sign.simple_read_term sign Ind_Syntax.iT;
    val rec_tms = map read_i srec_tms;
    val con_ty_lists = Ind_Syntax.read_constructs sign scon_ty_lists
    val dom_sum =
      if sdom = "" then Ind_Syntax.data_domain coind (rec_tms, con_ty_lists)
      else read_i sdom;
  in add_datatype_i (dom_sum, rec_tms) con_ty_lists (monos, type_intrs, type_elims) thy end;

fun add_datatype (sdom, srec_tms) scon_ty_lists (raw_monos, raw_type_intrs, raw_type_elims) thy =
  let
    val (thy', ((monos, type_intrs), type_elims)) = thy
      |> IsarThy.apply_theorems raw_monos
      |>>> IsarThy.apply_theorems raw_type_intrs
      |>>> IsarThy.apply_theorems raw_type_elims;
  in add_datatype_x (sdom, srec_tms) scon_ty_lists (monos, type_intrs, type_elims) thy' end;


(* outer syntax *)

local structure P = OuterParse and K = OuterSyntax.Keyword in

fun mk_datatype ((((dom, dts), monos), type_intrs), type_elims) =
  #1 o add_datatype (dom, map fst dts) (map snd dts) (monos, type_intrs, type_elims);

val con_decl =
  P.name -- Scan.optional (P.$$$ "(" |-- P.list1 P.term --| P.$$$ ")") [] -- P.opt_mixfix
  --| P.marg_comment >> P.triple1;

val datatype_decl =
  (Scan.optional ((P.$$$ "\\<subseteq>" || P.$$$ "<=") |-- P.!!! P.term --| P.marg_comment) "") --
  P.and_list1 (P.term -- (P.$$$ "=" |-- P.enum1 "|" con_decl)) --
  Scan.optional (P.$$$ "monos" |-- P.!!! P.xthms1 --| P.marg_comment) [] --
  Scan.optional (P.$$$ "type_intros" |-- P.!!! P.xthms1 --| P.marg_comment) [] --
  Scan.optional (P.$$$ "type_elims" |-- P.!!! P.xthms1 --| P.marg_comment) []
  >> (Toplevel.theory o mk_datatype);

val coind_prefix = if coind then "co" else "";

val inductiveP = OuterSyntax.command (coind_prefix ^ "datatype")
  ("define " ^ coind_prefix ^ "datatype") K.thy_decl datatype_decl;

val _ = OuterSyntax.add_parsers [inductiveP];

end;

end;
