(*  Title:      HOL/Tools/Predicate_Compile/predicate_compile_pred.ML
    Author:     Lukas Bulwahn, TU Muenchen

Preprocessing definitions of predicates to introduction rules.
*)

signature PREDICATE_COMPILE_PRED =
sig
  (* preprocesses an equation to a set of intro rules; defines new constants *)
  val preprocess : Predicate_Compile_Aux.options -> (string * thm list) -> theory
    -> ((string * thm list) list * theory) 
  val flat_higher_order_arguments : ((string * thm list) list * theory)
    -> ((string * thm list) list * ((string * thm list) list * theory))
end;


structure Predicate_Compile_Pred : PREDICATE_COMPILE_PRED =
struct

open Predicate_Compile_Aux


fun datatype_names_of_case_name thy case_name =
  map (#1 o #2) (#descr (the (Datatype_Data.info_of_case thy case_name)))

fun make_case_distribs new_type_names descr sorts thy =
  let
    val case_combs = Datatype_Prop.make_case_combs new_type_names descr sorts thy "f";
    fun make comb =
      let
        val Type ("fun", [T, T']) = fastype_of comb;
        val (Const (case_name, _), fs) = strip_comb comb
        val used = Term.add_tfree_names comb []
        val U = TFree (Name.variant used "'t", HOLogic.typeS)
        val x = Free ("x", T)
        val f = Free ("f", T' --> U)
        fun apply_f f' =
          let
            val Ts = binder_types (fastype_of f')
            val bs = map Bound ((length Ts - 1) downto 0)
          in
            fold (curry absdummy) (rev Ts) (f $ (list_comb (f', bs)))
          end
        val fs' = map apply_f fs
        val case_c' = Const (case_name, (map fastype_of fs') @ [T] ---> U)
      in
        HOLogic.mk_eq (f $ (comb $ x), list_comb (case_c', fs') $ x)
      end
  in
    map make case_combs
  end

fun case_rewrites thy Tcon =
  let
    val info = Datatype.the_info thy Tcon
    val descr = #descr info
    val sorts = #sorts info
    val typ_names = the_default [Tcon] (#alt_names info)
  in
    map (Drule.export_without_context o Skip_Proof.make_thm thy o HOLogic.mk_Trueprop)
      (make_case_distribs typ_names [descr] sorts thy)
  end

fun instantiated_case_rewrites thy Tcon =
  let
    val rew_ths = case_rewrites thy Tcon
    val ctxt = ProofContext.init_global thy
    fun instantiate th =
    let
      val f = (fst (strip_comb (fst (HOLogic.dest_eq (HOLogic.dest_Trueprop (prop_of th))))))
      val Type ("fun", [uninst_T, uninst_T']) = fastype_of f
      val ([tname, tname', uname, yname], ctxt') = Variable.add_fixes ["'t", "'t'", "'u", "y"] ctxt
      val T = TFree (tname, HOLogic.typeS)
      val T' = TFree (tname', HOLogic.typeS)
      val U = TFree (uname, HOLogic.typeS)
      val y = Free (yname, U)
      val f' = absdummy (U --> T', Bound 0 $ y)
      val th' = Thm.certify_instantiate
        ([(dest_TVar uninst_T, U --> T'), (dest_TVar uninst_T', T')],
         [((fst (dest_Var f), (U --> T') --> T'), f')]) th
      val [th'] = Variable.export ctxt' ctxt [th']
   in
     th'
   end
 in
   map instantiate rew_ths
 end

fun is_compound ((Const (@{const_name Not}, _)) $ t) =
    error "is_compound: Negation should not occur; preprocessing is defect"
  | is_compound ((Const (@{const_name Ex}, _)) $ _) = true
  | is_compound ((Const (@{const_name HOL.disj}, _)) $ _ $ _) = true
  | is_compound ((Const (@{const_name HOL.conj}, _)) $ _ $ _) =
    error "is_compound: Conjunction should not occur; preprocessing is defect"
  | is_compound _ = false

fun flatten constname atom (defs, thy) =
  if is_compound atom then
    let
      val atom = Envir.beta_norm (Pattern.eta_long [] atom)
      val constname = Name.variant (map (Long_Name.base_name o fst) defs)
        ((Long_Name.base_name constname) ^ "_aux")
      val full_constname = Sign.full_bname thy constname
      val (params, args) = List.partition (is_predT o fastype_of)
        (map Free (Term.add_frees atom []))
      val constT = map fastype_of (params @ args) ---> HOLogic.boolT
      val lhs = list_comb (Const (full_constname, constT), params @ args)
      val def = Logic.mk_equals (lhs, atom)
      val ([definition], thy') = thy
        |> Sign.add_consts_i [(Binding.name constname, constT, NoSyn)]
        |> PureThy.add_defs false [((Binding.name (constname ^ "_def"), def), [])]
    in
      (lhs, ((full_constname, [definition]) :: defs, thy'))
    end
  else
    case (fst (strip_comb atom)) of
      (Const (@{const_name If}, _)) =>
        let
          val if_beta = @{lemma "(if c then x else y) z = (if c then x z else y z)" by simp}
          val atom' = MetaSimplifier.rewrite_term thy
            (map (fn th => th RS @{thm eq_reflection}) [@{thm if_bool_eq_disj}, if_beta]) [] atom
          val _ = assert (not (atom = atom'))
        in
          flatten constname atom' (defs, thy)
        end
    | _ =>
      case find_split_thm thy (fst (strip_comb atom)) of
        NONE => (atom, (defs, thy))
      | SOME raw_split_thm =>
        let
          val (f, args) = strip_comb atom
          val split_thm = prepare_split_thm (ProofContext.init_global thy) raw_split_thm
          (* TODO: contextify things - this line is to unvarify the split_thm *)
          (*val ((_, [isplit_thm]), _) =
            Variable.import true [split_thm] (ProofContext.init_global thy)*)
          val (assms, concl) = Logic.strip_horn (prop_of split_thm)
          val (P, [split_t]) = strip_comb (HOLogic.dest_Trueprop concl) 
          val Tcons = datatype_names_of_case_name thy (fst (dest_Const f))
          val ths = maps (instantiated_case_rewrites thy) Tcons
          val atom = MetaSimplifier.rewrite_term thy
            (map (fn th => th RS @{thm eq_reflection}) ths) [] atom
          val (f, args) = strip_comb atom
          val subst = Pattern.match thy (split_t, atom) (Vartab.empty, Vartab.empty)
          val (_, split_args) = strip_comb split_t
          val match = split_args ~~ args
          val names = Term.add_free_names atom []
          val frees = map Free (Term.add_frees atom [])
          val constname = Name.variant (map (Long_Name.base_name o fst) defs)
            ((Long_Name.base_name constname) ^ "_aux")
          val full_constname = Sign.full_bname thy constname
          val constT = map fastype_of frees ---> HOLogic.boolT
          val lhs = list_comb (Const (full_constname, constT), frees)
          fun new_def assm =
            let
              val (vTs, assm') = strip_all (Envir.beta_norm (Envir.subst_term subst assm))
              val var_names = Name.variant_list names (map fst vTs)
              val vars = map Free (var_names ~~ (map snd vTs))
              val (prems', pre_res) = Logic.strip_horn (subst_bounds (rev vars, assm'))
              fun partition_prem_subst prem =
                case HOLogic.dest_eq (HOLogic.dest_Trueprop prem) of
                  (Free (x, T), r) => (NONE, SOME ((x, T), r))
                | _ => (SOME prem, NONE)
              fun partition f xs =
                let
                  fun partition' acc1 acc2 [] = (rev acc1, rev acc2)
                    | partition' acc1 acc2 (x :: xs) =
                      let
                        val (y, z) = f x
                        val acc1' = case y of NONE => acc1 | SOME y' => y' :: acc1
                        val acc2' = case z of NONE => acc2 | SOME z' => z' :: acc2
                      in partition' acc1' acc2' xs end
                in partition' [] [] xs end
              val (prems'', subst) = partition partition_prem_subst prems'
              val (_, [inner_t]) = strip_comb (HOLogic.dest_Trueprop pre_res)
              val pre_def = Logic.mk_equals (lhs,
                fold (curry HOLogic.mk_conj) (map HOLogic.dest_Trueprop prems'') inner_t)
              val def = Envir.expand_term_frees subst pre_def
            in
              def
            end
         val new_defs = map new_def assms
         val (definition, thy') = thy
          |> Sign.add_consts_i [(Binding.name constname, constT, NoSyn)]
          |> fold_map Specification.axiom (map_index
              (fn (i, t) => ((Binding.name (constname ^ "_def" ^ string_of_int i), []), t)) new_defs)
        in
          (lhs, ((full_constname, map Drule.export_without_context definition) :: defs, thy'))
        end


fun flatten_intros constname intros thy =
  let
    val ctxt = ProofContext.init_global thy
    val ((_, intros), ctxt') = Variable.import true intros ctxt
    val (intros', (local_defs, thy')) = (fold_map o fold_map_atoms)
      (flatten constname) (map prop_of intros) ([], thy)
    val ctxt'' = ProofContext.transfer thy' ctxt'
    val tac = fn _ => Skip_Proof.cheat_tac thy'
    val intros'' = map (fn t => Goal.prove ctxt'' [] [] t tac) intros'
      |> Variable.export ctxt'' ctxt
  in
    (intros'', (local_defs, thy'))
  end

(* TODO: same function occurs in inductive package *)
fun select_disj 1 1 = []
  | select_disj _ 1 = [rtac @{thm disjI1}]
  | select_disj n i = (rtac @{thm disjI2})::(select_disj (n - 1) (i - 1));

fun introrulify thy ths = 
  let
    val ctxt = ProofContext.init_global thy
    val ((_, ths'), ctxt') = Variable.import true ths ctxt
    fun introrulify' th =
      let
        val (lhs, rhs) = Logic.dest_equals (prop_of th)
        val frees = Term.add_free_names rhs []
        val disjuncts = HOLogic.dest_disj rhs
        val nctxt = Name.make_context frees
        fun mk_introrule t =
          let
            val ((ps, t'), nctxt') = focus_ex t nctxt
            val prems = map HOLogic.mk_Trueprop (HOLogic.dest_conj t')
          in
            (ps, Logic.list_implies (prems, HOLogic.mk_Trueprop lhs))
          end
        val x = ((cterm_of thy) o the_single o snd o strip_comb o HOLogic.dest_Trueprop o fst o
          Logic.dest_implies o prop_of) @{thm exI}
        fun prove_introrule (index, (ps, introrule)) =
          let
            val tac = Simplifier.simp_tac (HOL_basic_ss addsimps [th]) 1
              THEN EVERY1 (select_disj (length disjuncts) (index + 1)) 
              THEN (EVERY (map (fn y =>
                rtac (Drule.cterm_instantiate [(x, cterm_of thy (Free y))] @{thm exI}) 1) ps))
              THEN REPEAT_DETERM (rtac @{thm conjI} 1 THEN atac 1)
              THEN TRY (atac 1)
          in
            Goal.prove ctxt' (map fst ps) [] introrule (fn _ => tac)
          end
      in
        map_index prove_introrule (map mk_introrule disjuncts)
      end
  in maps introrulify' ths' |> Variable.export ctxt' ctxt end

val rewrite =
  Simplifier.simplify (HOL_basic_ss addsimps [@{thm Ball_def}, @{thm Bex_def}])
  #> Simplifier.simplify (HOL_basic_ss addsimps [@{thm all_not_ex}])
  #> Conv.fconv_rule nnf_conv 
  #> Simplifier.simplify (HOL_basic_ss addsimps [@{thm ex_disj_distrib}])

fun split_conjs thy t =
  let 
    fun split_conjunctions (Const (@{const_name HOL.conj}, _) $ t1 $ t2) =
    (split_conjunctions t1) @ (split_conjunctions t2)
    | split_conjunctions t = [t]
  in
    map HOLogic.mk_Trueprop (split_conjunctions (HOLogic.dest_Trueprop t))
  end

fun rewrite_intros thy =
  Simplifier.full_simplify (HOL_basic_ss addsimps [@{thm all_not_ex}])
  #> Simplifier.full_simplify
    (HOL_basic_ss addsimps (tl @{thms bool_simps}) addsimps @{thms nnf_simps})
  #> map_term thy (maps_premises (split_conjs thy))

fun print_specs options thy msg ths =
  if show_intermediate_results options then
    (tracing (msg); tracing (commas (map (Display.string_of_thm_global thy) ths)))
  else
    ()
(*
fun split_cases thy th =
  let
    
  in
    map_term thy th
  end
*)
fun preprocess options (constname, specs) thy =
(*  case Predicate_Compile_Data.processed_specs thy constname of
    SOME specss => (specss, thy)
  | NONE =>*)
    let
      val ctxt = ProofContext.init_global thy
      val intros =
        if forall is_pred_equation specs then 
          map (map_term thy (maps_premises (split_conjs thy))) (introrulify thy (map rewrite specs))
        else if forall (is_intro constname) specs then
          map (rewrite_intros thy) specs
        else
          error ("unexpected specification for constant " ^ quote constname ^ ":\n"
            ^ commas (map (quote o Display.string_of_thm_global thy) specs))
      val if_beta = @{lemma "(if c then x else y) z = (if c then x z else y z)" by simp}
      val intros = map (MetaSimplifier.rewrite_rule
          [if_beta RS @{thm eq_reflection}]) intros
      val _ = print_specs options thy "normalized intros" intros
      (*val intros = maps (split_cases thy) intros*)
      val (intros', (local_defs, thy')) = flatten_intros constname intros thy
      val (intross, thy'') = fold_map (preprocess options) local_defs thy'
      val full_spec = (constname, intros') :: flat intross
      (*val thy''' = Predicate_Compile_Data.store_processed_specs (constname, full_spec) thy''*)
    in
      (full_spec, thy'')
    end;

fun preprocess_term t thy = error "preprocess_pred_term: to implement" 

fun is_Abs (Abs _) = true
  | is_Abs _       = false

fun flat_higher_order_arguments (intross, thy) =
  let
    fun process constname atom (new_defs, thy) =
      let
        val (pred, args) = strip_comb atom
        fun replace_abs_arg (abs_arg as Abs _ ) (new_defs, thy) =
          let
            val vars = map Var (Term.add_vars abs_arg [])
            val abs_arg' = Logic.unvarify_global abs_arg
            val frees = map Free (Term.add_frees abs_arg' [])
            val constname = Name.variant (map (Long_Name.base_name o fst) new_defs)
              ((Long_Name.base_name constname) ^ "_hoaux")
            val full_constname = Sign.full_bname thy constname
            val constT = map fastype_of frees ---> (fastype_of abs_arg')
            val const = Const (full_constname, constT)
            val lhs = list_comb (const, frees)
            val def = Logic.mk_equals (lhs, abs_arg')
            val ([definition], thy') = thy
              |> Sign.add_consts_i [(Binding.name constname, constT, NoSyn)]
              |> PureThy.add_defs false [((Binding.name (constname ^ "_def"), def), [])]
          in
            (list_comb (Logic.varify_global const, vars),
              ((full_constname, [definition])::new_defs, thy'))
          end
        | replace_abs_arg arg (new_defs, thy) =
          if is_some (try HOLogic.dest_prodT (fastype_of arg)) then
            (case try HOLogic.dest_prod arg of
              SOME (t1, t2) =>
                (new_defs, thy)
                |> process constname t1 
                ||>> process constname t2
                |>> HOLogic.mk_prod
            | NONE => (warning ("Replacing higher order arguments " ^
              "is not applied in an undestructable product type"); (arg, (new_defs, thy))))
          else if (is_predT (fastype_of arg)) then
            process constname arg (new_defs, thy)
          else
            (arg, (new_defs, thy))

        val (args', (new_defs', thy')) = fold_map replace_abs_arg
          (map Envir.beta_eta_contract args) (new_defs, thy)
      in
        (list_comb (pred, args'), (new_defs', thy'))
      end
    fun flat_intro intro (new_defs, thy) =
      let
        val constname = fst (dest_Const (fst (strip_comb
          (HOLogic.dest_Trueprop (Logic.strip_imp_concl (prop_of intro))))))
        val (intro_ts, (new_defs, thy)) = fold_map_atoms (process constname) (prop_of intro) (new_defs, thy)
        val th = Skip_Proof.make_thm thy intro_ts
      in
        (th, (new_defs, thy))
      end
    fun fold_map_spec f [] s = ([], s)
      | fold_map_spec f ((c, ths) :: specs) s =
        let
          val (ths', s') = f ths s
          val (specs', s'') = fold_map_spec f specs s'
        in ((c, ths') :: specs', s'') end
    val (intross', (new_defs, thy')) = fold_map_spec (fold_map flat_intro) intross ([], thy)
  in
    (intross', (new_defs, thy'))
  end

end;
