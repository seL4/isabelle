(*  Title:      HOLCF/Tools/Domain/domain_theorems.ML
    Author:     David von Oheimb
    Author:     Brian Huffman

Proof generator for domain command.
*)

val HOLCF_ss = @{simpset};

signature DOMAIN_THEOREMS =
sig
  val theorems:
      Domain_Library.eq * Domain_Library.eq list ->
      binding ->
      (binding * (bool * binding option * typ) list * mixfix) list ->
      Domain_Take_Proofs.iso_info ->
      Domain_Take_Proofs.take_induct_info ->
      theory -> thm list * theory;

  val comp_theorems :
      binding * Domain_Library.eq list ->
      Domain_Take_Proofs.take_induct_info ->
      theory -> thm list * theory

  val quiet_mode: bool Unsynchronized.ref;
  val trace_domain: bool Unsynchronized.ref;
end;

structure Domain_Theorems :> DOMAIN_THEOREMS =
struct

val quiet_mode = Unsynchronized.ref false;
val trace_domain = Unsynchronized.ref false;

fun message s = if !quiet_mode then () else writeln s;
fun trace s = if !trace_domain then tracing s else ();

open Domain_Library;
infixr 0 ===>;
infixr 0 ==>;
infix 0 == ; 
infix 1 ===;
infix 1 ~= ;
infix 1 <<;
infix 1 ~<<;
infix 9 `   ;
infix 9 `% ;
infix 9 `%%;
infixr 9 oo;

(* ----- general proof facilities ------------------------------------------- *)

local

fun map_typ f g (Type (c, Ts)) = Type (g c, map (map_typ f g) Ts)
  | map_typ f _ (TFree (x, S)) = TFree (x, map f S)
  | map_typ f _ (TVar (xi, S)) = TVar (xi, map f S);

fun map_term f g h (Const (c, T)) = Const (h c, map_typ f g T)
  | map_term f g _ (Free (x, T)) = Free (x, map_typ f g T)
  | map_term f g _ (Var (xi, T)) = Var (xi, map_typ f g T)
  | map_term _ _ _ (t as Bound _) = t
  | map_term f g h (Abs (x, T, t)) = Abs (x, map_typ f g T, map_term f g h t)
  | map_term f g h (t $ u) = map_term f g h t $ map_term f g h u;

in

fun intern_term thy =
  map_term (Sign.intern_class thy) (Sign.intern_type thy) (Sign.intern_const thy);

end;

fun legacy_infer_term thy t =
  let val ctxt = ProofContext.set_mode ProofContext.mode_schematic (ProofContext.init_global thy)
  in singleton (Syntax.check_terms ctxt) (intern_term thy t) end;

fun pg'' thy defs t tacs =
  let
    val t' = legacy_infer_term thy t;
    val asms = Logic.strip_imp_prems t';
    val prop = Logic.strip_imp_concl t';
    fun tac {prems, context} =
      rewrite_goals_tac defs THEN
      EVERY (tacs {prems = map (rewrite_rule defs) prems, context = context})
  in Goal.prove_global thy [] asms prop tac end;

fun pg' thy defs t tacsf =
  let
    fun tacs {prems, context} =
      if null prems then tacsf context
      else cut_facts_tac prems 1 :: tacsf context;
  in pg'' thy defs t tacs end;

(* FIXME!!!!!!!!! *)
(* We should NEVER re-parse variable names as strings! *)
(* The names can conflict with existing constants or other syntax! *)
fun case_UU_tac ctxt rews i v =
  InductTacs.case_tac ctxt (v^"=UU") i THEN
  asm_simp_tac (HOLCF_ss addsimps rews) i;

(* ----- general proofs ----------------------------------------------------- *)

val all2E = @{lemma "!x y . P x y ==> (P x y ==> R) ==> R" by simp}

fun theorems
    (((dname, _), cons) : eq, eqs : eq list)
    (dbind : binding)
    (spec : (binding * (bool * binding option * typ) list * mixfix) list)
    (iso_info : Domain_Take_Proofs.iso_info)
    (take_info : Domain_Take_Proofs.take_induct_info)
    (thy : theory) =
let

val _ = message ("Proving isomorphism properties of domain "^dname^" ...");
val map_tab = Domain_Take_Proofs.get_map_tab thy;


(* ----- getting the axioms and definitions --------------------------------- *)

val ax_abs_iso = #abs_inverse iso_info;
val ax_rep_iso = #rep_inverse iso_info;

val abs_const = #abs_const iso_info;
val rep_const = #rep_const iso_info;

local
  fun ga s dn = PureThy.get_thm thy (dn ^ "." ^ s);
in
  val ax_take_0      = ga "take_0" dname;
  val ax_take_strict = ga "take_strict" dname;
end; (* local *)

val {take_Suc_thms, deflation_take_thms, ...} = take_info;

(* ----- define constructors ------------------------------------------------ *)

val (result, thy) =
    Domain_Constructors.add_domain_constructors dbind spec iso_info thy;

val con_appls = #con_betas result;
val {nchotomy, exhaust, ...} = result;
val {compacts, con_rews, inverts, injects, dist_les, dist_eqs, ...} = result;
val {sel_rews, ...} = result;
val when_rews = #cases result;
val when_strict = hd when_rews;
val dis_rews = #dis_rews result;
val mat_rews = #match_rews result;

(* ----- theorems concerning the isomorphism -------------------------------- *)

val pg = pg' thy;

val retraction_strict = @{thm retraction_strict};
val abs_strict = ax_rep_iso RS (allI RS retraction_strict);
val rep_strict = ax_abs_iso RS (allI RS retraction_strict);
val iso_rews = [ax_abs_iso, ax_rep_iso, abs_strict, rep_strict];

(* ----- theorems concerning one induction step ----------------------------- *)

local
  fun dc_take dn = %%:(dn^"_take");
  val dnames = map (fst o fst) eqs;
  val deflation_thms = Domain_Take_Proofs.get_deflation_thms thy;

  fun copy_of_dtyp tab r dt =
      if Datatype_Aux.is_rec_type dt then copy tab r dt else ID
  and copy tab r (Datatype_Aux.DtRec i) = r i
    | copy tab r (Datatype_Aux.DtTFree a) = ID
    | copy tab r (Datatype_Aux.DtType (c, ds)) =
      case Symtab.lookup tab c of
        SOME f => list_ccomb (%%:f, map (copy_of_dtyp tab r) ds)
      | NONE => (warning ("copy_of_dtyp: unknown type constructor " ^ c); ID);

  fun one_take_app (con, args) =
    let
      fun mk_take n = dc_take (List.nth (dnames, n)) $ %:"n";
      fun one_rhs arg =
          if Datatype_Aux.is_rec_type (dtyp_of arg)
          then copy_of_dtyp map_tab
                 mk_take (dtyp_of arg) ` (%# arg)
          else (%# arg);
      val lhs = (dc_take dname $ (%%: @{const_name Suc} $ %:"n")) ` (con_app con args);
      val rhs = con_app2 con one_rhs args;
      val goal = mk_trp (lhs === rhs);
      val rules =
          [ax_abs_iso] @ @{thms take_con_rules}
          @ take_Suc_thms @ deflation_thms @ deflation_take_thms;
      val tacs = [simp_tac (HOL_basic_ss addsimps rules) 1];
    in pg con_appls goal (K tacs) end;
  val take_apps = map one_take_app cons;
in
  val take_rews = ax_take_0 :: ax_take_strict :: take_apps;
end;

val case_ns =
    "bottom" :: map (fn (b,_,_) => Binding.name_of b) spec;

fun qualified name = Binding.qualified true name dbind;
val simp = Simplifier.simp_add;

in
  thy
  |> PureThy.add_thmss [
     ((qualified "iso_rews"  , iso_rews    ), [simp]),
     ((qualified "nchotomy"  , [nchotomy]  ), []),
     ((qualified "exhaust"   , [exhaust]   ),
      [Rule_Cases.case_names case_ns, Induct.cases_type dname]),
     ((qualified "when_rews" , when_rews   ), [simp]),
     ((qualified "compacts"  , compacts    ), [simp]),
     ((qualified "con_rews"  , con_rews    ), [simp]),
     ((qualified "sel_rews"  , sel_rews    ), [simp]),
     ((qualified "dis_rews"  , dis_rews    ), [simp]),
     ((qualified "dist_les"  , dist_les    ), [simp]),
     ((qualified "dist_eqs"  , dist_eqs    ), [simp]),
     ((qualified "inverts"   , inverts     ), [simp]),
     ((qualified "injects"   , injects     ), [simp]),
     ((qualified "take_rews" , take_rews   ), [simp]),
     ((qualified "match_rews", mat_rews    ), [simp])]
  |> snd
  |> pair (iso_rews @ when_rews @ con_rews @ sel_rews @ dis_rews @
      dist_les @ dist_eqs)
end; (* let *)

(******************************************************************************)
(****************************** induction rules *******************************)
(******************************************************************************)

fun prove_induction
    (comp_dbind : binding, eqs : eq list)
    (take_rews : thm list)
    (take_info : Domain_Take_Proofs.take_induct_info)
    (thy : theory) =
let
  val comp_dname = Sign.full_name thy comp_dbind;
  val dnames = map (fst o fst) eqs;
  val conss  = map  snd        eqs;
  fun dc_take dn = %%:(dn^"_take");
  val x_name = idx_name dnames "x";
  val P_name = idx_name dnames "P";
  val pg = pg' thy;

  local
    fun ga s dn = PureThy.get_thm thy (dn ^ "." ^ s);
    fun gts s dn = PureThy.get_thms thy (dn ^ "." ^ s);
  in
    val axs_rep_iso = map (ga "rep_iso") dnames;
    val axs_abs_iso = map (ga "abs_iso") dnames;
    val exhausts = map (ga  "exhaust" ) dnames;
    val con_rews  = maps (gts "con_rews" ) dnames;
  end;

  val {take_consts, ...} = take_info;
  val {take_0_thms, take_Suc_thms, chain_take_thms, ...} = take_info;
  val {lub_take_thms, finite_defs, reach_thms, ...} = take_info;
  val {take_induct_thms, ...} = take_info;

  fun one_con p (con, args) =
    let
      val P_names = map P_name (1 upto (length dnames));
      val vns = Name.variant_list P_names (map vname args);
      val nonlazy_vns = map snd (filter_out (is_lazy o fst) (args ~~ vns));
      fun ind_hyp arg = %:(P_name (1 + rec_of arg)) $ bound_arg args arg;
      val t1 = mk_trp (%:p $ con_app2 con (bound_arg args) args);
      val t2 = lift ind_hyp (filter is_rec args, t1);
      val t3 = lift_defined (bound_arg vns) (nonlazy_vns, t2);
    in Library.foldr mk_All (vns, t3) end;

  fun one_eq ((p, cons), concl) =
    mk_trp (%:p $ UU) ===> Logic.list_implies (map (one_con p) cons, concl);

  fun ind_term concf = Library.foldr one_eq
    (mapn (fn n => fn x => (P_name n, x)) 1 conss,
     mk_trp (foldr1 mk_conj (mapn concf 1 dnames)));
  val take_ss = HOL_ss addsimps (@{thm Rep_CFun_strict1} :: take_rews);
  fun quant_tac ctxt i = EVERY
    (mapn (fn n => fn _ => res_inst_tac ctxt [(("x", 0), x_name n)] spec i) 1 dnames);

  fun ind_prems_tac prems = EVERY
    (maps (fn cons =>
      (resolve_tac prems 1 ::
        maps (fn (_,args) => 
          resolve_tac prems 1 ::
          map (K(atac 1)) (nonlazy args) @
          map (K(atac 1)) (filter is_rec args))
        cons))
      conss);
  local
    fun rec_to ns lazy_rec (n,cons) = forall (exists (fn arg => 
          is_rec arg andalso not (member (op =) ns (rec_of arg)) andalso
          ((rec_of arg =  n andalso not (lazy_rec orelse is_lazy arg)) orelse 
            rec_of arg <> n andalso rec_to (rec_of arg::ns) 
              (lazy_rec orelse is_lazy arg) (n, (List.nth(conss,rec_of arg))))
          ) o snd) cons;
    fun warn (n,cons) =
      if rec_to [] false (n,cons)
      then (warning ("domain "^List.nth(dnames,n)^" is empty!"); true)
      else false;

  in
    val n__eqs = mapn (fn n => fn (_,cons) => (n,cons)) 0 eqs;
    val is_emptys = map warn n__eqs;
    val is_finite = #is_finite take_info;
    val _ = if is_finite
            then message ("Proving finiteness rule for domain "^comp_dname^" ...")
            else ();
  end;
  val _ = trace " Proving finite_ind...";
  val finite_ind =
    let
      fun concf n dn = %:(P_name n) $ (dc_take dn $ %:"n" `%(x_name n));
      val goal = ind_term concf;

      fun tacf {prems, context} =
        let
          val tacs1 = [
            quant_tac context 1,
            simp_tac HOL_ss 1,
            InductTacs.induct_tac context [[SOME "n"]] 1,
            simp_tac (take_ss addsimps prems) 1,
            TRY (safe_tac HOL_cs)];
          fun arg_tac arg =
                        (* FIXME! case_UU_tac *)
            case_UU_tac context (prems @ con_rews) 1
              (List.nth (dnames, rec_of arg) ^ "_take n$" ^ vname arg);
          fun con_tacs (con, args) = 
            asm_simp_tac take_ss 1 ::
            map arg_tac (filter is_nonlazy_rec args) @
            [resolve_tac prems 1] @
            map (K (atac 1)) (nonlazy args) @
            map (K (etac spec 1)) (filter is_rec args);
          fun cases_tacs (cons, exhaust) =
            res_inst_tac context [(("y", 0), "x")] exhaust 1 ::
            asm_simp_tac (take_ss addsimps prems) 1 ::
            maps con_tacs cons;
        in
          tacs1 @ maps cases_tacs (conss ~~ exhausts)
        end;
    in pg'' thy [] goal tacf end;

(* ----- theorems concerning finiteness and induction ----------------------- *)

  val global_ctxt = ProofContext.init_global thy;

  val _ = trace " Proving ind...";
  val ind =
    if is_finite
    then (* finite case *)
      let
        fun concf n dn = %:(P_name n) $ %:(x_name n);
        fun tacf {prems, context} =
          let
            fun finite_tacs (take_induct, fin_ind) = [
                rtac take_induct 1,
                rtac fin_ind 1,
                ind_prems_tac prems];
          in
            TRY (safe_tac HOL_cs) ::
            maps finite_tacs (take_induct_thms ~~ atomize global_ctxt finite_ind)
          end;
      in pg'' thy [] (ind_term concf) tacf end

    else (* infinite case *)
      let
        val goal =
          let
            fun one_adm n _ = mk_trp (mk_adm (%:(P_name n)));
            fun concf n dn = %:(P_name n) $ %:(x_name n);
          in Logic.list_implies (mapn one_adm 1 dnames, ind_term concf) end;
        val cont_rules =
            @{thms cont_id cont_const cont2cont_Rep_CFun
                   cont2cont_fst cont2cont_snd};
        val subgoal =
          let
            val Ts = map (Type o fst) eqs;
            val P_names = Datatype_Prop.indexify_names (map (K "P") dnames);
            val x_names = Datatype_Prop.indexify_names (map (K "x") dnames);
            val P_types = map (fn T => T --> HOLogic.boolT) Ts;
            val Ps = map Free (P_names ~~ P_types);
            val xs = map Free (x_names ~~ Ts);
            val n = Free ("n", HOLogic.natT);
            val goals =
                map (fn ((P,t),x) => P $ HOLCF_Library.mk_capply (t $ n, x))
                  (Ps ~~ take_consts ~~ xs);
          in
            HOLogic.mk_Trueprop
            (HOLogic.mk_all ("n", HOLogic.natT, foldr1 HOLogic.mk_conj goals))
          end;
        fun tacf {prems, context} =
          let
            val subtac =
                EVERY [rtac allI 1, rtac finite_ind 1, ind_prems_tac prems];
            val subthm = Goal.prove context [] [] subgoal (K subtac);
          in
            map (fn ax_reach => rtac (ax_reach RS subst) 1) reach_thms @ [
            cut_facts_tac (subthm :: take (length dnames) prems) 1,
            REPEAT (rtac @{thm conjI} 1 ORELSE
                    EVERY [etac @{thm admD [OF _ ch2ch_Rep_CFunL]} 1,
                           resolve_tac chain_take_thms 1,
                           asm_simp_tac HOL_basic_ss 1])
            ]
          end;
      in pg'' thy [] goal tacf end;

val case_ns =
  let
    val adms =
        if is_finite then [] else
        if length dnames = 1 then ["adm"] else
        map (fn s => "adm_" ^ Long_Name.base_name s) dnames;
    val bottoms =
        if length dnames = 1 then ["bottom"] else
        map (fn s => "bottom_" ^ Long_Name.base_name s) dnames;
    fun one_eq bot (_,cons) =
          bot :: map (fn (c,_) => Long_Name.base_name c) cons;
  in adms @ flat (map2 one_eq bottoms eqs) end;

val inducts = Project_Rule.projections (ProofContext.init_global thy) ind;
fun ind_rule (dname, rule) =
    ((Binding.empty, [rule]),
     [Rule_Cases.case_names case_ns, Induct.induct_type dname]);

in
  thy
  |> snd o PureThy.add_thmss [
     ((Binding.qualified true "finite_induct" comp_dbind, [finite_ind]), []),
     ((Binding.qualified true "induct"        comp_dbind, [ind]       ), [])]
  |> (snd o PureThy.add_thmss (map ind_rule (dnames ~~ inducts)))
end; (* prove_induction *)

(******************************************************************************)
(************************ bisimulation and coinduction ************************)
(******************************************************************************)

fun prove_coinduction
    (comp_dbind : binding, eqs : eq list)
    (take_lemmas : thm list)
    (thy : theory) : theory =
let

val dnames = map (fst o fst) eqs;
val comp_dname = Sign.full_name thy comp_dbind;
fun dc_take dn = %%:(dn^"_take");
val x_name = idx_name dnames "x"; 
val n_eqs = length eqs;

val take_rews =
    maps (fn dn => PureThy.get_thms thy (dn ^ ".take_rews")) dnames;

(* ----- define bisimulation predicate -------------------------------------- *)

local
  open HOLCF_Library
  val dtypes  = map (Type o fst) eqs;
  val relprod = mk_tupleT (map (fn tp => tp --> tp --> boolT) dtypes);
  val bisim_bind = Binding.suffix_name "_bisim" comp_dbind;
  val bisim_type = relprod --> boolT;
in
  val (bisim_const, thy) =
      Sign.declare_const ((bisim_bind, bisim_type), NoSyn) thy;
end;

local

  fun legacy_infer_term thy t =
      singleton (Syntax.check_terms (ProofContext.init_global thy)) (intern_term thy t);
  fun legacy_infer_prop thy t = legacy_infer_term thy (Type.constraint propT t);
  fun infer_props thy = map (apsnd (legacy_infer_prop thy));
  fun add_defs_i x = PureThy.add_defs false (map Thm.no_attributes x);
  fun add_defs_infer defs thy = add_defs_i (infer_props thy defs) thy;

  fun one_con (con, args) =
    let
      val nonrec_args = filter_out is_rec args;
      val    rec_args = filter is_rec args;
      val    recs_cnt = length rec_args;
      val allargs     = nonrec_args @ rec_args
                        @ map (upd_vname (fn s=> s^"'")) rec_args;
      val allvns      = map vname allargs;
      fun vname_arg s arg = if is_rec arg then vname arg^s else vname arg;
      val vns1        = map (vname_arg "" ) args;
      val vns2        = map (vname_arg "'") args;
      val allargs_cnt = length nonrec_args + 2*recs_cnt;
      val rec_idxs    = (recs_cnt-1) downto 0;
      val nonlazy_idxs = map snd (filter_out (fn (arg,_) => is_lazy arg)
                                             (allargs~~((allargs_cnt-1) downto 0)));
      fun rel_app i ra = proj (Bound(allargs_cnt+2)) eqs (rec_of ra) $ 
                              Bound (2*recs_cnt-i) $ Bound (recs_cnt-i);
      val capps =
          List.foldr
            mk_conj
            (mk_conj(
             Bound(allargs_cnt+1)===list_ccomb(%%:con,map (bound_arg allvns) vns1),
             Bound(allargs_cnt+0)===list_ccomb(%%:con,map (bound_arg allvns) vns2)))
            (mapn rel_app 1 rec_args);
    in
      List.foldr
        mk_ex
        (Library.foldr mk_conj
                       (map (defined o Bound) nonlazy_idxs,capps)) allvns
    end;
  fun one_comp n (_,cons) =
      mk_all (x_name(n+1),
      mk_all (x_name(n+1)^"'",
      mk_imp (proj (Bound 2) eqs n $ Bound 1 $ Bound 0,
      foldr1 mk_disj (mk_conj(Bound 1 === UU,Bound 0 === UU)
                      ::map one_con cons))));
  val bisim_eqn =
      %%:(comp_dname^"_bisim") ==
         mk_lam("R", foldr1 mk_conj (mapn one_comp 0 eqs));

in
  val (ax_bisim_def, thy) =
      yield_singleton add_defs_infer
        (Binding.qualified true "bisim_def" comp_dbind, bisim_eqn) thy;
end; (* local *)

(* ----- theorem concerning coinduction ------------------------------------- *)

local
  val pg = pg' thy;
  val xs = mapn (fn n => K (x_name n)) 1 dnames;
  fun bnd_arg n i = Bound(2*(n_eqs - n)-i-1);
  val take_ss = HOL_ss addsimps (@{thm Rep_CFun_strict1} :: take_rews);
  val sproj = prj (fn s => K("fst("^s^")")) (fn s => K("snd("^s^")"));
  val _ = trace " Proving coind_lemma...";
  val coind_lemma =
    let
      fun mk_prj n _ = proj (%:"R") eqs n $ bnd_arg n 0 $ bnd_arg n 1;
      fun mk_eqn n dn =
        (dc_take dn $ %:"n" ` bnd_arg n 0) ===
        (dc_take dn $ %:"n" ` bnd_arg n 1);
      fun mk_all2 (x,t) = mk_all (x, mk_all (x^"'", t));
      val goal =
        mk_trp (mk_imp (%%:(comp_dname^"_bisim") $ %:"R",
          Library.foldr mk_all2 (xs,
            Library.foldr mk_imp (mapn mk_prj 0 dnames,
              foldr1 mk_conj (mapn mk_eqn 0 dnames)))));
      fun x_tacs ctxt n x = [
        rotate_tac (n+1) 1,
        etac all2E 1,
        eres_inst_tac ctxt [(("P", 1), sproj "R" eqs n^" "^x^" "^x^"'")] (mp RS disjE) 1,
        TRY (safe_tac HOL_cs),
        REPEAT (CHANGED (asm_simp_tac take_ss 1))];
      fun tacs ctxt = [
        rtac impI 1,
        InductTacs.induct_tac ctxt [[SOME "n"]] 1,
        simp_tac take_ss 1,
        safe_tac HOL_cs] @
        flat (mapn (x_tacs ctxt) 0 xs);
    in pg [ax_bisim_def] goal tacs end;
in
  val _ = trace " Proving coind...";
  val coind = 
    let
      fun mk_prj n x = mk_trp (proj (%:"R") eqs n $ %:x $ %:(x^"'"));
      fun mk_eqn x = %:x === %:(x^"'");
      val goal =
        mk_trp (%%:(comp_dname^"_bisim") $ %:"R") ===>
          Logic.list_implies (mapn mk_prj 0 xs,
            mk_trp (foldr1 mk_conj (map mk_eqn xs)));
      val tacs =
        TRY (safe_tac HOL_cs) ::
        maps (fn take_lemma => [
          rtac take_lemma 1,
          cut_facts_tac [coind_lemma] 1,
          fast_tac HOL_cs 1])
        take_lemmas;
    in pg [] goal (K tacs) end;
end; (* local *)

in thy |> snd o PureThy.add_thmss
    [((Binding.qualified true "coinduct" comp_dbind, [coind]), [])]
end; (* let *)

fun comp_theorems
    (comp_dbind : binding, eqs : eq list)
    (take_info : Domain_Take_Proofs.take_induct_info)
    (thy : theory) =
let
val map_tab = Domain_Take_Proofs.get_map_tab thy;

val dnames = map (fst o fst) eqs;
val comp_dname = Sign.full_name thy comp_dbind;

(* ----- getting the composite axiom and definitions ------------------------ *)

(* Test for indirect recursion *)
local
  fun indirect_arg arg =
      rec_of arg = ~1 andalso Datatype_Aux.is_rec_type (dtyp_of arg);
  fun indirect_con (_, args) = exists indirect_arg args;
  fun indirect_eq (_, cons) = exists indirect_con cons;
in
  val is_indirect = exists indirect_eq eqs;
  val _ =
      if is_indirect
      then message "Indirect recursion detected, skipping proofs of (co)induction rules"
      else message ("Proving induction properties of domain "^comp_dname^" ...");
end;

(* theorems about take *)

val take_lemmas = #take_lemma_thms take_info;

val take_rews =
    maps (fn dn => PureThy.get_thms thy (dn ^ ".take_rews")) dnames;

(* prove induction rules, unless definition is indirect recursive *)
val thy =
    if is_indirect then thy else
    prove_induction (comp_dbind, eqs) take_rews take_info thy;

val thy =
    if is_indirect then thy else
    prove_coinduction (comp_dbind, eqs) take_lemmas thy;

in
  (take_rews, thy)
end; (* let *)
end; (* struct *)
