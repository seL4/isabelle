(*  Title:      HOLCF/Tools/Domain/domain_theorems.ML
    Author:     David von Oheimb
    Author:     Brian Huffman

Proof generator for domain command.
*)

val HOLCF_ss = @{simpset};

signature DOMAIN_THEOREMS =
sig
  val theorems:
    Domain_Library.eq * Domain_Library.eq list
    -> typ * (binding * (bool * binding option * typ) list * mixfix) list
    -> Domain_Take_Proofs.iso_info
    -> theory -> thm list * theory;

  val comp_theorems: bstring * Domain_Library.eq list -> theory -> thm list * theory;
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

fun legacy_infer_term thy t =
  let val ctxt = ProofContext.set_mode ProofContext.mode_schematic (ProofContext.init thy)
  in singleton (Syntax.check_terms ctxt) (Sign.intern_term thy t) end;

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
    (dom_eqn : typ * (binding * (bool * binding option * typ) list * mixfix) list)
    (iso_info : Domain_Take_Proofs.iso_info)
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
  val ax_take_Suc    = ga "take_Suc" dname;
  val ax_take_strict = ga "take_strict" dname;
end; (* local *)

(* ----- define constructors ------------------------------------------------ *)

val (result, thy) =
  Domain_Constructors.add_domain_constructors
    (Long_Name.base_name dname) (snd dom_eqn) iso_info thy;

val con_appls = #con_betas result;
val {exhaust, casedist, ...} = result;
val {con_compacts, con_rews, inverts, injects, dist_les, dist_eqs, ...} = result;
val {sel_rews, ...} = result;
val when_rews = #cases result;
val when_strict = hd when_rews;
val dis_rews = #dis_rews result;
val mat_rews = #match_rews result;
val pat_rews = #pat_rews result;

(* ----- theorems concerning the isomorphism -------------------------------- *)

val pg = pg' thy;

val retraction_strict = @{thm retraction_strict};
val abs_strict = ax_rep_iso RS (allI RS retraction_strict);
val rep_strict = ax_abs_iso RS (allI RS retraction_strict);
val iso_rews = map Drule.export_without_context [ax_abs_iso, ax_rep_iso, abs_strict, rep_strict];

(* ----- theorems concerning one induction step ----------------------------- *)

local
  fun dc_take dn = %%:(dn^"_take");
  val dnames = map (fst o fst) eqs;
  val deflation_thms = Domain_Take_Proofs.get_deflation_thms thy;
  fun get_deflation_take dn = PureThy.get_thm thy (dn ^ ".deflation_take");
  val axs_deflation_take = map get_deflation_take dnames;

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
      val lhs = (dc_take dname $ (%%:"Suc" $ %:"n"))`(con_app con args);
      val rhs = con_app2 con one_rhs args;
      val goal = mk_trp (lhs === rhs);
      val rules =
          [ax_take_Suc, ax_abs_iso, @{thm cfcomp2}]
          @ @{thms take_con_rules ID1 deflation_strict}
          @ deflation_thms @ axs_deflation_take;
      val tacs = [simp_tac (HOL_basic_ss addsimps rules) 1];
    in pg con_appls goal (K tacs) end;
  val take_apps = map one_take_app cons;
in
  val take_rews = ax_take_0 :: ax_take_strict :: take_apps;
end;

val case_ns =
    "bottom" :: map (fn (b,_,_) => Binding.name_of b) (snd dom_eqn);

in
  thy
    |> Sign.add_path (Long_Name.base_name dname)
    |> snd o PureThy.add_thmss [
        ((Binding.name "iso_rews"  , iso_rews    ), [Simplifier.simp_add]),
        ((Binding.name "exhaust"   , [exhaust]   ), []),
        ((Binding.name "casedist"  , [casedist]  ),
         [Rule_Cases.case_names case_ns, Induct.cases_type dname]),
        ((Binding.name "when_rews" , when_rews   ), [Simplifier.simp_add]),
        ((Binding.name "compacts"  , con_compacts), [Simplifier.simp_add]),
        ((Binding.name "con_rews"  , con_rews    ),
         [Simplifier.simp_add, Fixrec.fixrec_simp_add]),
        ((Binding.name "sel_rews"  , sel_rews    ), [Simplifier.simp_add]),
        ((Binding.name "dis_rews"  , dis_rews    ), [Simplifier.simp_add]),
        ((Binding.name "pat_rews"  , pat_rews    ), [Simplifier.simp_add]),
        ((Binding.name "dist_les"  , dist_les    ), [Simplifier.simp_add]),
        ((Binding.name "dist_eqs"  , dist_eqs    ), [Simplifier.simp_add]),
        ((Binding.name "inverts"   , inverts     ), [Simplifier.simp_add]),
        ((Binding.name "injects"   , injects     ), [Simplifier.simp_add]),
        ((Binding.name "take_rews" , take_rews   ), [Simplifier.simp_add]),
        ((Binding.name "match_rews", mat_rews    ),
         [Simplifier.simp_add, Fixrec.fixrec_simp_add])]
    |> Sign.parent_path
    |> pair (iso_rews @ when_rews @ con_rews @ sel_rews @ dis_rews @
        pat_rews @ dist_les @ dist_eqs)
end; (* let *)

(******************************************************************************)
(****************************** induction rules *******************************)
(******************************************************************************)

fun prove_induction
    (comp_dnam, eqs : eq list)
    (take_lemmas : thm list)
    (axs_reach : thm list)
    (take_rews : thm list)
    (thy : theory) =
let
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
    val axs_chain_take = map (ga "chain_take") dnames;
    val lub_take_thms = map (ga "lub_take") dnames;
    val axs_finite_def = map (ga "finite_def") dnames;
    val take_0_thms = map (ga "take_0") dnames;
    val take_Suc_thms = map (ga "take_Suc") dnames;
    val cases = map (ga  "casedist" ) dnames;
    val con_rews  = maps (gts "con_rews" ) dnames;
  end;

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
    (* check whether every/exists constructor of the n-th part of the equation:
       it has a possibly indirectly recursive argument that isn't/is possibly 
       indirectly lazy *)
    fun rec_to quant nfn rfn ns lazy_rec (n,cons) = quant (exists (fn arg => 
          is_rec arg andalso not(rec_of arg mem ns) andalso
          ((rec_of arg =  n andalso nfn(lazy_rec orelse is_lazy arg)) orelse 
            rec_of arg <> n andalso rec_to quant nfn rfn (rec_of arg::ns) 
              (lazy_rec orelse is_lazy arg) (n, (List.nth(conss,rec_of arg))))
          ) o snd) cons;
    fun all_rec_to ns  = rec_to forall not all_rec_to  ns;
    fun warn (n,cons) =
      if all_rec_to [] false (n,cons)
      then (warning ("domain "^List.nth(dnames,n)^" is empty!"); true)
      else false;
    fun lazy_rec_to ns = rec_to exists I  lazy_rec_to ns;

  in
    val n__eqs = mapn (fn n => fn (_,cons) => (n,cons)) 0 eqs;
    val is_emptys = map warn n__eqs;
    val is_finite = forall (not o lazy_rec_to [] false) n__eqs;
    val _ = if is_finite
            then message ("Proving finiteness rule for domain "^comp_dnam^" ...")
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
          fun cases_tacs (cons, cases) =
            res_inst_tac context [(("y", 0), "x")] cases 1 ::
            asm_simp_tac (take_ss addsimps prems) 1 ::
            maps con_tacs cons;
        in
          tacs1 @ maps cases_tacs (conss ~~ cases)
        end;
    in pg'' thy [] goal tacf
       handle ERROR _ => (warning "Proof of finite_ind failed."; TrueI)
    end;

(* ----- theorems concerning finiteness and induction ----------------------- *)

  val global_ctxt = ProofContext.init thy;

  val _ = trace " Proving finites, ind...";
  val (finites, ind) =
  (
    if is_finite
    then (* finite case *)
      let
        val decisive_lemma =
          let
            val iso_locale_thms =
                map2 (fn x => fn y => @{thm iso.intro} OF [x, y])
                axs_abs_iso axs_rep_iso;
            val decisive_abs_rep_thms =
                map (fn x => @{thm decisive_abs_rep} OF [x])
                iso_locale_thms;
            val n = Free ("n", @{typ nat});
            fun mk_decisive t = %%: @{const_name decisive} $ t;
            fun f dn = mk_decisive (dc_take dn $ n);
            val goal = mk_trp (foldr1 mk_conj (map f dnames));
            val rules0 = @{thm decisive_bottom} :: take_0_thms;
            val rules1 =
                take_Suc_thms @ decisive_abs_rep_thms
                @ @{thms decisive_ID decisive_ssum_map decisive_sprod_map};
            val tacs = [
                rtac @{thm nat.induct} 1,
                simp_tac (HOL_ss addsimps rules0) 1,
                asm_simp_tac (HOL_ss addsimps rules1) 1];
          in pg [] goal (K tacs) end;
        fun take_enough dn = mk_ex ("n",dc_take dn $ Bound 0 ` %:"x" === %:"x");
        fun one_finite (dn, decisive_thm) =
          let
            val goal = mk_trp (%%:(dn^"_finite") $ %:"x");
            val tacs = [
                rtac @{thm lub_ID_finite} 1,
                resolve_tac axs_chain_take 1,
                resolve_tac lub_take_thms 1,
                rtac decisive_thm 1];
          in pg axs_finite_def goal (K tacs) end;

        val _ = trace " Proving finites";
        val finites = map one_finite (dnames ~~ atomize global_ctxt decisive_lemma);
        val _ = trace " Proving ind";
        val ind =
          let
            fun concf n dn = %:(P_name n) $ %:(x_name n);
            fun tacf {prems, context} =
              let
                fun finite_tacs (finite, fin_ind) = [
                  rtac(rewrite_rule axs_finite_def finite RS exE)1,
                  etac subst 1,
                  rtac fin_ind 1,
                  ind_prems_tac prems];
              in
                TRY (safe_tac HOL_cs) ::
                maps finite_tacs (finites ~~ atomize global_ctxt finite_ind)
              end;
          in pg'' thy [] (ind_term concf) tacf end;
      in (finites, ind) end (* let *)

    else (* infinite case *)
      let
        fun one_finite n dn =
          read_instantiate global_ctxt [(("P", 0), dn ^ "_finite " ^ x_name n)] excluded_middle;
        val finites = mapn one_finite 1 dnames;

        val goal =
          let
            fun one_adm n _ = mk_trp (mk_adm (%:(P_name n)));
            fun concf n dn = %:(P_name n) $ %:(x_name n);
          in Logic.list_implies (mapn one_adm 1 dnames, ind_term concf) end;
        val cont_rules =
            @{thms cont_id cont_const cont2cont_Rep_CFun
                   cont2cont_fst cont2cont_snd};
        val subgoal =
          let fun p n dn = %:(P_name n) $ (dc_take dn $ Bound 0 `%(x_name n));
          in mk_trp (mk_all ("n", foldr1 mk_conj (mapn p 1 dnames))) end;
        val subgoal' = legacy_infer_term thy subgoal;
        fun tacf {prems, context} =
          let
            val subtac =
                EVERY [rtac allI 1, rtac finite_ind 1, ind_prems_tac prems];
            val subthm = Goal.prove context [] [] subgoal' (K subtac);
          in
            map (fn ax_reach => rtac (ax_reach RS subst) 1) axs_reach @ [
            cut_facts_tac (subthm :: take (length dnames) prems) 1,
            REPEAT (rtac @{thm conjI} 1 ORELSE
                    EVERY [etac @{thm admD [OF _ ch2ch_Rep_CFunL]} 1,
                           resolve_tac axs_chain_take 1,
                           asm_simp_tac HOL_basic_ss 1])
            ]
          end;
        val ind = (pg'' thy [] goal tacf
          handle ERROR _ =>
            (warning "Cannot prove infinite induction rule"; TrueI)
                  );
      in (finites, ind) end
  )
      handle THM _ =>
             (warning "Induction proofs failed (THM raised)."; ([], TrueI))
           | ERROR _ =>
             (warning "Cannot prove induction rule"; ([], TrueI));

val case_ns =
  let
    val bottoms =
        if length dnames = 1 then ["bottom"] else
        map (fn s => "bottom_" ^ Long_Name.base_name s) dnames;
    fun one_eq bot (_,cons) =
          bot :: map (fn (c,_) => Long_Name.base_name c) cons;
  in flat (map2 one_eq bottoms eqs) end;

val inducts = Project_Rule.projections (ProofContext.init thy) ind;
fun ind_rule (dname, rule) =
    ((Binding.empty, [rule]),
     [Rule_Cases.case_names case_ns, Induct.induct_type dname]);

val induct_failed = (Thm.prop_of ind = Thm.prop_of TrueI);

in thy |> Sign.add_path comp_dnam
       |> snd o PureThy.add_thmss [
           ((Binding.name "finites"    , finites     ), []),
           ((Binding.name "finite_ind" , [finite_ind]), []),
           ((Binding.name "ind"        , [ind]       ), [])]
       |> (if induct_failed then I
           else snd o PureThy.add_thmss (map ind_rule (dnames ~~ inducts)))
       |> Sign.parent_path
end; (* prove_induction *)

(******************************************************************************)
(************************ bisimulation and coinduction ************************)
(******************************************************************************)

fun prove_coinduction
    (comp_dnam, eqs : eq list)
    (take_lemmas : thm list)
    (thy : theory) : theory =
let

val dnames = map (fst o fst) eqs;
val comp_dname = Sign.full_bname thy comp_dnam;
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
  val bisim_bind = Binding.name (comp_dnam ^ "_bisim");
  val bisim_type = relprod --> boolT;
in
  val (bisim_const, thy) =
      Sign.declare_const ((bisim_bind, bisim_type), NoSyn) thy;
end;

local

  fun legacy_infer_term thy t =
      singleton (Syntax.check_terms (ProofContext.init thy)) (Sign.intern_term thy t);
  fun legacy_infer_prop thy t = legacy_infer_term thy (TypeInfer.constrain propT t);
  fun infer_props thy = map (apsnd (legacy_infer_prop thy));
  fun add_defs_i x = PureThy.add_defs false (map Thm.no_attributes x);
  fun add_defs_infer defs thy = add_defs_i (infer_props thy defs) thy;

  val comp_dname = Sign.full_bname thy comp_dnam;
  val dnames = map (fst o fst) eqs;
  val x_name = idx_name dnames "x"; 

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
  val ([ax_bisim_def], thy) =
      thy
        |> Sign.add_path comp_dnam
        |> add_defs_infer [(Binding.name "bisim_def", bisim_eqn)]
        ||> Sign.parent_path;
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

in thy |> Sign.add_path comp_dnam
       |> snd o PureThy.add_thmss [((Binding.name "coind", [coind]), [])]
       |> Sign.parent_path
end; (* let *)

fun comp_theorems (comp_dnam, eqs: eq list) thy =
let
val map_tab = Domain_Take_Proofs.get_map_tab thy;

val dnames = map (fst o fst) eqs;
val comp_dname = Sign.full_bname thy comp_dnam;

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

local
  fun ga s dn = PureThy.get_thm thy (dn ^ "." ^ s);
  val axs_chain_take = map (ga "chain_take") dnames;
  val axs_lub_take   = map (ga "lub_take"  ) dnames;
in
  val _ = trace " Proving take_lemmas...";
  val take_lemmas =
    let
      fun take_lemma (ax_chain_take, ax_lub_take) =
          Drule.export_without_context
            (@{thm lub_ID_take_lemma} OF [ax_chain_take, ax_lub_take]);
    in map take_lemma (axs_chain_take ~~ axs_lub_take) end;
  val axs_reach =
    let
      fun reach (ax_chain_take, ax_lub_take) =
          Drule.export_without_context
            (@{thm lub_ID_reach} OF [ax_chain_take, ax_lub_take]);
    in map reach (axs_chain_take ~~ axs_lub_take) end;
end;

val take_rews =
    maps (fn dn => PureThy.get_thms thy (dn ^ ".take_rews")) dnames;

(* prove induction rules, unless definition is indirect recursive *)
val thy =
    if is_indirect then thy else
    prove_induction (comp_dnam, eqs) take_lemmas axs_reach take_rews thy;

val thy =
    if is_indirect then thy else
    prove_coinduction (comp_dnam, eqs) take_lemmas thy;

in thy |> Sign.add_path comp_dnam
       |> snd o PureThy.add_thmss [
           ((Binding.name "take_lemmas", take_lemmas ), []),
           ((Binding.name "reach"      , axs_reach   ), [])]
       |> Sign.parent_path |> pair take_rews
end; (* let *)
end; (* struct *)
