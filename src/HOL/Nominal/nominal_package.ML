(*  Title:      HOL/Nominal/nominal_package.ML
    ID:         $Id$
    Author:     Stefan Berghofer and Christian Urban, TU Muenchen

Nominal datatype package for Isabelle/HOL.
*)

signature NOMINAL_PACKAGE =
sig
  val add_nominal_datatype : bool -> string list -> (string list * bstring * mixfix *
    (bstring * string list * mixfix) list) list -> theory -> theory
end

structure NominalPackage : NOMINAL_PACKAGE =
struct

open DatatypeAux;
open NominalAtoms;

(** FIXME: DatatypePackage should export this function **)

local

fun dt_recs (DtTFree _) = []
  | dt_recs (DtType (_, dts)) = List.concat (map dt_recs dts)
  | dt_recs (DtRec i) = [i];

fun dt_cases (descr: descr) (_, args, constrs) =
  let
    fun the_bname i = Sign.base_name (#1 (valOf (AList.lookup (op =) descr i)));
    val bnames = map the_bname (distinct op = (List.concat (map dt_recs args)));
  in map (fn (c, _) => space_implode "_" (Sign.base_name c :: bnames)) constrs end;


fun induct_cases descr =
  DatatypeProp.indexify_names (List.concat (map (dt_cases descr) (map #2 descr)));

fun exhaust_cases descr i = dt_cases descr (valOf (AList.lookup (op =) descr i));

in

fun mk_case_names_induct descr = RuleCases.case_names (induct_cases descr);

fun mk_case_names_exhausts descr new =
  map (RuleCases.case_names o exhaust_cases descr o #1)
    (List.filter (fn ((_, (name, _, _))) => name mem_string new) descr);

end;

(*******************************)

val (_ $ (_ $ (_ $ (distinct_f $ _) $ _))) = hd (prems_of distinct_lemma);

fun read_typ sign ((Ts, sorts), str) =
  let
    val T = Type.no_tvars (Sign.read_typ (sign, (AList.lookup op =)
      (map (apfst (rpair ~1)) sorts)) str) handle TYPE (msg, _, _) => error msg
  in (Ts @ [T], add_typ_tfrees (T, sorts)) end;

(** taken from HOL/Tools/datatype_aux.ML **)

fun indtac indrule indnames i st =
  let
    val ts = HOLogic.dest_conj (HOLogic.dest_Trueprop (concl_of indrule));
    val ts' = HOLogic.dest_conj (HOLogic.dest_Trueprop
      (Logic.strip_imp_concl (List.nth (prems_of st, i - 1))));
    val getP = if can HOLogic.dest_imp (hd ts) then
      (apfst SOME) o HOLogic.dest_imp else pair NONE;
    fun abstr (t1, t2) = (case t1 of
        NONE => (case filter (fn Free (s, _) => s mem indnames | _ => false)
              (term_frees t2) of
            [Free (s, T)] => absfree (s, T, t2)
          | _ => sys_error "indtac")
      | SOME (_ $ t' $ _) => Abs ("x", fastype_of t', abstract_over (t', t2)))
    val cert = cterm_of (Thm.sign_of_thm st);
    val Ps = map (cert o head_of o snd o getP) ts;
    val indrule' = cterm_instantiate (Ps ~~
      (map (cert o abstr o getP) ts')) indrule
  in
    rtac indrule' i st
  end;

fun mk_subgoal i f st =
  let
    val cg = List.nth (cprems_of st, i - 1);
    val g = term_of cg;
    val revcut_rl' = Thm.lift_rule cg revcut_rl;
    val v = head_of (Logic.strip_assums_concl (hd (prems_of revcut_rl')));
    val ps = Logic.strip_params g;
    val cert = cterm_of (sign_of_thm st);
  in
    compose_tac (false,
      Thm.instantiate ([], [(cert v, cert (list_abs (ps,
        f (rev ps) (Logic.strip_assums_hyp g) (Logic.strip_assums_concl g))))])
      revcut_rl', 2) i st
  end;

(** simplification procedure for sorting permutations **)

val dj_cp = thm "dj_cp";

fun dest_permT (Type ("fun", [Type ("List.list", [Type ("*", [T, _])]),
      Type ("fun", [_, U])])) = (T, U);

fun permTs_of (Const ("Nominal.perm", T) $ t $ u) = fst (dest_permT T) :: permTs_of u
  | permTs_of _ = [];

fun perm_simproc' thy ss (Const ("Nominal.perm", T) $ t $ (u as Const ("Nominal.perm", U) $ r $ s)) =
      let
        val (aT as Type (a, []), S) = dest_permT T;
        val (bT as Type (b, []), _) = dest_permT U
      in if aT mem permTs_of u andalso aT <> bT then
          let
            val a' = Sign.base_name a;
            val b' = Sign.base_name b;
            val cp = PureThy.get_thm thy (Name ("cp_" ^ a' ^ "_" ^ b' ^ "_inst"));
            val dj = PureThy.get_thm thy (Name ("dj_" ^ b' ^ "_" ^ a'));
            val dj_cp' = [cp, dj] MRS dj_cp;
            val cert = SOME o cterm_of thy
          in
            SOME (mk_meta_eq (Drule.instantiate' [SOME (ctyp_of thy S)]
              [cert t, cert r, cert s] dj_cp'))
          end
        else NONE
      end
  | perm_simproc' thy ss _ = NONE;

val perm_simproc =
  Simplifier.simproc (the_context ()) "perm_simp" ["pi1 \\<bullet> (pi2 \\<bullet> x)"] perm_simproc';

val allE_Nil = read_instantiate_sg (the_context()) [("x", "[]")] allE;

val meta_spec = thm "meta_spec";

fun projections rule =
  ProjectRule.projections rule
  |> map (standard #> RuleCases.save rule);

fun gen_add_nominal_datatype prep_typ err flat_names new_type_names dts thy =
  let
    (* this theory is used just for parsing *)
  
    val tmp_thy = thy |>
      Theory.copy |>
      Theory.add_types (map (fn (tvs, tname, mx, _) =>
        (tname, length tvs, mx)) dts);

    val sign = Theory.sign_of tmp_thy;

    val atoms = atoms_of thy;
    val classes = map (NameSpace.map_base (fn s => "pt_" ^ s)) atoms;
    val cp_classes = List.concat (map (fn atom1 => map (fn atom2 =>
      Sign.intern_class thy ("cp_" ^ Sign.base_name atom1 ^ "_" ^
        Sign.base_name atom2)) atoms) atoms);
    fun augment_sort S = S union classes;
    val augment_sort_typ = map_type_tfree (fn (s, S) => TFree (s, augment_sort S));

    fun prep_constr ((constrs, sorts), (cname, cargs, mx)) =
      let val (cargs', sorts') = Library.foldl (prep_typ sign) (([], sorts), cargs)
      in (constrs @ [(cname, cargs', mx)], sorts') end

    fun prep_dt_spec ((dts, sorts), (tvs, tname, mx, constrs)) =
      let val (constrs', sorts') = Library.foldl prep_constr (([], sorts), constrs)
      in (dts @ [(tvs, tname, mx, constrs')], sorts') end

    val (dts', sorts) = Library.foldl prep_dt_spec (([], []), dts);
    val sorts' = map (apsnd augment_sort) sorts;
    val tyvars = map #1 dts';

    val types_syntax = map (fn (tvs, tname, mx, constrs) => (tname, mx)) dts';
    val constr_syntax = map (fn (tvs, tname, mx, constrs) =>
      map (fn (cname, cargs, mx) => (cname, mx)) constrs) dts';

    val ps = map (fn (_, n, _, _) =>
      (Sign.full_name sign n, Sign.full_name sign (n ^ "_Rep"))) dts;
    val rps = map Library.swap ps;

    fun replace_types (Type ("Nominal.ABS", [T, U])) = 
          Type ("fun", [T, Type ("Nominal.noption", [replace_types U])])
      | replace_types (Type (s, Ts)) =
          Type (getOpt (AList.lookup op = ps s, s), map replace_types Ts)
      | replace_types T = T;

    val dts'' = map (fn (tvs, tname, mx, constrs) => (tvs, tname ^ "_Rep", NoSyn,
      map (fn (cname, cargs, mx) => (cname ^ "_Rep",
        map (augment_sort_typ o replace_types) cargs, NoSyn)) constrs)) dts';

    val new_type_names' = map (fn n => n ^ "_Rep") new_type_names;
    val full_new_type_names' = map (Sign.full_name (sign_of thy)) new_type_names';

    val ({induction, ...},thy1) =
      DatatypePackage.add_datatype_i err flat_names new_type_names' dts'' thy;

    val SOME {descr, ...} = Symtab.lookup
      (DatatypePackage.get_datatypes thy1) (hd full_new_type_names');
    fun nth_dtyp i = typ_of_dtyp descr sorts' (DtRec i);

    (**** define permutation functions ****)

    val permT = mk_permT (TFree ("'x", HOLogic.typeS));
    val pi = Free ("pi", permT);
    val perm_types = map (fn (i, _) =>
      let val T = nth_dtyp i
      in permT --> T --> T end) descr;
    val perm_names = replicate (length new_type_names) "Nominal.perm" @
      DatatypeProp.indexify_names (map (fn i => Sign.full_name (sign_of thy1)
        ("perm_" ^ name_of_typ (nth_dtyp i)))
          (length new_type_names upto length descr - 1));
    val perm_names_types = perm_names ~~ perm_types;

    val perm_eqs = List.concat (map (fn (i, (_, _, constrs)) =>
      let val T = nth_dtyp i
      in map (fn (cname, dts) => 
        let
          val Ts = map (typ_of_dtyp descr sorts') dts;
          val names = DatatypeProp.make_tnames Ts;
          val args = map Free (names ~~ Ts);
          val c = Const (cname, Ts ---> T);
          fun perm_arg (dt, x) =
            let val T = type_of x
            in if is_rec_type dt then
                let val (Us, _) = strip_type T
                in list_abs (map (pair "x") Us,
                  Const (List.nth (perm_names_types, body_index dt)) $ pi $
                    list_comb (x, map (fn (i, U) =>
                      Const ("Nominal.perm", permT --> U --> U) $
                        (Const ("List.rev", permT --> permT) $ pi) $
                        Bound i) ((length Us - 1 downto 0) ~~ Us)))
                end
              else Const ("Nominal.perm", permT --> T --> T) $ pi $ x
            end;  
        in
          (("", HOLogic.mk_Trueprop (HOLogic.mk_eq
            (Const (List.nth (perm_names_types, i)) $
               Free ("pi", mk_permT (TFree ("'x", HOLogic.typeS))) $
               list_comb (c, args),
             list_comb (c, map perm_arg (dts ~~ args))))), [])
        end) constrs
      end) descr);

    val (thy2, perm_simps) = thy1 |>
      Theory.add_consts_i (map (fn (s, T) => (Sign.base_name s, T, NoSyn))
        (List.drop (perm_names_types, length new_type_names))) |>
      PrimrecPackage.add_primrec_unchecked_i "" perm_eqs;

    (**** prove that permutation functions introduced by unfolding are ****)
    (**** equivalent to already existing permutation functions         ****)

    val _ = warning ("length descr: " ^ string_of_int (length descr));
    val _ = warning ("length new_type_names: " ^ string_of_int (length new_type_names));

    val perm_indnames = DatatypeProp.make_tnames (map body_type perm_types);
    val perm_fun_def = PureThy.get_thm thy2 (Name "perm_fun_def");

    val unfolded_perm_eq_thms =
      if length descr = length new_type_names then []
      else map standard (List.drop (split_conj_thm
        (Goal.prove thy2 [] []
          (HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj
            (map (fn (c as (s, T), x) =>
               let val [T1, T2] = binder_types T
               in HOLogic.mk_eq (Const c $ pi $ Free (x, T2),
                 Const ("Nominal.perm", T) $ pi $ Free (x, T2))
               end)
             (perm_names_types ~~ perm_indnames))))
          (fn _ => EVERY [indtac induction perm_indnames 1,
            ALLGOALS (asm_full_simp_tac
              (simpset_of thy2 addsimps [perm_fun_def]))])),
        length new_type_names));

    (**** prove [] \<bullet> t = t ****)

    val _ = warning "perm_empty_thms";

    val perm_empty_thms = List.concat (map (fn a =>
      let val permT = mk_permT (Type (a, []))
      in map standard (List.take (split_conj_thm
        (Goal.prove thy2 [] []
          (HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj
            (map (fn ((s, T), x) => HOLogic.mk_eq
                (Const (s, permT --> T --> T) $
                   Const ("List.list.Nil", permT) $ Free (x, T),
                 Free (x, T)))
             (perm_names ~~
              map body_type perm_types ~~ perm_indnames))))
          (fn _ => EVERY [indtac induction perm_indnames 1,
            ALLGOALS (asm_full_simp_tac (simpset_of thy2))])),
        length new_type_names))
      end)
      atoms);

    (**** prove (pi1 @ pi2) \<bullet> t = pi1 \<bullet> (pi2 \<bullet> t) ****)

    val _ = warning "perm_append_thms";

    (*FIXME: these should be looked up statically*)
    val at_pt_inst = PureThy.get_thm thy2 (Name "at_pt_inst");
    val pt2 = PureThy.get_thm thy2 (Name "pt2");

    val perm_append_thms = List.concat (map (fn a =>
      let
        val permT = mk_permT (Type (a, []));
        val pi1 = Free ("pi1", permT);
        val pi2 = Free ("pi2", permT);
        val pt_inst = PureThy.get_thm thy2 (Name ("pt_" ^ Sign.base_name a ^ "_inst"));
        val pt2' = pt_inst RS pt2;
        val pt2_ax = PureThy.get_thm thy2
          (Name (NameSpace.map_base (fn s => "pt_" ^ s ^ "2") a));
      in List.take (map standard (split_conj_thm
        (Goal.prove thy2 [] []
             (HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj
                (map (fn ((s, T), x) =>
                    let val perm = Const (s, permT --> T --> T)
                    in HOLogic.mk_eq
                      (perm $ (Const ("List.op @", permT --> permT --> permT) $
                         pi1 $ pi2) $ Free (x, T),
                       perm $ pi1 $ (perm $ pi2 $ Free (x, T)))
                    end)
                  (perm_names ~~
                   map body_type perm_types ~~ perm_indnames))))
           (fn _ => EVERY [indtac induction perm_indnames 1,
              ALLGOALS (asm_full_simp_tac (simpset_of thy2 addsimps [pt2', pt2_ax]))]))),
         length new_type_names)
      end) atoms);

    (**** prove pi1 ~ pi2 ==> pi1 \<bullet> t = pi2 \<bullet> t ****)

    val _ = warning "perm_eq_thms";

    val pt3 = PureThy.get_thm thy2 (Name "pt3");
    val pt3_rev = PureThy.get_thm thy2 (Name "pt3_rev");

    val perm_eq_thms = List.concat (map (fn a =>
      let
        val permT = mk_permT (Type (a, []));
        val pi1 = Free ("pi1", permT);
        val pi2 = Free ("pi2", permT);
        (*FIXME: not robust - better access these theorems using NominalData?*)
        val at_inst = PureThy.get_thm thy2 (Name ("at_" ^ Sign.base_name a ^ "_inst"));
        val pt_inst = PureThy.get_thm thy2 (Name ("pt_" ^ Sign.base_name a ^ "_inst"));
        val pt3' = pt_inst RS pt3;
        val pt3_rev' = at_inst RS (pt_inst RS pt3_rev);
        val pt3_ax = PureThy.get_thm thy2
          (Name (NameSpace.map_base (fn s => "pt_" ^ s ^ "3") a));
      in List.take (map standard (split_conj_thm
        (Goal.prove thy2 [] [] (Logic.mk_implies
             (HOLogic.mk_Trueprop (Const ("Nominal.prm_eq",
                permT --> permT --> HOLogic.boolT) $ pi1 $ pi2),
              HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj
                (map (fn ((s, T), x) =>
                    let val perm = Const (s, permT --> T --> T)
                    in HOLogic.mk_eq
                      (perm $ pi1 $ Free (x, T),
                       perm $ pi2 $ Free (x, T))
                    end)
                  (perm_names ~~
                   map body_type perm_types ~~ perm_indnames)))))
           (fn _ => EVERY [indtac induction perm_indnames 1,
              ALLGOALS (asm_full_simp_tac (simpset_of thy2 addsimps [pt3', pt3_rev', pt3_ax]))]))),
         length new_type_names)
      end) atoms);

    (**** prove pi1 \<bullet> (pi2 \<bullet> t) = (pi1 \<bullet> pi2) \<bullet> (pi1 \<bullet> t) ****)

    val cp1 = PureThy.get_thm thy2 (Name "cp1");
    val dj_cp = PureThy.get_thm thy2 (Name "dj_cp");
    val pt_perm_compose = PureThy.get_thm thy2 (Name "pt_perm_compose");
    val pt_perm_compose_rev = PureThy.get_thm thy2 (Name "pt_perm_compose_rev");
    val dj_perm_perm_forget = PureThy.get_thm thy2 (Name "dj_perm_perm_forget");

    fun composition_instance name1 name2 thy =
      let
        val name1' = Sign.base_name name1;
        val name2' = Sign.base_name name2;
        val cp_class = Sign.intern_class thy ("cp_" ^ name1' ^ "_" ^ name2');
        val permT1 = mk_permT (Type (name1, []));
        val permT2 = mk_permT (Type (name2, []));
        val augment = map_type_tfree
          (fn (x, S) => TFree (x, cp_class :: S));
        val Ts = map (augment o body_type) perm_types;
        val cp_inst = PureThy.get_thm thy
          (Name ("cp_" ^ name1' ^ "_" ^ name2' ^ "_inst"));
        val simps = simpset_of thy addsimps (perm_fun_def ::
          (if name1 <> name2 then
             let val dj = PureThy.get_thm thy (Name ("dj_" ^ name2' ^ "_" ^ name1'))
             in [dj RS (cp_inst RS dj_cp), dj RS dj_perm_perm_forget] end
           else
             let
               val at_inst = PureThy.get_thm thy (Name ("at_" ^ name1' ^ "_inst"));
               val pt_inst = PureThy.get_thm thy (Name ("pt_" ^ name1' ^ "_inst"))
             in
               [cp_inst RS cp1 RS sym,
                at_inst RS (pt_inst RS pt_perm_compose) RS sym,
                at_inst RS (pt_inst RS pt_perm_compose_rev) RS sym]
            end))
        val thms = split_conj_thm (standard (Goal.prove thy [] []
            (HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj
              (map (fn ((s, T), x) =>
                  let
                    val pi1 = Free ("pi1", permT1);
                    val pi2 = Free ("pi2", permT2);
                    val perm1 = Const (s, permT1 --> T --> T);
                    val perm2 = Const (s, permT2 --> T --> T);
                    val perm3 = Const ("Nominal.perm", permT1 --> permT2 --> permT2)
                  in HOLogic.mk_eq
                    (perm1 $ pi1 $ (perm2 $ pi2 $ Free (x, T)),
                     perm2 $ (perm3 $ pi1 $ pi2) $ (perm1 $ pi1 $ Free (x, T)))
                  end)
                (perm_names ~~ Ts ~~ perm_indnames))))
          (fn _ => EVERY [indtac induction perm_indnames 1,
             ALLGOALS (asm_full_simp_tac simps)])))
      in
        foldl (fn ((s, tvs), thy) => AxClass.prove_arity
            (s, replicate (length tvs) (cp_class :: classes), [cp_class])
            (ClassPackage.intro_classes_tac [] THEN ALLGOALS (resolve_tac thms)) thy)
          thy (full_new_type_names' ~~ tyvars)
      end;

    val (perm_thmss,thy3) = thy2 |>
      fold (fn name1 => fold (composition_instance name1) atoms) atoms |>
      curry (Library.foldr (fn ((i, (tyname, args, _)), thy) =>
        AxClass.prove_arity (tyname, replicate (length args) classes, classes)
        (ClassPackage.intro_classes_tac [] THEN REPEAT (EVERY
           [resolve_tac perm_empty_thms 1,
            resolve_tac perm_append_thms 1,
            resolve_tac perm_eq_thms 1, assume_tac 1])) thy))
        (List.take (descr, length new_type_names)) |>
      PureThy.add_thmss
        [((space_implode "_" new_type_names ^ "_unfolded_perm_eq",
          unfolded_perm_eq_thms), [Simplifier.simp_add]),
         ((space_implode "_" new_type_names ^ "_perm_empty",
          perm_empty_thms), [Simplifier.simp_add]),
         ((space_implode "_" new_type_names ^ "_perm_append",
          perm_append_thms), [Simplifier.simp_add]),
         ((space_implode "_" new_type_names ^ "_perm_eq",
          perm_eq_thms), [Simplifier.simp_add])];
  
    (**** Define representing sets ****)

    val _ = warning "representing sets";

    val rep_set_names = map (Sign.full_name thy3) (DatatypeProp.indexify_names
      (map (fn (i, _) => name_of_typ (nth_dtyp i) ^ "_set") descr));
    val big_rep_name =
      space_implode "_" (DatatypeProp.indexify_names (List.mapPartial
        (fn (i, ("Nominal.noption", _, _)) => NONE
          | (i, _) => SOME (name_of_typ (nth_dtyp i))) descr)) ^ "_set";
    val _ = warning ("big_rep_name: " ^ big_rep_name);

    fun strip_option (dtf as DtType ("fun", [dt, DtRec i])) =
          (case AList.lookup op = descr i of
             SOME ("Nominal.noption", _, [(_, [dt']), _]) =>
               apfst (cons dt) (strip_option dt')
           | _ => ([], dtf))
      | strip_option (DtType ("fun", [dt, DtType ("Nominal.noption", [dt'])])) =
          apfst (cons dt) (strip_option dt')
      | strip_option dt = ([], dt);

    val dt_atomTs = distinct op = (map (typ_of_dtyp descr sorts')
      (List.concat (map (fn (_, (_, _, cs)) => List.concat
        (map (List.concat o map (fst o strip_option) o snd) cs)) descr)));

    fun make_intr s T (cname, cargs) =
      let
        fun mk_prem (dt, (j, j', prems, ts)) = 
          let
            val (dts, dt') = strip_option dt;
            val (dts', dt'') = strip_dtyp dt';
            val Ts = map (typ_of_dtyp descr sorts') dts;
            val Us = map (typ_of_dtyp descr sorts') dts';
            val T = typ_of_dtyp descr sorts' dt'';
            val free = mk_Free "x" (Us ---> T) j;
            val free' = app_bnds free (length Us);
            fun mk_abs_fun (T, (i, t)) =
              let val U = fastype_of t
              in (i + 1, Const ("Nominal.abs_fun", [T, U, T] --->
                Type ("Nominal.noption", [U])) $ mk_Free "y" T i $ t)
              end
          in (j + 1, j' + length Ts,
            case dt'' of
                DtRec k => list_all (map (pair "x") Us,
                  HOLogic.mk_Trueprop (HOLogic.mk_mem (free',
                    Const (List.nth (rep_set_names, k),
                      HOLogic.mk_setT T)))) :: prems
              | _ => prems,
            snd (foldr mk_abs_fun (j', free) Ts) :: ts)
          end;

        val (_, _, prems, ts) = foldr mk_prem (1, 1, [], []) cargs;
        val concl = HOLogic.mk_Trueprop (HOLogic.mk_mem
          (list_comb (Const (cname, map fastype_of ts ---> T), ts),
           Const (s, HOLogic.mk_setT T)))
      in Logic.list_implies (prems, concl)
      end;

    val (intr_ts, ind_consts) =
      apfst List.concat (ListPair.unzip (List.mapPartial
        (fn ((_, ("Nominal.noption", _, _)), _) => NONE
          | ((i, (_, _, constrs)), rep_set_name) =>
              let val T = nth_dtyp i
              in SOME (map (make_intr rep_set_name T) constrs,
                Const (rep_set_name, HOLogic.mk_setT T))
              end)
                (descr ~~ rep_set_names)));

    val (thy4, {raw_induct = rep_induct, intrs = rep_intrs, ...}) =
      setmp InductivePackage.quiet_mode false
        (InductivePackage.add_inductive_i false true big_rep_name false true false
           ind_consts (map (fn x => (("", x), [])) intr_ts) []) thy3;

    (**** Prove that representing set is closed under permutation ****)

    val _ = warning "proving closure under permutation...";

    val perm_indnames' = List.mapPartial
      (fn (x, (_, ("Nominal.noption", _, _))) => NONE | (x, _) => SOME x)
      (perm_indnames ~~ descr);

    fun mk_perm_closed name = map (fn th => standard (th RS mp))
      (List.take (split_conj_thm (Goal.prove thy4 [] []
        (HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj (map
           (fn (S, x) =>
              let
                val S = map_term_types (map_type_tfree
                  (fn (s, cs) => TFree (s, cs union cp_classes))) S;
                val T = HOLogic.dest_setT (fastype_of S);
                val permT = mk_permT (Type (name, []))
              in HOLogic.mk_imp (HOLogic.mk_mem (Free (x, T), S),
                HOLogic.mk_mem (Const ("Nominal.perm", permT --> T --> T) $
                  Free ("pi", permT) $ Free (x, T), S))
              end) (ind_consts ~~ perm_indnames'))))
        (fn _ => EVERY (* CU: added perm_fun_def in the final tactic in order to deal with funs *)
           [indtac rep_induct [] 1,
            ALLGOALS (simp_tac (simpset_of thy4 addsimps
              (symmetric perm_fun_def :: PureThy.get_thms thy4 (Name ("abs_perm"))))),
            ALLGOALS (resolve_tac rep_intrs 
               THEN_ALL_NEW (asm_full_simp_tac (simpset_of thy4 addsimps [perm_fun_def])))])),
        length new_type_names));

    (* FIXME: theorems are stored in database for testing only *)
    val perm_closed_thmss = map mk_perm_closed atoms;
    val (_,thy5) = PureThy.add_thmss [(("perm_closed", List.concat perm_closed_thmss), [])] thy4;

    (**** typedef ****)

    val _ = warning "defining type...";

    val (typedefs, thy6) =
      fold_map (fn ((((name, mx), tvs), c), name') => fn thy =>
        setmp TypedefPackage.quiet_mode true
          (TypedefPackage.add_typedef_i false (SOME name') (name, tvs, mx) c NONE
            (rtac exI 1 THEN
              QUIET_BREADTH_FIRST (has_fewer_prems 1)
              (resolve_tac rep_intrs 1))) thy |> (fn (r, thy) =>
        let
          val permT = mk_permT (TFree (variant tvs "'a", HOLogic.typeS));
          val pi = Free ("pi", permT);
          val tvs' = map (fn s => TFree (s, the (AList.lookup op = sorts' s))) tvs;
          val T = Type (Sign.intern_type thy name, tvs');
          val Const (_, Type (_, [U])) = c
        in apfst (pair r o hd)
          (PureThy.add_defs_unchecked_i true [(("prm_" ^ name ^ "_def", Logic.mk_equals
            (Const ("Nominal.perm", permT --> T --> T) $ pi $ Free ("x", T),
             Const (Sign.intern_const thy ("Abs_" ^ name), U --> T) $
               (Const ("Nominal.perm", permT --> U --> U) $ pi $
                 (Const (Sign.intern_const thy ("Rep_" ^ name), T --> U) $
                   Free ("x", T))))), [])] thy)
        end))
          (types_syntax ~~ tyvars ~~
            (List.take (ind_consts, length new_type_names)) ~~ new_type_names) thy5;

    val perm_defs = map snd typedefs;
    val Abs_inverse_thms = map (#Abs_inverse o fst) typedefs;
    val Rep_inverse_thms = map (#Rep_inverse o fst) typedefs;
    val Rep_thms = map (#Rep o fst) typedefs;

    val big_name = space_implode "_" new_type_names;


    (** prove that new types are in class pt_<name> **)

    val _ = warning "prove that new types are in class pt_<name> ...";

    fun pt_instance ((class, atom), perm_closed_thms) =
      fold (fn (((({Abs_inverse, Rep_inverse, Rep, ...},
        perm_def), name), tvs), perm_closed) => fn thy =>
          AxClass.prove_arity
            (Sign.intern_type thy name,
              replicate (length tvs) (classes @ cp_classes), [class])
            (EVERY [ClassPackage.intro_classes_tac [],
              rewrite_goals_tac [perm_def],
              asm_full_simp_tac (simpset_of thy addsimps [Rep_inverse]) 1,
              asm_full_simp_tac (simpset_of thy addsimps
                [Rep RS perm_closed RS Abs_inverse]) 1,
              asm_full_simp_tac (HOL_basic_ss addsimps [PureThy.get_thm thy
                (Name ("pt_" ^ Sign.base_name atom ^ "3"))]) 1]) thy)
        (typedefs ~~ new_type_names ~~ tyvars ~~ perm_closed_thms);


    (** prove that new types are in class cp_<name1>_<name2> **)

    val _ = warning "prove that new types are in class cp_<name1>_<name2> ...";

    fun cp_instance (atom1, perm_closed_thms1) (atom2, perm_closed_thms2) thy =
      let
        val name = "cp_" ^ Sign.base_name atom1 ^ "_" ^ Sign.base_name atom2;
        val class = Sign.intern_class thy name;
        val cp1' = PureThy.get_thm thy (Name (name ^ "_inst")) RS cp1
      in fold (fn ((((({Abs_inverse, Rep_inverse, Rep, ...},
        perm_def), name), tvs), perm_closed1), perm_closed2) => fn thy =>
          AxClass.prove_arity
            (Sign.intern_type thy name,
              replicate (length tvs) (classes @ cp_classes), [class])
            (EVERY [ClassPackage.intro_classes_tac [],
              rewrite_goals_tac [perm_def],
              asm_full_simp_tac (simpset_of thy addsimps
                ((Rep RS perm_closed1 RS Abs_inverse) ::
                 (if atom1 = atom2 then []
                  else [Rep RS perm_closed2 RS Abs_inverse]))) 1,
              cong_tac 1,
              rtac refl 1,
              rtac cp1' 1]) thy)
        (typedefs ~~ new_type_names ~~ tyvars ~~ perm_closed_thms1 ~~
          perm_closed_thms2) thy
      end;

    val thy7 = fold (fn x => fn thy => thy |>
      pt_instance x |>
      fold (cp_instance (apfst snd x)) (atoms ~~ perm_closed_thmss))
        (classes ~~ atoms ~~ perm_closed_thmss) thy6;

    (**** constructors ****)

    fun mk_abs_fun (x, t) =
      let
        val T = fastype_of x;
        val U = fastype_of t
      in
        Const ("Nominal.abs_fun", T --> U --> T -->
          Type ("Nominal.noption", [U])) $ x $ t
      end;

    val (ty_idxs, _) = foldl
      (fn ((i, ("Nominal.noption", _, _)), p) => p
        | ((i, _), (ty_idxs, j)) => (ty_idxs @ [(i, j)], j + 1)) ([], 0) descr;

    fun reindex (DtType (s, dts)) = DtType (s, map reindex dts)
      | reindex (DtRec i) = DtRec (the (AList.lookup op = ty_idxs i))
      | reindex dt = dt;

    fun strip_suffix i s = implode (List.take (explode s, size s - i));

    (** strips the "_Rep" in type names *)
    fun strip_nth_name i s = 
      let val xs = NameSpace.unpack s; 
      in NameSpace.pack (Library.nth_map (length xs - i) (strip_suffix 4) xs) end;

    val (descr'', ndescr) = ListPair.unzip (List.mapPartial
      (fn (i, ("Nominal.noption", _, _)) => NONE
        | (i, (s, dts, constrs)) =>
             let
               val SOME index = AList.lookup op = ty_idxs i;
               val (constrs1, constrs2) = ListPair.unzip
                 (map (fn (cname, cargs) => apfst (pair (strip_nth_name 2 (strip_nth_name 1 cname)))
                   (foldl_map (fn (dts, dt) =>
                     let val (dts', dt') = strip_option dt
                     in (dts @ dts' @ [reindex dt'], (length dts, length dts')) end)
                       ([], cargs))) constrs)
             in SOME ((index, (strip_nth_name 1 s,  map reindex dts, constrs1)),
               (index, constrs2))
             end) descr);

    val (descr1, descr2) = chop (length new_type_names) descr'';
    val descr' = [descr1, descr2];

    fun partition_cargs idxs xs = map (fn (i, j) =>
      (List.take (List.drop (xs, i), j), List.nth (xs, i + j))) idxs;

    val pdescr = map (fn ((i, (s, dts, constrs)), (_, idxss)) => (i, (s, dts,
      map (fn ((cname, cargs), idxs) => (cname, partition_cargs idxs cargs))
        (constrs ~~ idxss)))) (descr'' ~~ ndescr);

    fun nth_dtyp' i = typ_of_dtyp descr'' sorts' (DtRec i);

    val rep_names = map (fn s =>
      Sign.intern_const thy7 ("Rep_" ^ s)) new_type_names;
    val abs_names = map (fn s =>
      Sign.intern_const thy7 ("Abs_" ^ s)) new_type_names;

    val recTs' = List.mapPartial
      (fn ((_, ("Nominal.noption", _, _)), T) => NONE
        | (_, T) => SOME T) (descr ~~ get_rec_types descr sorts');
    val recTs = get_rec_types descr'' sorts';
    val newTs' = Library.take (length new_type_names, recTs');
    val newTs = Library.take (length new_type_names, recTs);

    val full_new_type_names = map (Sign.full_name (sign_of thy)) new_type_names;

    fun make_constr_def tname T T' ((thy, defs, eqns),
        (((cname_rep, _), (cname, cargs)), (cname', mx))) =
      let
        fun constr_arg ((dts, dt), (j, l_args, r_args)) =
          let
            val xs = map (fn (dt, i) => mk_Free "x" (typ_of_dtyp descr'' sorts' dt) i)
              (dts ~~ (j upto j + length dts - 1))
            val x = mk_Free "x" (typ_of_dtyp descr'' sorts' dt) (j + length dts)
          in
            (j + length dts + 1,
             xs @ x :: l_args,
             foldr mk_abs_fun
               (case dt of
                  DtRec k => if k < length new_type_names then
                      Const (List.nth (rep_names, k), typ_of_dtyp descr'' sorts' dt -->
                        typ_of_dtyp descr sorts' dt) $ x
                    else error "nested recursion not (yet) supported"
                | _ => x) xs :: r_args)
          end

        val (_, l_args, r_args) = foldr constr_arg (1, [], []) cargs;
        val abs_name = Sign.intern_const (Theory.sign_of thy) ("Abs_" ^ tname);
        val rep_name = Sign.intern_const (Theory.sign_of thy) ("Rep_" ^ tname);
        val constrT = map fastype_of l_args ---> T;
        val lhs = list_comb (Const (cname, constrT), l_args);
        val rhs = list_comb (Const (cname_rep, map fastype_of r_args ---> T'), r_args);
        val def = Logic.mk_equals (lhs, Const (abs_name, T' --> T) $ rhs);
        val eqn = HOLogic.mk_Trueprop (HOLogic.mk_eq
          (Const (rep_name, T --> T') $ lhs, rhs));
        val def_name = (Sign.base_name cname) ^ "_def";
        val ([def_thm], thy') = thy |>
          Theory.add_consts_i [(cname', constrT, mx)] |>
          (PureThy.add_defs_i false o map Thm.no_attributes) [(def_name, def)]
      in (thy', defs @ [def_thm], eqns @ [eqn]) end;

    fun dt_constr_defs ((thy, defs, eqns, dist_lemmas), ((((((_, (_, _, constrs)),
        (_, (_, _, constrs'))), tname), T), T'), constr_syntax)) =
      let
        val rep_const = cterm_of thy
          (Const (Sign.intern_const thy ("Rep_" ^ tname), T --> T'));
        val dist = standard (cterm_instantiate [(cterm_of thy distinct_f, rep_const)] distinct_lemma);
        val (thy', defs', eqns') = Library.foldl (make_constr_def tname T T')
          ((Theory.add_path tname thy, defs, []), constrs ~~ constrs' ~~ constr_syntax)
      in
        (parent_path flat_names thy', defs', eqns @ [eqns'], dist_lemmas @ [dist])
      end;

    val (thy8, constr_defs, constr_rep_eqns, dist_lemmas) = Library.foldl dt_constr_defs
      ((thy7, [], [], []), List.take (descr, length new_type_names) ~~
        List.take (pdescr, length new_type_names) ~~
        new_type_names ~~ newTs ~~ newTs' ~~ constr_syntax);

    val abs_inject_thms = map (fn tname =>
      PureThy.get_thm thy8 (Name ("Abs_" ^ tname ^ "_inject"))) new_type_names;

    val rep_inject_thms = map (fn tname =>
      PureThy.get_thm thy8 (Name ("Rep_" ^ tname ^ "_inject"))) new_type_names;

    val rep_thms = map (fn tname =>
      PureThy.get_thm thy8 (Name ("Rep_" ^ tname))) new_type_names;

    val rep_inverse_thms = map (fn tname =>
      PureThy.get_thm thy8 (Name ("Rep_" ^ tname ^ "_inverse"))) new_type_names;

    (* prove theorem  Rep_i (Constr_j ...) = Constr'_j ...  *)
    
    fun prove_constr_rep_thm eqn =
      let
        val inj_thms = map (fn r => r RS iffD1) abs_inject_thms;
        val rewrites = constr_defs @ map mk_meta_eq rep_inverse_thms
      in standard (Goal.prove thy8 [] [] eqn (fn _ => EVERY
        [resolve_tac inj_thms 1,
         rewrite_goals_tac rewrites,
         rtac refl 3,
         resolve_tac rep_intrs 2,
         REPEAT (resolve_tac rep_thms 1)]))
      end;

    val constr_rep_thmss = map (map prove_constr_rep_thm) constr_rep_eqns;

    (* prove theorem  pi \<bullet> Rep_i x = Rep_i (pi \<bullet> x) *)

    fun prove_perm_rep_perm (atom, perm_closed_thms) = map (fn th =>
      let
        val _ $ (_ $ (Rep $ x) $ _) = Logic.unvarify (prop_of th);
        val Type ("fun", [T, U]) = fastype_of Rep;
        val permT = mk_permT (Type (atom, []));
        val pi = Free ("pi", permT);
      in
        standard (Goal.prove thy8 [] [] (HOLogic.mk_Trueprop (HOLogic.mk_eq
            (Const ("Nominal.perm", permT --> U --> U) $ pi $ (Rep $ x),
             Rep $ (Const ("Nominal.perm", permT --> T --> T) $ pi $ x))))
          (fn _ => simp_tac (HOL_basic_ss addsimps (perm_defs @ Abs_inverse_thms @
            perm_closed_thms @ Rep_thms)) 1))
      end) Rep_thms;

    val perm_rep_perm_thms = List.concat (map prove_perm_rep_perm
      (atoms ~~ perm_closed_thmss));

    (* prove distinctness theorems *)

    val distinct_props = setmp DatatypeProp.dtK 1000
      (DatatypeProp.make_distincts new_type_names descr' sorts') thy8;

    val dist_rewrites = map (fn (rep_thms, dist_lemma) =>
      dist_lemma::(rep_thms @ [In0_eq, In1_eq, In0_not_In1, In1_not_In0]))
        (constr_rep_thmss ~~ dist_lemmas);

    fun prove_distinct_thms (_, []) = []
      | prove_distinct_thms (p as (rep_thms, dist_lemma), t::ts) =
          let
            val dist_thm = standard (Goal.prove thy8 [] [] t (fn _ =>
              simp_tac (simpset_of thy8 addsimps (dist_lemma :: rep_thms)) 1))
          in dist_thm::(standard (dist_thm RS not_sym))::
            (prove_distinct_thms (p, ts))
          end;

    val distinct_thms = map prove_distinct_thms
      (constr_rep_thmss ~~ dist_lemmas ~~ distinct_props);

    (** prove equations for permutation functions **)

    val abs_perm = PureThy.get_thms thy8 (Name "abs_perm"); (* FIXME *)

    val perm_simps' = map (fn (((i, (_, _, constrs)), tname), constr_rep_thms) =>
      let val T = nth_dtyp' i
      in List.concat (map (fn (atom, perm_closed_thms) =>
          map (fn ((cname, dts), constr_rep_thm) => 
        let
          val cname = Sign.intern_const thy8
            (NameSpace.append tname (Sign.base_name cname));
          val permT = mk_permT (Type (atom, []));
          val pi = Free ("pi", permT);

          fun perm t =
            let val T = fastype_of t
            in Const ("Nominal.perm", permT --> T --> T) $ pi $ t end;

          fun constr_arg ((dts, dt), (j, l_args, r_args)) =
            let
              val Ts = map (typ_of_dtyp descr'' sorts') dts;
              val xs = map (fn (T, i) => mk_Free "x" T i)
                (Ts ~~ (j upto j + length dts - 1))
              val x = mk_Free "x" (typ_of_dtyp descr'' sorts' dt) (j + length dts)
            in
              (j + length dts + 1,
               xs @ x :: l_args,
               map perm (xs @ [x]) @ r_args)
            end

          val (_, l_args, r_args) = foldr constr_arg (1, [], []) dts;
          val c = Const (cname, map fastype_of l_args ---> T)
        in
          standard (Goal.prove thy8 [] []
            (HOLogic.mk_Trueprop (HOLogic.mk_eq
              (perm (list_comb (c, l_args)), list_comb (c, r_args))))
            (fn _ => EVERY
              [simp_tac (simpset_of thy8 addsimps (constr_rep_thm :: perm_defs)) 1,
               simp_tac (HOL_basic_ss addsimps (Rep_thms @ Abs_inverse_thms @
                 constr_defs @ perm_closed_thms)) 1,
               TRY (simp_tac (HOL_basic_ss addsimps
                 (symmetric perm_fun_def :: abs_perm)) 1),
               TRY (simp_tac (HOL_basic_ss addsimps
                 (perm_fun_def :: perm_defs @ Rep_thms @ Abs_inverse_thms @
                    perm_closed_thms)) 1)]))
        end) (constrs ~~ constr_rep_thms)) (atoms ~~ perm_closed_thmss))
      end) (List.take (pdescr, length new_type_names) ~~ new_type_names ~~ constr_rep_thmss);

    (** prove injectivity of constructors **)

    val rep_inject_thms' = map (fn th => th RS sym) rep_inject_thms;
    val alpha = PureThy.get_thms thy8 (Name "alpha");
    val abs_fresh = PureThy.get_thms thy8 (Name "abs_fresh");
    val fresh_def = PureThy.get_thm thy8 (Name "fresh_def");
    val supp_def = PureThy.get_thm thy8 (Name "supp_def");

    val inject_thms = map (fn (((i, (_, _, constrs)), tname), constr_rep_thms) =>
      let val T = nth_dtyp' i
      in List.mapPartial (fn ((cname, dts), constr_rep_thm) =>
        if null dts then NONE else SOME
        let
          val cname = Sign.intern_const thy8
            (NameSpace.append tname (Sign.base_name cname));

          fun make_inj ((dts, dt), (j, args1, args2, eqs)) =
            let
              val Ts_idx = map (typ_of_dtyp descr'' sorts') dts ~~ (j upto j + length dts - 1);
              val xs = map (fn (T, i) => mk_Free "x" T i) Ts_idx;
              val ys = map (fn (T, i) => mk_Free "y" T i) Ts_idx;
              val x = mk_Free "x" (typ_of_dtyp descr'' sorts' dt) (j + length dts);
              val y = mk_Free "y" (typ_of_dtyp descr'' sorts' dt) (j + length dts)
            in
              (j + length dts + 1,
               xs @ (x :: args1), ys @ (y :: args2),
               HOLogic.mk_eq
                 (foldr mk_abs_fun x xs, foldr mk_abs_fun y ys) :: eqs)
            end;

          val (_, args1, args2, eqs) = foldr make_inj (1, [], [], []) dts;
          val Ts = map fastype_of args1;
          val c = Const (cname, Ts ---> T)
        in
          standard (Goal.prove thy8 [] [] (HOLogic.mk_Trueprop (HOLogic.mk_eq
              (HOLogic.mk_eq (list_comb (c, args1), list_comb (c, args2)),
               foldr1 HOLogic.mk_conj eqs)))
            (fn _ => EVERY
               [asm_full_simp_tac (simpset_of thy8 addsimps (constr_rep_thm ::
                  rep_inject_thms')) 1,
                TRY (asm_full_simp_tac (HOL_basic_ss addsimps (fresh_def :: supp_def ::
                  alpha @ abs_perm @ abs_fresh @ rep_inject_thms @
                  perm_rep_perm_thms)) 1),
                TRY (asm_full_simp_tac (HOL_basic_ss addsimps (perm_fun_def ::
                  expand_fun_eq :: rep_inject_thms @ perm_rep_perm_thms)) 1)]))
        end) (constrs ~~ constr_rep_thms)
      end) (List.take (pdescr, length new_type_names) ~~ new_type_names ~~ constr_rep_thmss);

    (** equations for support and freshness **)

    val Un_assoc = PureThy.get_thm thy8 (Name "Un_assoc");
    val de_Morgan_conj = PureThy.get_thm thy8 (Name "de_Morgan_conj");
    val Collect_disj_eq = PureThy.get_thm thy8 (Name "Collect_disj_eq");
    val finite_Un = PureThy.get_thm thy8 (Name "finite_Un");

    val (supp_thms, fresh_thms) = ListPair.unzip (map ListPair.unzip
      (map (fn ((((i, (_, _, constrs)), tname), inject_thms'), perm_thms') =>
      let val T = nth_dtyp' i
      in List.concat (map (fn (cname, dts) => map (fn atom =>
        let
          val cname = Sign.intern_const thy8
            (NameSpace.append tname (Sign.base_name cname));
          val atomT = Type (atom, []);

          fun process_constr ((dts, dt), (j, args1, args2)) =
            let
              val Ts_idx = map (typ_of_dtyp descr'' sorts') dts ~~ (j upto j + length dts - 1);
              val xs = map (fn (T, i) => mk_Free "x" T i) Ts_idx;
              val x = mk_Free "x" (typ_of_dtyp descr'' sorts' dt) (j + length dts)
            in
              (j + length dts + 1,
               xs @ (x :: args1), foldr mk_abs_fun x xs :: args2)
            end;

          val (_, args1, args2) = foldr process_constr (1, [], []) dts;
          val Ts = map fastype_of args1;
          val c = list_comb (Const (cname, Ts ---> T), args1);
          fun supp t =
            Const ("Nominal.supp", fastype_of t --> HOLogic.mk_setT atomT) $ t;
          fun fresh t =
            Const ("Nominal.fresh", atomT --> fastype_of t --> HOLogic.boolT) $
              Free ("a", atomT) $ t;
          val supp_thm = standard (Goal.prove thy8 [] []
              (HOLogic.mk_Trueprop (HOLogic.mk_eq
                (supp c,
                 if null dts then Const ("{}", HOLogic.mk_setT atomT)
                 else foldr1 (HOLogic.mk_binop "op Un") (map supp args2))))
            (fn _ =>
              simp_tac (HOL_basic_ss addsimps (supp_def ::
                 Un_assoc :: de_Morgan_conj :: Collect_disj_eq :: finite_Un ::
                 symmetric empty_def :: Finites.emptyI :: simp_thms @
                 abs_perm @ abs_fresh @ inject_thms' @ perm_thms')) 1))
        in
          (supp_thm,
           standard (Goal.prove thy8 [] [] (HOLogic.mk_Trueprop (HOLogic.mk_eq
              (fresh c,
               if null dts then HOLogic.true_const
               else foldr1 HOLogic.mk_conj (map fresh args2))))
             (fn _ =>
               simp_tac (simpset_of thy8 addsimps [fresh_def, supp_thm]) 1)))
        end) atoms) constrs)
      end) (List.take (pdescr, length new_type_names) ~~ new_type_names ~~ inject_thms ~~ perm_simps')));

    (**** weak induction theorem ****)

    fun mk_indrule_lemma ((prems, concls), (((i, _), T), U)) =
      let
        val Rep_t = Const (List.nth (rep_names, i), T --> U) $
          mk_Free "x" T i;

        val Abs_t =  Const (List.nth (abs_names, i), U --> T)

      in (prems @ [HOLogic.imp $ HOLogic.mk_mem (Rep_t,
            Const (List.nth (rep_set_names, i), HOLogic.mk_setT U)) $
              (mk_Free "P" (T --> HOLogic.boolT) (i + 1) $ (Abs_t $ Rep_t))],
          concls @ [mk_Free "P" (T --> HOLogic.boolT) (i + 1) $ mk_Free "x" T i])
      end;

    val (indrule_lemma_prems, indrule_lemma_concls) =
      Library.foldl mk_indrule_lemma (([], []), (descr'' ~~ recTs ~~ recTs'));

    val indrule_lemma = standard (Goal.prove thy8 [] []
      (Logic.mk_implies
        (HOLogic.mk_Trueprop (mk_conj indrule_lemma_prems),
         HOLogic.mk_Trueprop (mk_conj indrule_lemma_concls))) (fn _ => EVERY
           [REPEAT (etac conjE 1),
            REPEAT (EVERY
              [TRY (rtac conjI 1), full_simp_tac (HOL_basic_ss addsimps Rep_inverse_thms) 1,
               etac mp 1, resolve_tac Rep_thms 1])]));

    val Ps = map head_of (HOLogic.dest_conj (HOLogic.dest_Trueprop (concl_of indrule_lemma)));
    val frees = if length Ps = 1 then [Free ("P", snd (dest_Var (hd Ps)))] else
      map (Free o apfst fst o dest_Var) Ps;
    val indrule_lemma' = cterm_instantiate
      (map (cterm_of thy8) Ps ~~ map (cterm_of thy8) frees) indrule_lemma;

    val Abs_inverse_thms' = map (fn r => r RS subst) Abs_inverse_thms;

    val dt_induct_prop = DatatypeProp.make_ind descr' sorts';
    val dt_induct = standard (Goal.prove thy8 []
      (Logic.strip_imp_prems dt_induct_prop) (Logic.strip_imp_concl dt_induct_prop)
      (fn prems => EVERY
        [rtac indrule_lemma' 1,
         (DatatypeAux.indtac rep_induct THEN_ALL_NEW ObjectLogic.atomize_tac) 1,
         EVERY (map (fn (prem, r) => (EVERY
           [REPEAT (eresolve_tac Abs_inverse_thms' 1),
            simp_tac (HOL_basic_ss addsimps [symmetric r]) 1,
            DEPTH_SOLVE_1 (ares_tac [prem] 1 ORELSE etac allE 1)]))
                (prems ~~ constr_defs))]));

    val case_names_induct = mk_case_names_induct descr'';

    (**** prove that new datatypes have finite support ****)

    val _ = warning "proving finite support for the new datatype";

    val indnames = DatatypeProp.make_tnames recTs;

    val abs_supp = PureThy.get_thms thy8 (Name "abs_supp");
    val supp_atm = PureThy.get_thms thy8 (Name "supp_atm");

    val finite_supp_thms = map (fn atom =>
      let val atomT = Type (atom, [])
      in map standard (List.take
        (split_conj_thm (Goal.prove thy8 [] [] (HOLogic.mk_Trueprop
           (foldr1 HOLogic.mk_conj (map (fn (s, T) => HOLogic.mk_mem
             (Const ("Nominal.supp", T --> HOLogic.mk_setT atomT) $ Free (s, T),
              Const ("Finite_Set.Finites", HOLogic.mk_setT (HOLogic.mk_setT atomT))))
               (indnames ~~ recTs))))
           (fn _ => indtac dt_induct indnames 1 THEN
            ALLGOALS (asm_full_simp_tac (simpset_of thy8 addsimps
              (abs_supp @ supp_atm @
               PureThy.get_thms thy8 (Name ("fs_" ^ Sign.base_name atom ^ "1")) @
               List.concat supp_thms))))),
         length new_type_names))
      end) atoms;

    val simp_atts = replicate (length new_type_names) [Simplifier.simp_add];

    val (_, thy9) = thy8 |>
      Theory.add_path big_name |>
      PureThy.add_thms [(("induct_weak", dt_induct), [case_names_induct])] ||>>
      PureThy.add_thmss [(("inducts_weak", projections dt_induct), [case_names_induct])] ||>
      Theory.parent_path ||>>
      DatatypeAux.store_thmss_atts "distinct" new_type_names simp_atts distinct_thms ||>>
      DatatypeAux.store_thmss "constr_rep" new_type_names constr_rep_thmss ||>>
      DatatypeAux.store_thmss_atts "perm" new_type_names simp_atts perm_simps' ||>>
      DatatypeAux.store_thmss "inject" new_type_names inject_thms ||>>
      DatatypeAux.store_thmss "supp" new_type_names supp_thms ||>>
      DatatypeAux.store_thmss_atts "fresh" new_type_names simp_atts fresh_thms ||>
      fold (fn (atom, ths) => fn thy =>
        let val class = Sign.intern_class thy ("fs_" ^ Sign.base_name atom)
        in fold (fn T => AxClass.prove_arity
            (fst (dest_Type T),
              replicate (length sorts) [class], [class])
            (ClassPackage.intro_classes_tac [] THEN resolve_tac ths 1)) newTs thy
        end) (atoms ~~ finite_supp_thms);

    (**** strong induction theorem ****)

    val pnames = if length descr'' = 1 then ["P"]
      else map (fn i => "P" ^ string_of_int i) (1 upto length descr'');
    val ind_sort = if null dt_atomTs then HOLogic.typeS
      else Sign.certify_sort thy9 (map (fn T => Sign.intern_class thy9 ("fs_" ^
        Sign.base_name (fst (dest_Type T)))) dt_atomTs);
    val fsT = TFree ("'n", ind_sort);
    val fsT' = TFree ("'n", HOLogic.typeS);

    val fresh_fs = map (fn (s, T) => (T, Free (s, fsT' --> HOLogic.mk_setT T)))
      (DatatypeProp.indexify_names (replicate (length dt_atomTs) "f") ~~ dt_atomTs);

    fun make_pred fsT i T =
      Free (List.nth (pnames, i), fsT --> T --> HOLogic.boolT);

    fun make_ind_prem fsT f k T ((cname, cargs), idxs) =
      let
        val recs = List.filter is_rec_type cargs;
        val Ts = map (typ_of_dtyp descr'' sorts') cargs;
        val recTs' = map (typ_of_dtyp descr'' sorts') recs;
        val tnames = variantlist (DatatypeProp.make_tnames Ts, pnames);
        val rec_tnames = map fst (List.filter (is_rec_type o snd) (tnames ~~ cargs));
        val frees = tnames ~~ Ts;
        val frees' = partition_cargs idxs frees;
        val z = (variant tnames "z", fsT);

        fun mk_prem ((dt, s), T) =
          let
            val (Us, U) = strip_type T;
            val l = length Us
          in list_all (z :: map (pair "x") Us, HOLogic.mk_Trueprop
            (make_pred fsT (body_index dt) U $ Bound l $ app_bnds (Free (s, T)) l))
          end;

        fun mk_fresh1 xs [] = []
          | mk_fresh1 xs ((y as (_, T)):: ys) = map (fn x => HOLogic.mk_Trueprop
                (HOLogic.mk_not (HOLogic.mk_eq (Free y, Free x))))
                  (filter (fn (_, U) => T = U) (rev xs)) @
              mk_fresh1 (y :: xs) ys;

        fun mk_fresh2 xss [] = []
          | mk_fresh2 xss ((p as (ys, _)) :: yss) = List.concat (map (fn y as (_, T) =>
                map (fn (_, x as (_, U)) => HOLogic.mk_Trueprop
                  (Const ("Nominal.fresh", T --> U --> HOLogic.boolT) $ Free y $ Free x))
                    (rev xss @ yss)) ys) @
              mk_fresh2 (p :: xss) yss;

        val prems = map mk_prem (recs ~~ rec_tnames ~~ recTs');
        val prems' = map (fn p as (_, T) => HOLogic.mk_Trueprop
            (f T (Free p) (Free z))) (List.concat (map fst frees')) @
          mk_fresh1 [] (List.concat (map fst frees')) @
          mk_fresh2 [] frees'

      in list_all_free (frees @ [z], Logic.list_implies (prems' @ prems,
        HOLogic.mk_Trueprop (make_pred fsT k T $ Free z $
          list_comb (Const (cname, Ts ---> T), map Free frees))))
      end;

    val ind_prems = List.concat (map (fn (((i, (_, _, constrs)), (_, idxss)), T) =>
      map (make_ind_prem fsT (fn T => fn t => fn u =>
        Const ("Nominal.fresh", T --> fsT --> HOLogic.boolT) $ t $ u) i T)
          (constrs ~~ idxss)) (descr'' ~~ ndescr ~~ recTs));
    val tnames = DatatypeProp.make_tnames recTs;
    val zs = variantlist (replicate (length descr'') "z", tnames);
    val ind_concl = HOLogic.mk_Trueprop (foldr1 (HOLogic.mk_binop "op &")
      (map (fn ((((i, _), T), tname), z) =>
        make_pred fsT i T $ Free (z, fsT) $ Free (tname, T))
        (descr'' ~~ recTs ~~ tnames ~~ zs)));
    val induct = Logic.list_implies (ind_prems, ind_concl);

    val ind_prems' =
      map (fn (_, f as Free (_, T)) => list_all_free ([("x", fsT')],
        HOLogic.mk_Trueprop (HOLogic.mk_mem (f $ Free ("x", fsT'),
          Const ("Finite_Set.Finites", HOLogic.mk_setT (body_type T)))))) fresh_fs @
      List.concat (map (fn (((i, (_, _, constrs)), (_, idxss)), T) =>
        map (make_ind_prem fsT' (fn T => fn t => fn u => HOLogic.Not $
          HOLogic.mk_mem (t, the (AList.lookup op = fresh_fs T) $ u)) i T)
            (constrs ~~ idxss)) (descr'' ~~ ndescr ~~ recTs));
    val ind_concl' = HOLogic.mk_Trueprop (foldr1 (HOLogic.mk_binop "op &")
      (map (fn ((((i, _), T), tname), z) =>
        make_pred fsT' i T $ Free (z, fsT') $ Free (tname, T))
        (descr'' ~~ recTs ~~ tnames ~~ zs)));
    val induct' = Logic.list_implies (ind_prems', ind_concl');

    fun mk_perm Ts (t, u) =
      let
        val T = fastype_of1 (Ts, t);
        val U = fastype_of1 (Ts, u)
      in Const ("Nominal.perm", T --> U --> U) $ t $ u end;

    val aux_ind_vars =
      (DatatypeProp.indexify_names (replicate (length dt_atomTs) "pi") ~~
       map mk_permT dt_atomTs) @ [("z", fsT')];
    val aux_ind_Ts = rev (map snd aux_ind_vars);
    val aux_ind_concl = HOLogic.mk_Trueprop (foldr1 (HOLogic.mk_binop "op &")
      (map (fn (((i, _), T), tname) =>
        HOLogic.list_all (aux_ind_vars, make_pred fsT' i T $ Bound 0 $
          foldr (mk_perm aux_ind_Ts) (Free (tname, T))
            (map Bound (length dt_atomTs downto 1))))
        (descr'' ~~ recTs ~~ tnames)));

    fun mk_ind_perm i k p l vs j =
      let
        val n = length vs;
        val Ts = map snd vs;
        val T = List.nth (Ts, i - j);
        val pT = NominalAtoms.mk_permT T
      in
        Const ("List.list.Cons", HOLogic.mk_prodT (T, T) --> pT --> pT) $
          (HOLogic.pair_const T T $ Bound (l - j) $ foldr (mk_perm Ts)
            (Bound (i - j))
            (map (mk_ind_perm i k p l vs) (j - 1 downto 0) @
             map Bound (n - k - 1 downto n - k - p))) $
          Const ("List.list.Nil", pT)
      end;

    fun mk_fresh i i' j k p l is vs _ _ =
      let
        val n = length vs;
        val Ts = map snd vs;
        val T = List.nth (Ts, n - i - 1 - j);
        val f = the (AList.lookup op = fresh_fs T);
        val U = List.nth (Ts, n - i' - 1);
        val S = HOLogic.mk_setT T;
        val prms' = map Bound (n - k downto n - k - p + 1);
        val prms = map (mk_ind_perm (n - i) k p (n - l) (("a", T) :: vs))
            (j - 1 downto 0) @ prms';
        val bs = rev (List.mapPartial
          (fn ((_, T'), i) => if T = T' then SOME (Bound i) else NONE)
          (List.take (vs, n - k - p - 1) ~~ (1 upto n - k - p - 1)));
        val ts = map (fn i =>
          Const ("Nominal.supp", List.nth (Ts, n - i - 1) --> S) $
            foldr (mk_perm (T :: Ts)) (Bound (n - i)) prms') is
      in
        HOLogic.mk_Trueprop (Const ("Ex", (T --> HOLogic.boolT) --> HOLogic.boolT) $
          Abs ("a", T, HOLogic.Not $
            (Const ("op :", T --> S --> HOLogic.boolT) $ Bound 0 $
              (foldr (fn (t, u) => Const ("insert", T --> S --> S) $ t $ u)
                (foldl (fn (t, u) => Const ("op Un", S --> S --> S) $ u $ t)
                  (f $ Bound (n - k - p))
                  (Const ("Nominal.supp", U --> S) $
                     foldr (mk_perm (T :: Ts)) (Bound (n - i')) prms :: ts))
                (foldr (mk_perm (T :: Ts)) (Bound (n - i - j)) prms :: bs)))))
      end;

    fun mk_fresh_constr is p vs _ concl =
      let
        val n = length vs;
        val Ts = map snd vs;
        val _ $ (_ $ _ $ t) = concl;
        val c = head_of t;
        val T = body_type (fastype_of c);
        val k = foldr op + 0 (map (fn (_, i) => i + 1) is);
        val ps = map Bound (n - k - 1 downto n - k - p);
        val (_, _, ts, us) = foldl (fn ((_, i), (m, n, ts, us)) =>
          (m - i - 1, n - i,
           ts @ map Bound (n downto n - i + 1) @
             [foldr (mk_perm Ts) (Bound (m - i))
                (map (mk_ind_perm m k p n vs) (i - 1 downto 0) @ ps)],
           us @ map (fn j => foldr (mk_perm Ts) (Bound j) ps) (m downto m - i)))
          (n - 1, n - k - p - 2, [], []) is
      in
        HOLogic.mk_Trueprop (HOLogic.eq_const T $ list_comb (c, ts) $ list_comb (c, us))
      end;

    val abs_fun_finite_supp = PureThy.get_thm thy9 (Name "abs_fun_finite_supp");

    val at_finite_select = PureThy.get_thm thy9 (Name "at_finite_select");

    val induct_aux_lemmas = List.concat (map (fn Type (s, _) =>
      [PureThy.get_thm thy9 (Name ("pt_" ^ Sign.base_name s ^ "_inst")),
       PureThy.get_thm thy9 (Name ("fs_" ^ Sign.base_name s ^ "1")),
       PureThy.get_thm thy9 (Name ("at_" ^ Sign.base_name s ^ "_inst"))]) dt_atomTs);

    val induct_aux_lemmas' = map (fn Type (s, _) =>
      PureThy.get_thm thy9 (Name ("pt_" ^ Sign.base_name s ^ "2")) RS sym) dt_atomTs;

    val fresh_aux = PureThy.get_thms thy9 (Name "fresh_aux");

    (**********************************************************************
      The subgoals occurring in the proof of induct_aux have the
      following parameters:

        x_1 ... x_k p_1 ... p_m z b_1 ... b_n

      where

        x_i : constructor arguments (introduced by weak induction rule)
        p_i : permutations (one for each atom type in the data type)
        z   : freshness context
        b_i : newly introduced names for binders (sufficiently fresh)
    ***********************************************************************)

    val _ = warning "proving strong induction theorem ...";

    val induct_aux = standard (Goal.prove thy9 [] ind_prems' ind_concl'
      (fn prems => EVERY
        ([mk_subgoal 1 (K (K (K aux_ind_concl))),
          indtac dt_induct tnames 1] @
         List.concat (map (fn ((_, (_, _, constrs)), (_, constrs')) =>
           List.concat (map (fn ((cname, cargs), is) =>
             [simp_tac (HOL_basic_ss addsimps List.concat perm_simps') 1,
              REPEAT (rtac allI 1)] @
             List.concat (map
               (fn ((_, 0), _) => []
                 | ((i, j), k) => List.concat (map (fn j' =>
                     let
                       val DtType (tname, _) = List.nth (cargs, i + j');
                       val atom = Sign.base_name tname
                     in
                       [mk_subgoal 1 (mk_fresh i (i + j) j'
                          (length cargs) (length dt_atomTs)
                          (length cargs + length dt_atomTs + 1 + i - k)
                          (List.mapPartial (fn (i', j) =>
                             if i = i' then NONE else SOME (i' + j)) is)),
                        rtac at_finite_select 1,
                        rtac (PureThy.get_thm thy9 (Name ("at_" ^ atom ^ "_inst"))) 1,
                        asm_full_simp_tac (simpset_of thy9 addsimps
                          [PureThy.get_thm thy9 (Name ("fs_" ^ atom ^ "1"))]) 1,
                        resolve_tac prems 1,
                        etac exE 1,
                        asm_full_simp_tac (simpset_of thy9 addsimps
                          [symmetric fresh_def]) 1]
                     end) (0 upto j - 1))) (is ~~ (0 upto length is - 1))) @
             (if exists (not o equal 0 o snd) is then
                [mk_subgoal 1 (mk_fresh_constr is (length dt_atomTs)),
                 asm_full_simp_tac (simpset_of thy9 addsimps
                   (List.concat inject_thms @
                    alpha @ abs_perm @ abs_fresh @ [abs_fun_finite_supp] @
                    induct_aux_lemmas)) 1,
                 dtac sym 1,
                 asm_full_simp_tac (simpset_of thy9) 1,
                 REPEAT (etac conjE 1)]
              else
                []) @
             [(resolve_tac prems THEN_ALL_NEW
                (atac ORELSE'
                  SUBGOAL (fn (t, i) => case Logic.strip_assums_concl t of
                      _ $ (Const ("Nominal.fresh", _) $ _ $ _) =>
                        asm_simp_tac (simpset_of thy9 addsimps fresh_aux) i
                    | _ =>
                        asm_simp_tac (simpset_of thy9
                        addsimps induct_aux_lemmas'
                        addsimprocs [perm_simproc]) i))) 1])
               (constrs ~~ constrs'))) (descr'' ~~ ndescr)) @
         [REPEAT (eresolve_tac [conjE, allE_Nil] 1),
          REPEAT (etac allE 1),
          REPEAT (TRY (rtac conjI 1) THEN asm_full_simp_tac (simpset_of thy9) 1)])));

    val induct_aux' = Thm.instantiate ([],
      map (fn (s, T) =>
        let val pT = TVar (("'n", 0), HOLogic.typeS) --> T --> HOLogic.boolT
        in (cterm_of thy9 (Var ((s, 0), pT)), cterm_of thy9 (Free (s, pT))) end)
          (pnames ~~ recTs) @
      map (fn (_, f) =>
        let val f' = Logic.varify f
        in (cterm_of thy9 f',
          cterm_of thy9 (Const ("Nominal.supp", fastype_of f')))
        end) fresh_fs) induct_aux;

    val induct = standard (Goal.prove thy9 [] ind_prems ind_concl
      (fn prems => EVERY
         [rtac induct_aux' 1,
          REPEAT (resolve_tac induct_aux_lemmas 1),
          REPEAT ((resolve_tac prems THEN_ALL_NEW
            (etac meta_spec ORELSE' full_simp_tac (HOL_basic_ss addsimps [fresh_def]))) 1)]))

    val (_, thy10) = thy9 |>
      Theory.add_path big_name |>
      PureThy.add_thms [(("induct'", induct_aux), [])] ||>>
      PureThy.add_thms [(("induct", induct), [case_names_induct])] ||>>
      PureThy.add_thmss [(("inducts", projections induct), [case_names_induct])] ||>
      Theory.parent_path;

    (**** recursion combinator ****)

    val _ = warning "defining recursion combinator ...";

    val used = foldr add_typ_tfree_names [] recTs;

    val (rec_result_Ts, rec_fn_Ts) = DatatypeProp.make_primrec_Ts descr' sorts' used;

    val permTs = map mk_permT dt_atomTs;
    val perms = map Free
      (DatatypeProp.indexify_names (replicate (length permTs) "pi") ~~ permTs);

    val rec_set_Ts = map (fn (T1, T2) => rec_fn_Ts ---> HOLogic.mk_setT
      (HOLogic.mk_prodT (T1, permTs ---> T2))) (recTs ~~ rec_result_Ts);

    val big_rec_name = big_name ^ "_rec_set";
    val rec_set_names = map (Sign.full_name (Theory.sign_of thy10))
      (if length descr'' = 1 then [big_rec_name] else
        (map ((curry (op ^) (big_rec_name ^ "_")) o string_of_int)
          (1 upto (length descr''))));

    val rec_fns = map (uncurry (mk_Free "f"))
      (rec_fn_Ts ~~ (1 upto (length rec_fn_Ts)));
    val rec_sets = map (fn c => list_comb (Const c, rec_fns))
      (rec_set_names ~~ rec_set_Ts);

    (* introduction rules for graph of recursion function *)

    fun mk_fresh_fun (a, t) = Const ("Nominal.fresh_fun",
      (fastype_of a --> fastype_of t) --> fastype_of t) $ lambda a t;

    fun make_rec_intr T rec_set ((rec_intr_ts, l), ((cname, cargs), idxs)) =
      let
        fun mk_prem ((dts, (dt, U)), (j, k, prems, t1s, t2s, t3s, atoms)) =
          let
            val free1 = mk_Free "x" U (j + length dts);
            val Us = map snd dts;
            val xs = Us ~~ (j upto j + length dts - 1);
            val frees = map (uncurry (mk_Free "x")) xs;
            val frees' = map (uncurry (mk_Free "x'")) xs;
            val frees'' = Us ~~ (frees ~~ frees');
            val pis = map (fn (T, p) =>
              case filter (equal T o fst) frees'' of
                [] => p
              | xs => HOLogic.mk_binop "List.op @" (p,
                HOLogic.mk_list (HOLogic.mk_prod o snd)
                  (HOLogic.mk_prodT (T, T)) xs))
                  (dt_atomTs ~~ perms)
          in (case dt of
             DtRec m =>
               let val free2 = mk_Free "y"
                 (permTs ---> List.nth (rec_result_Ts, m)) k
               in (j + length dts + 1, k + 1,
                   HOLogic.mk_Trueprop
                     (HOLogic.mk_mem (HOLogic.mk_prod
                       (free1, free2),
                         List.nth (rec_sets, m))) :: prems,
                   frees @ free1 :: t1s,
                   frees' @ foldr (mk_perm []) free1 pis :: t2s,
                   list_comb (free2, pis) :: t3s,
                   frees' @ atoms)
               end
           | _ => (j + length dts + 1, k, prems,
               frees @ free1 :: t1s,
               frees' @ foldr (mk_perm []) free1 pis :: t2s,
               t3s,
               frees' @ atoms))
          end;

        val Ts = map (typ_of_dtyp descr'' sorts') cargs;
        val (_, _, prems, t1s, t2s, t3s, atoms) = foldr mk_prem (1, 1, [], [], [], [], [])
          (partition_cargs idxs (cargs ~~ Ts))

      in (rec_intr_ts @ [Logic.list_implies (prems, HOLogic.mk_Trueprop (HOLogic.mk_mem
        (HOLogic.mk_prod (list_comb (Const (cname, Ts ---> T), t1s),
          foldr (uncurry lambda)
            (foldr mk_fresh_fun
              (list_comb (List.nth (rec_fns, l), t2s @ t3s)) atoms)
            perms), rec_set)))], l + 1)
      end;

    val (rec_intr_ts, _) = Library.foldl (fn (x, (((d, d'), T), rec_set)) =>
      Library.foldl (make_rec_intr T rec_set) (x, #3 (snd d) ~~ snd d'))
        (([], 0), descr'' ~~ ndescr ~~ recTs ~~ rec_sets);

    val (thy11, {intrs = rec_intrs, elims = rec_elims, ...}) =
      setmp InductivePackage.quiet_mode (!quiet_mode)
        (InductivePackage.add_inductive_i false true big_rec_name false false false
           rec_sets (map (fn x => (("", x), [])) rec_intr_ts) []) thy10;

  in
    thy11
  end;

val add_nominal_datatype = gen_add_nominal_datatype read_typ true;


(* FIXME: The following stuff should be exported by DatatypePackage *)

local structure P = OuterParse and K = OuterKeyword in

val datatype_decl =
  Scan.option (P.$$$ "(" |-- P.name --| P.$$$ ")") -- P.type_args -- P.name -- P.opt_infix --
    (P.$$$ "=" |-- P.enum1 "|" (P.name -- Scan.repeat P.typ -- P.opt_mixfix));

fun mk_datatype args =
  let
    val names = map (fn ((((NONE, _), t), _), _) => t | ((((SOME t, _), _), _), _) => t) args;
    val specs = map (fn ((((_, vs), t), mx), cons) =>
      (vs, t, mx, map (fn ((x, y), z) => (x, y, z)) cons)) args;
  in add_nominal_datatype false names specs end;

val nominal_datatypeP =
  OuterSyntax.command "nominal_datatype" "define inductive datatypes" K.thy_decl
    (P.and_list1 datatype_decl >> (Toplevel.theory o mk_datatype));

val _ = OuterSyntax.add_parsers [nominal_datatypeP];

end;

end

