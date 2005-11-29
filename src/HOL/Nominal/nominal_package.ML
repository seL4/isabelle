(* $Id$ *)

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
    val bnames = map the_bname (distinct (List.concat (map dt_recs args)));
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

    fun replace_types (Type ("nominal.ABS", [T, U])) = 
          Type ("fun", [T, Type ("nominal.nOption", [replace_types U])])
      | replace_types (Type (s, Ts)) =
          Type (getOpt (AList.lookup op = ps s, s), map replace_types Ts)
      | replace_types T = T;

    fun replace_types' (Type (s, Ts)) =
          Type (getOpt (AList.lookup op = rps s, s), map replace_types' Ts)
      | replace_types' T = T;

    val dts'' = map (fn (tvs, tname, mx, constrs) => (tvs, tname ^ "_Rep", NoSyn,
      map (fn (cname, cargs, mx) => (cname,
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
    val perm_names = replicate (length new_type_names) "nominal.perm" @
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
                      Const ("nominal.perm", permT --> U --> U) $
                        (Const ("List.rev", permT --> permT) $ pi) $
                        Bound i) ((length Us - 1 downto 0) ~~ Us)))
                end
              else Const ("nominal.perm", permT --> T --> T) $ pi $ x
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
      PrimrecPackage.add_primrec_i "" perm_eqs;

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
                 Const ("nominal.perm", T) $ pi $ Free (x, T2))
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
             (HOLogic.mk_Trueprop (Const ("nominal.prm_eq",
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
                    val perm3 = Const ("nominal.perm", permT1 --> permT2 --> permT2)
                  in HOLogic.mk_eq
                    (perm1 $ pi1 $ (perm2 $ pi2 $ Free (x, T)),
                     perm2 $ (perm3 $ pi1 $ pi2) $ (perm1 $ pi1 $ Free (x, T)))
                  end)
                (perm_names ~~ Ts ~~ perm_indnames))))
          (fn _ => EVERY [indtac induction perm_indnames 1,
             ALLGOALS (asm_full_simp_tac simps)])))
      in
        foldl (fn ((s, tvs), thy) => AxClass.add_inst_arity_i
            (s, replicate (length tvs) (cp_class :: classes), [cp_class])
            (AxClass.intro_classes_tac [] THEN ALLGOALS (resolve_tac thms)) thy)
          thy (full_new_type_names' ~~ tyvars)
      end;

    val (thy3, perm_thmss) = thy2 |>
      fold (fn name1 => fold (composition_instance name1) atoms) atoms |>
      curry (Library.foldr (fn ((i, (tyname, args, _)), thy) =>
        AxClass.add_inst_arity_i (tyname, replicate (length args) classes, classes)
        (AxClass.intro_classes_tac [] THEN REPEAT (EVERY
           [resolve_tac perm_empty_thms 1,
            resolve_tac perm_append_thms 1,
            resolve_tac perm_eq_thms 1, assume_tac 1])) thy))
        (List.take (descr, length new_type_names)) |>
      PureThy.add_thmss
        [((space_implode "_" new_type_names ^ "_unfolded_perm_eq",
          unfolded_perm_eq_thms), [Simplifier.simp_add_global]),
         ((space_implode "_" new_type_names ^ "_perm_empty",
          perm_empty_thms), [Simplifier.simp_add_global]),
         ((space_implode "_" new_type_names ^ "_perm_append",
          perm_append_thms), [Simplifier.simp_add_global]),
         ((space_implode "_" new_type_names ^ "_perm_eq",
          perm_eq_thms), [Simplifier.simp_add_global])];
  
    (**** Define representing sets ****)

    val _ = warning "representing sets";

    val rep_set_names = map (Sign.full_name thy3) (DatatypeProp.indexify_names
      (map (fn (i, _) => name_of_typ (nth_dtyp i) ^ "_set") descr));
    val big_rep_name =
      space_implode "_" (DatatypeProp.indexify_names (List.mapPartial
        (fn (i, ("nominal.nOption", _, _)) => NONE
          | (i, _) => SOME (name_of_typ (nth_dtyp i))) descr)) ^ "_set";
    val _ = warning ("big_rep_name: " ^ big_rep_name);

    fun strip_option (dtf as DtType ("fun", [dt, DtRec i])) =
          (case AList.lookup op = descr i of
             SOME ("nominal.nOption", _, [(_, [dt']), _]) =>
               apfst (cons dt) (strip_option dt')
           | _ => ([], dtf))
      | strip_option (DtType ("fun", [dt, DtType ("nominal.nOption", [dt'])])) =
          apfst (cons dt) (strip_option dt')
      | strip_option dt = ([], dt);

    val dt_atomTs = distinct (map (typ_of_dtyp descr sorts')
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
              in (i + 1, Const ("nominal.abs_fun", [T, U, T] --->
                Type ("nominal.nOption", [U])) $ mk_Free "y" T i $ t)
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
        (fn ((_, ("nominal.nOption", _, _)), _) => NONE
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
      (fn (x, (_, ("nominal.nOption", _, _))) => NONE | (x, _) => SOME x)
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
                HOLogic.mk_mem (Const ("nominal.perm", permT --> T --> T) $
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
    val (thy5, _) = PureThy.add_thmss [(("perm_closed",
      List.concat perm_closed_thmss), [])] thy4;

    (**** typedef ****)

    val _ = warning "defining type...";

    val (thy6, typedefs) =
      foldl_map (fn (thy, ((((name, mx), tvs), c), name')) =>
        setmp TypedefPackage.quiet_mode true
          (TypedefPackage.add_typedef_i false (SOME name') (name, tvs, mx) c NONE
            (rtac exI 1 THEN
              QUIET_BREADTH_FIRST (has_fewer_prems 1)
              (resolve_tac rep_intrs 1))) thy |> (fn (thy, r) =>
        let
          val permT = mk_permT (TFree (variant tvs "'a", HOLogic.typeS));
          val pi = Free ("pi", permT);
          val tvs' = map (fn s => TFree (s, the (AList.lookup op = sorts' s))) tvs;
          val T = Type (Sign.intern_type thy name, tvs');
          val Const (_, Type (_, [U])) = c
        in apsnd (pair r o hd)
          (PureThy.add_defs_i true [(("prm_" ^ name ^ "_def", Logic.mk_equals
            (Const ("nominal.perm", permT --> T --> T) $ pi $ Free ("x", T),
             Const (Sign.intern_const thy ("Abs_" ^ name), U --> T) $
               (Const ("nominal.perm", permT --> U --> U) $ pi $
                 (Const (Sign.intern_const thy ("Rep_" ^ name), T --> U) $
                   Free ("x", T))))), [])] thy)
        end))
          (thy5, types_syntax ~~ tyvars ~~
            (List.take (ind_consts, length new_type_names)) ~~ new_type_names);

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
          AxClass.add_inst_arity_i
            (Sign.intern_type thy name,
              replicate (length tvs) (classes @ cp_classes), [class])
            (EVERY [AxClass.intro_classes_tac [],
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
          AxClass.add_inst_arity_i
            (Sign.intern_type thy name,
              replicate (length tvs) (classes @ cp_classes), [class])
            (EVERY [AxClass.intro_classes_tac [],
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
        Const ("nominal.abs_fun", T --> U --> T -->
          Type ("nominal.nOption", [U])) $ x $ t
      end;

    val (ty_idxs, _) = foldl
      (fn ((i, ("nominal.nOption", _, _)), p) => p
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
      (fn (i, ("nominal.nOption", _, _)) => NONE
        | (i, (s, dts, constrs)) =>
             let
               val SOME index = AList.lookup op = ty_idxs i;
               val (constrs1, constrs2) = ListPair.unzip
                 (map (fn (cname, cargs) => apfst (pair (strip_nth_name 2 cname))
                   (foldl_map (fn (dts, dt) =>
                     let val (dts', dt') = strip_option dt
                     in (dts @ dts' @ [reindex dt'], (length dts, length dts')) end)
                       ([], cargs))) constrs)
             in SOME ((index, (strip_nth_name 1 s,  map reindex dts, constrs1)),
               (index, constrs2))
             end) descr);

    val (descr1, descr2) = splitAt (length new_type_names, descr'');
    val descr' = [descr1, descr2];

    val typ_of_dtyp' = replace_types' o typ_of_dtyp descr sorts';

    val rep_names = map (fn s =>
      Sign.intern_const thy7 ("Rep_" ^ s)) new_type_names;
    val abs_names = map (fn s =>
      Sign.intern_const thy7 ("Abs_" ^ s)) new_type_names;

    val recTs' = List.mapPartial
      (fn ((_, ("nominal.nOption", _, _)), T) => NONE
        | (_, T) => SOME T) (descr ~~ get_rec_types descr sorts');
    val recTs = get_rec_types descr'' sorts';
    val newTs' = Library.take (length new_type_names, recTs');
    val newTs = Library.take (length new_type_names, recTs);

    val full_new_type_names = map (Sign.full_name (sign_of thy)) new_type_names;

    fun make_constr_def tname T T' ((thy, defs, eqns), ((cname, cargs), (cname', mx))) =
      let
        fun constr_arg (dt, (j, l_args, r_args)) =
          let
            val x' = mk_Free "x" (typ_of_dtyp' dt) j;
            val (dts, dt') = strip_option dt;
            val xs = map (fn (dt, i) => mk_Free "x" (typ_of_dtyp' dt) i)
              (dts ~~ (j upto j + length dts - 1))
            val x = mk_Free "x" (typ_of_dtyp' dt') (j + length dts)
            val (dts', dt'') = strip_dtyp dt'
          in
            (j + length dts + 1,
             xs @ x :: l_args,
             foldr mk_abs_fun
               (case dt'' of
                  DtRec k => if k < length new_type_names then
                      list_abs (map (pair "z" o typ_of_dtyp') dts',
                        Const (List.nth (rep_names, k), typ_of_dtyp' dt'' -->
                          typ_of_dtyp descr sorts' dt'') $ app_bnds x (length dts'))
                    else error "nested recursion not (yet) supported"
                | _ => x) xs :: r_args)
          end

        val (_, l_args, r_args) = foldr constr_arg (1, [], []) cargs;
        val abs_name = Sign.intern_const (Theory.sign_of thy) ("Abs_" ^ tname);
        val rep_name = Sign.intern_const (Theory.sign_of thy) ("Rep_" ^ tname);
        val constrT = map fastype_of l_args ---> T;
        val lhs = list_comb (Const (Sign.full_name thy (Sign.base_name cname),
          constrT), l_args);
        val rhs = list_comb (Const (cname, map fastype_of r_args ---> T'), r_args);
        val def = Logic.mk_equals (lhs, Const (abs_name, T' --> T) $ rhs);
        val eqn = HOLogic.mk_Trueprop (HOLogic.mk_eq
          (Const (rep_name, T --> T') $ lhs, rhs));
        val def_name = (Sign.base_name cname) ^ "_def";
        val (thy', [def_thm]) = thy |>
          Theory.add_consts_i [(cname', constrT, mx)] |>
          (PureThy.add_defs_i false o map Thm.no_attributes) [(def_name, def)]
      in (thy', defs @ [def_thm], eqns @ [eqn]) end;

    fun dt_constr_defs ((thy, defs, eqns, dist_lemmas),
        (((((_, (_, _, constrs)), tname), T), T'), constr_syntax)) =
      let
        val rep_const = cterm_of thy
          (Const (Sign.intern_const thy ("Rep_" ^ tname), T --> T'));
        val dist = standard (cterm_instantiate [(cterm_of thy distinct_f, rep_const)] distinct_lemma);
        val (thy', defs', eqns') = Library.foldl (make_constr_def tname T T')
          ((Theory.add_path tname thy, defs, []), constrs ~~ constr_syntax)
      in
        (parent_path flat_names thy', defs', eqns @ [eqns'], dist_lemmas @ [dist])
      end;

    val (thy8, constr_defs, constr_rep_eqns, dist_lemmas) = Library.foldl dt_constr_defs
      ((thy7, [], [], []), List.take (descr, length new_type_names) ~~
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
            (Const ("nominal.perm", permT --> U --> U) $ pi $ (Rep $ x),
             Rep $ (Const ("nominal.perm", permT --> T --> T) $ pi $ x))))
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
      let val T = replace_types' (nth_dtyp i)
      in List.concat (map (fn (atom, perm_closed_thms) =>
          map (fn ((cname, dts), constr_rep_thm) => 
        let
          val cname = Sign.intern_const thy8
            (NameSpace.append tname (Sign.base_name cname));
          val permT = mk_permT (Type (atom, []));
          val pi = Free ("pi", permT);

          fun perm t =
            let val T = fastype_of t
            in Const ("nominal.perm", permT --> T --> T) $ pi $ t end;

          fun constr_arg (dt, (j, l_args, r_args)) =
            let
              val x' = mk_Free "x" (typ_of_dtyp' dt) j;
              val (dts, dt') = strip_option dt;
              val Ts = map typ_of_dtyp' dts;
              val xs = map (fn (T, i) => mk_Free "x" T i)
                (Ts ~~ (j upto j + length dts - 1))
              val x = mk_Free "x" (typ_of_dtyp' dt') (j + length dts);
              val (dts', dt'') = strip_dtyp dt';
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
      end) (List.take (descr, length new_type_names) ~~ new_type_names ~~ constr_rep_thmss);

    (** prove injectivity of constructors **)

    val rep_inject_thms' = map (fn th => th RS sym) rep_inject_thms;
    val alpha = PureThy.get_thms thy8 (Name "alpha");
    val abs_fresh = PureThy.get_thms thy8 (Name "abs_fresh");
    val fresh_def = PureThy.get_thm thy8 (Name "fresh_def");
    val supp_def = PureThy.get_thm thy8 (Name "supp_def");

    val inject_thms = map (fn (((i, (_, _, constrs)), tname), constr_rep_thms) =>
      let val T = replace_types' (nth_dtyp i)
      in List.mapPartial (fn ((cname, dts), constr_rep_thm) =>
        if null dts then NONE else SOME
        let
          val cname = Sign.intern_const thy8
            (NameSpace.append tname (Sign.base_name cname));

          fun make_inj (dt, (j, args1, args2, eqs)) =
            let
              val x' = mk_Free "x" (typ_of_dtyp' dt) j;
              val y' = mk_Free "y" (typ_of_dtyp' dt) j;
              val (dts, dt') = strip_option dt;
              val Ts_idx = map typ_of_dtyp' dts ~~ (j upto j + length dts - 1);
              val xs = map (fn (T, i) => mk_Free "x" T i) Ts_idx;
              val ys = map (fn (T, i) => mk_Free "y" T i) Ts_idx;
              val x = mk_Free "x" (typ_of_dtyp' dt') (j + length dts);
              val y = mk_Free "y" (typ_of_dtyp' dt') (j + length dts);
              val (dts', dt'') = strip_dtyp dt';
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
      end) (List.take (descr, length new_type_names) ~~ new_type_names ~~ constr_rep_thmss);

    (** equations for support and freshness **)

    val Un_assoc = PureThy.get_thm thy8 (Name "Un_assoc");
    val de_Morgan_conj = PureThy.get_thm thy8 (Name "de_Morgan_conj");
    val Collect_disj_eq = PureThy.get_thm thy8 (Name "Collect_disj_eq");
    val finite_Un = PureThy.get_thm thy8 (Name "finite_Un");

    val (supp_thms, fresh_thms) = ListPair.unzip (map ListPair.unzip
      (map (fn ((((i, (_, _, constrs)), tname), inject_thms'), perm_thms') =>
      let val T = replace_types' (nth_dtyp i)
      in List.concat (map (fn (cname, dts) => map (fn atom =>
        let
          val cname = Sign.intern_const thy8
            (NameSpace.append tname (Sign.base_name cname));
          val atomT = Type (atom, []);

          fun process_constr (dt, (j, args1, args2)) =
            let
              val x' = mk_Free "x" (typ_of_dtyp' dt) j;
              val (dts, dt') = strip_option dt;
              val Ts_idx = map typ_of_dtyp' dts ~~ (j upto j + length dts - 1);
              val xs = map (fn (T, i) => mk_Free "x" T i) Ts_idx;
              val x = mk_Free "x" (typ_of_dtyp' dt') (j + length dts);
              val (dts', dt'') = strip_dtyp dt';
            in
              (j + length dts + 1,
               xs @ (x :: args1), foldr mk_abs_fun x xs :: args2)
            end;

          val (_, args1, args2) = foldr process_constr (1, [], []) dts;
          val Ts = map fastype_of args1;
          val c = list_comb (Const (cname, Ts ---> T), args1);
          fun supp t =
            Const ("nominal.supp", fastype_of t --> HOLogic.mk_setT atomT) $ t;
          fun fresh t =
            Const ("nominal.fresh", atomT --> fastype_of t --> HOLogic.boolT) $
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
      end) (List.take (descr, length new_type_names) ~~ new_type_names ~~ inject_thms ~~ perm_simps')));

    (**** weak induction theorem ****)

    val arities = get_arities descr'';

    fun mk_funs_inv thm =
      let
        val {sign, prop, ...} = rep_thm thm;
        val _ $ (_ $ (Const (_, Type (_, [U, _])) $ _ $ S)) $
          (_ $ (_ $ (r $ (a $ _)) $ _)) = Type.freeze prop;
        val used = add_term_tfree_names (a, []);

        fun mk_thm i =
          let
            val Ts = map (TFree o rpair HOLogic.typeS)
              (variantlist (replicate i "'t", used));
            val f = Free ("f", Ts ---> U)
          in standard (Goal.prove sign [] [] (Logic.mk_implies
            (HOLogic.mk_Trueprop (HOLogic.list_all
               (map (pair "x") Ts, HOLogic.mk_mem (app_bnds f i, S))),
             HOLogic.mk_Trueprop (HOLogic.mk_eq (list_abs (map (pair "x") Ts,
               r $ (a $ app_bnds f i)), f))))
            (fn _ => EVERY [REPEAT (rtac ext 1), REPEAT (etac allE 1), rtac thm 1, atac 1]))
          end
      in map (fn r => r RS subst) (thm :: map mk_thm arities) end;

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

    val Abs_inverse_thms' = List.concat (map mk_funs_inv Abs_inverse_thms);

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
             (Const ("nominal.supp", T --> HOLogic.mk_setT atomT) $ Free (s, T),
              Const ("Finite_Set.Finites", HOLogic.mk_setT (HOLogic.mk_setT atomT))))
               (indnames ~~ recTs))))
           (fn _ => indtac dt_induct indnames 1 THEN
            ALLGOALS (asm_full_simp_tac (simpset_of thy8 addsimps
              (abs_supp @ supp_atm @
               PureThy.get_thms thy8 (Name ("fs_" ^ Sign.base_name atom ^ "1")) @
               List.concat supp_thms))))),
         length new_type_names))
      end) atoms;

    (**** strong induction theorem ****)

    val pnames = if length descr'' = 1 then ["P"]
      else map (fn i => "P" ^ string_of_int i) (1 upto length descr'');
    val ind_sort = if null dt_atomTs then HOLogic.typeS
      else map (fn T => Sign.intern_class thy8 ("fs_" ^
        Sign.base_name (fst (dest_Type T)))) dt_atomTs;
    val fsT = TFree ("'n", ind_sort);

    fun make_pred i T =
      Free (List.nth (pnames, i), T --> fsT --> HOLogic.boolT);

    fun make_ind_prem k T ((cname, cargs), idxs) =
      let
        val recs = List.filter is_rec_type cargs;
        val Ts = map (typ_of_dtyp descr'' sorts') cargs;
        val recTs' = map (typ_of_dtyp descr'' sorts') recs;
        val tnames = variantlist (DatatypeProp.make_tnames Ts, pnames);
        val rec_tnames = map fst (List.filter (is_rec_type o snd) (tnames ~~ cargs));
        val frees = tnames ~~ Ts;
        val z = (variant tnames "z", fsT);

        fun mk_prem ((dt, s), T) =
          let
            val (Us, U) = strip_type T;
            val l = length Us
          in list_all (z :: map (pair "x") Us, HOLogic.mk_Trueprop
            (make_pred (body_index dt) U $ app_bnds (Free (s, T)) l $ Bound l))
          end;

        val prems = map mk_prem (recs ~~ rec_tnames ~~ recTs');
        val prems' = map (fn p as (_, T) => HOLogic.mk_Trueprop
            (Const ("nominal.fresh", T --> fsT --> HOLogic.boolT) $
              Free p $ Free z))
          (map (curry List.nth frees) (List.concat (map (fn (m, n) =>
             m upto m + n - 1) idxs)))

      in list_all_free (z :: frees, Logic.list_implies (prems' @ prems,
        HOLogic.mk_Trueprop (make_pred k T $ 
          list_comb (Const (cname, Ts ---> T), map Free frees) $ Free z)))
      end;

    val ind_prems = List.concat (map (fn (((i, (_, _, constrs)), (_, idxss)), T) =>
      map (make_ind_prem i T) (constrs ~~ idxss)) (descr'' ~~ ndescr ~~ recTs));
    val tnames = DatatypeProp.make_tnames recTs;
    val z = (variant tnames "z", fsT);
    val ind_concl = HOLogic.mk_Trueprop (foldr1 (HOLogic.mk_binop "op &")
      (map (fn (((i, _), T), tname) => make_pred i T $ Free (tname, T) $ Free z)
        (descr'' ~~ recTs ~~ tnames)));
    val induct = Logic.list_implies (ind_prems, ind_concl);

    val simp_atts = replicate (length new_type_names) [Simplifier.simp_add_global];

    val (thy9, _) = thy8 |>
      Theory.add_path big_name |>
      PureThy.add_thms [(("induct_weak", dt_induct), [case_names_induct])] |>>
      Theory.parent_path |>>>
      DatatypeAux.store_thmss_atts "distinct" new_type_names simp_atts distinct_thms |>>>
      DatatypeAux.store_thmss "constr_rep" new_type_names constr_rep_thmss |>>>
      DatatypeAux.store_thmss_atts "perm" new_type_names simp_atts perm_simps' |>>>
      DatatypeAux.store_thmss "inject" new_type_names inject_thms |>>>
      DatatypeAux.store_thmss "supp" new_type_names supp_thms |>>>
      DatatypeAux.store_thmss_atts "fresh" new_type_names simp_atts fresh_thms |>>
      fold (fn (atom, ths) => fn thy =>
        let val class = Sign.intern_class thy ("fs_" ^ Sign.base_name atom)
        in fold (fn T => AxClass.add_inst_arity_i
            (fst (dest_Type T),
              replicate (length sorts) [class], [class])
            (AxClass.intro_classes_tac [] THEN resolve_tac ths 1)) newTs thy
        end) (atoms ~~ finite_supp_thms) |>>
      Theory.add_path big_name |>>>
      PureThy.add_axioms_i [(("induct_unsafe", induct), [case_names_induct])] |>>
      Theory.parent_path;

  in
    thy9
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

