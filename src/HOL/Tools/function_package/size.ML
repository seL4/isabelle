(*  Title:      HOL/Tools/function_package/size.ML
    ID:         $Id$
    Author:     Stefan Berghofer, Florian Haftmann, TU Muenchen

Size functions for datatypes.
*)

signature SIZE =
sig
  val size_thms: theory -> string -> thm list
  val setup: theory -> theory
end;

structure Size: SIZE =
struct

open DatatypeAux;

structure SizeData = TheoryDataFun
(
  type T = (string * thm list) Symtab.table;
  val empty = Symtab.empty;
  val copy = I
  val extend = I
  fun merge _ = Symtab.merge (K true);
);

val lookup_size = SizeData.get #> Symtab.lookup;

fun plus (t1, t2) = Const ("HOL.plus_class.plus",
  HOLogic.natT --> HOLogic.natT --> HOLogic.natT) $ t1 $ t2;

fun size_of_type f g h (T as Type (s, Ts)) =
      (case f s of
         SOME t => SOME t
       | NONE => (case g s of
           SOME size_name =>
             SOME (list_comb (Const (size_name,
               map (fn U => U --> HOLogic.natT) Ts @ [T] ---> HOLogic.natT),
                 map (size_of_type' f g h) Ts))
         | NONE => NONE))
  | size_of_type f g h (TFree (s, _)) = h s
and size_of_type' f g h T = (case size_of_type f g h T of
      NONE => Abs ("x", T, HOLogic.zero)
    | SOME t => t);

fun is_poly thy (DtType (name, dts)) =
      (case DatatypePackage.get_datatype thy name of
         NONE => false
       | SOME _ => exists (is_poly thy) dts)
  | is_poly _ _ = true;

fun constrs_of thy name =
  let
    val {descr, index, ...} = DatatypePackage.the_datatype thy name
    val SOME (_, _, constrs) = AList.lookup op = descr index
  in constrs end;

val app = curry (list_comb o swap);

fun prove_size_thms (info : datatype_info) new_type_names thy =
  let
    val {descr, alt_names, sorts, rec_names, rec_rewrites, induction, ...} = info;
    val l = length new_type_names;
    val alt_names' = (case alt_names of
      NONE => replicate l NONE | SOME names => map SOME names);
    val descr' = List.take (descr, l);
    val (rec_names1, rec_names2) = chop l rec_names;
    val recTs = get_rec_types descr sorts;
    val (recTs1, recTs2) = chop l recTs;
    val (_, (_, paramdts, _)) :: _ = descr;
    val paramTs = map (typ_of_dtyp descr sorts) paramdts;
    val ((param_size_fs, param_size_fTs), f_names) = paramTs |>
      map (fn T as TFree (s, _) =>
        let
          val name = "f" ^ implode (tl (explode s));
          val U = T --> HOLogic.natT
        in
          (((s, Free (name, U)), U), name)
        end) |> split_list |>> split_list;
    val param_size = AList.lookup op = param_size_fs;

    val extra_rewrites = descr |> map (#1 o snd) |> distinct op = |>
      List.mapPartial (Option.map snd o lookup_size thy) |> flat;
    val extra_size = Option.map fst o lookup_size thy;

    val (((size_names, size_fns), def_names), def_names') =
      recTs1 ~~ alt_names' |>
      map (fn (T as Type (s, _), optname) =>
        let
          val s' = the_default (Sign.base_name s) optname ^ "_size";
          val s'' = Sign.full_name thy s'
        in
          (s'',
           (list_comb (Const (s'', param_size_fTs @ [T] ---> HOLogic.natT),
              map snd param_size_fs),
            (s' ^ "_def", s' ^ "_overloaded_def")))
        end) |> split_list ||>> split_list ||>> split_list;
    val overloaded_size_fns = map HOLogic.size_const recTs1;

    (* instantiation for primrec combinator *)
    fun size_of_constr b size_ofp ((_, cargs), (_, cargs')) =
      let
        val Ts = map (typ_of_dtyp descr sorts) cargs;
        val k = length (filter is_rec_type cargs);
        val (ts, _, _) = fold_rev (fn ((dt, dt'), T) => fn (us, i, j) =>
          if is_rec_type dt then (Bound i :: us, i + 1, j + 1)
          else
            (if b andalso is_poly thy dt' then
               case size_of_type (K NONE) extra_size size_ofp T of
                 NONE => us | SOME sz => sz $ Bound j :: us
             else us, i, j + 1))
              (cargs ~~ cargs' ~~ Ts) ([], 0, k);
        val t =
          if null ts andalso (not b orelse not (exists (is_poly thy) cargs'))
          then HOLogic.zero
          else foldl1 plus (ts @ [HOLogic.Suc_zero])
      in
        foldr (fn (T, t') => Abs ("x", T, t')) t (Ts @ replicate k HOLogic.natT)
      end;

    val fs = maps (fn (_, (name, _, constrs)) =>
      map (size_of_constr true param_size) (constrs ~~ constrs_of thy name)) descr;
    val fs' = maps (fn (n, (name, _, constrs)) =>
      map (size_of_constr (l <= n) (K NONE)) (constrs ~~ constrs_of thy name)) descr;
    val fTs = map fastype_of fs;

    val (rec_combs1, rec_combs2) = chop l (map (fn (T, rec_name) =>
      Const (rec_name, fTs @ [T] ---> HOLogic.natT))
        (recTs ~~ rec_names));

    fun instance_size_class tyco thy =
      thy
      |> TheoryTarget.instantiation
           ([tyco], replicate (Sign.arity_number thy tyco) HOLogic.typeS, [HOLogic.class_size])
      |> Class.prove_instantiation_instance (K (Class.intro_classes_tac []))
      |> LocalTheory.exit
      |> ProofContext.theory_of;

    val ((size_def_thms, size_def_thms'), thy') =
      thy
      |> Sign.add_consts_i (map (fn (s, T) =>
           (Sign.base_name s, param_size_fTs @ [T] ---> HOLogic.natT, NoSyn))
           (size_names ~~ recTs1))
      |> fold (fn (_, (name, _, _)) => instance_size_class name) descr'
      |> PureThy.add_defs_i false
        (map (Thm.no_attributes o apsnd (Logic.mk_equals o apsnd (app fs)))
           (def_names ~~ (size_fns ~~ rec_combs1)))
      ||>> PureThy.add_defs_i true
        (map (Thm.no_attributes o apsnd (Logic.mk_equals o apsnd (app fs')))
           (def_names' ~~ (overloaded_size_fns ~~ rec_combs1)));

    val ctxt = ProofContext.init thy';

    val simpset1 = HOL_basic_ss addsimps @{thm add_0} :: @{thm add_0_right} ::
      size_def_thms @ size_def_thms' @ rec_rewrites @ extra_rewrites;
    val xs = map (fn i => "x" ^ string_of_int i) (1 upto length recTs2);

    fun mk_unfolded_size_eq tab size_ofp fs (p as (x, T), r) =
      HOLogic.mk_eq (app fs r $ Free p,
        the (size_of_type tab extra_size size_ofp T) $ Free p);

    fun prove_unfolded_size_eqs size_ofp fs =
      if null recTs2 then []
      else map standard (split_conj_thm (SkipProof.prove ctxt [] []
        (HOLogic.mk_Trueprop (mk_conj (replicate l HOLogic.true_const @
           map (mk_unfolded_size_eq (AList.lookup op =
               (new_type_names ~~ map (app fs) rec_combs1)) size_ofp fs)
             (xs ~~ recTs2 ~~ rec_combs2))))
        (fn _ => (indtac induction xs THEN_ALL_NEW asm_simp_tac simpset1) 1)));

    val unfolded_size_eqs = prove_unfolded_size_eqs param_size fs @
      prove_unfolded_size_eqs (K NONE) fs';

    (* characteristic equations for size functions *)
    fun gen_mk_size_eq p size_of size_ofp size_const T (cname, cargs) =
      let
        val Ts = map (typ_of_dtyp descr sorts) cargs;
        val tnames = Name.variant_list f_names (DatatypeProp.make_tnames Ts);
        val ts = List.mapPartial (fn (sT as (s, T), dt) =>
          Option.map (fn sz => sz $ Free sT)
            (if p dt then size_of_type size_of extra_size size_ofp T
             else NONE)) (tnames ~~ Ts ~~ cargs)
      in
        HOLogic.mk_Trueprop (HOLogic.mk_eq
          (size_const $ list_comb (Const (cname, Ts ---> T),
             map2 (curry Free) tnames Ts),
           if null ts then HOLogic.zero
           else foldl1 plus (ts @ [HOLogic.Suc_zero])))
      end;

    val simpset2 = HOL_basic_ss addsimps
      size_def_thms @ size_def_thms' @ rec_rewrites @ unfolded_size_eqs;

    fun prove_size_eqs p size_fns size_ofp =
      maps (fn (((_, (_, _, constrs)), size_const), T) =>
        map (fn constr => standard (SkipProof.prove ctxt [] []
          (gen_mk_size_eq p (AList.lookup op = (new_type_names ~~ size_fns))
             size_ofp size_const T constr)
          (fn _ => simp_tac simpset2 1))) constrs)
        (descr' ~~ size_fns ~~ recTs1);

    val size_eqns = prove_size_eqs (is_poly thy') size_fns param_size @
      prove_size_eqs is_rec_type overloaded_size_fns (K NONE);

    val ([size_thms], thy'') =  PureThy.add_thmss
      [(("size", size_eqns),
        [Simplifier.simp_add, Thm.declaration_attribute
              (fn thm => Context.mapping (Code.add_default_func thm) I)])] thy'

  in
    SizeData.map (fold (Symtab.update_new o apsnd (rpair size_thms))
      (new_type_names ~~ size_names)) thy''
  end;

fun add_size_thms (new_type_names as name :: _) thy =
  let
    val info as {descr, alt_names, ...} = DatatypePackage.the_datatype thy name;
    val prefix = NameSpace.map_base (K (space_implode "_"
      (the_default (map Sign.base_name new_type_names) alt_names))) name;
    val no_size = exists (fn (_, (_, _, constrs)) => exists (fn (_, cargs) => exists (fn dt =>
      is_rec_type dt andalso not (null (fst (strip_dtyp dt)))) cargs) constrs) descr
  in if no_size then thy
    else
      thy
      |> Sign.root_path
      |> Sign.add_path prefix
      |> prove_size_thms info new_type_names
      |> Sign.restore_naming thy
  end;

val size_thms = snd oo (the oo lookup_size);

val setup = DatatypePackage.interpretation add_size_thms;

end;