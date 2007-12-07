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
  type T = thm list Symtab.table;
  val empty = Symtab.empty;
  val copy = I
  val extend = I
  fun merge _ = Symtab.merge (K true);
);

fun add_axioms label ts atts thy =
  thy
  |> PureThy.add_axiomss_i [((label, ts), atts)];

val Const (size_name, _) = HOLogic.size_const dummyT;
val size_name_base = NameSpace.base size_name;
val size_suffix = "_" ^ size_name_base;

fun instance_size_class tyco thy =
  thy
  |> TheoryTarget.instantiation
       ([tyco], replicate (Sign.arity_number thy tyco) HOLogic.typeS, [HOLogic.class_size])
  |> Class.prove_instantiation_instance (K (Class.intro_classes_tac []))
  |> LocalTheory.exit
  |> ProofContext.theory_of;

fun plus (t1, t2) = Const ("HOL.plus_class.plus",
  HOLogic.natT --> HOLogic.natT --> HOLogic.natT) $ t1 $ t2;

fun make_size head_len descr' sorts recTs thy =
  let
    val size_names = replicate head_len size_name @
      map (Sign.intern_const thy) (DatatypeProp.indexify_names
        (map (fn T => name_of_typ T ^ size_suffix) (Library.drop (head_len, recTs))));
    val size_consts = map2 (fn s => fn T => Const (s, T --> HOLogic.natT))
      size_names recTs;

    fun make_tnames Ts =
      let
        fun type_name (TFree (name, _)) = implode (tl (explode name))
          | type_name (Type (name, _)) = 
              let val name' = Sign.base_name name
              in if Syntax.is_identifier name' then name' else "x" end;
      in DatatypeProp.indexify_names (map type_name Ts) end;

    fun make_size_eqn size_const T (cname, cargs) =
      let
        val recs = filter is_rec_type cargs;
        val Ts = map (typ_of_dtyp descr' sorts) cargs;
        val recTs = map (typ_of_dtyp descr' sorts) recs;
        val tnames = make_tnames Ts;
        val rec_tnames = map fst (filter (is_rec_type o snd) (tnames ~~ cargs));
        val ts = map2 (fn (r, s) => fn T => nth size_consts (dest_DtRec r) $
          Free (s, T)) (recs ~~ rec_tnames) recTs;
        val t = if null ts then HOLogic.zero else
          Library.foldl plus (hd ts, tl ts @ [HOLogic.Suc_zero]);
      in
        HOLogic.mk_Trueprop (HOLogic.mk_eq (size_const $
          list_comb (Const (cname, Ts ---> T), map2 (curry Free) tnames Ts), t))
      end

  in
    maps (fn (((_, (_, _, constrs)), size_const), T) =>
      map (make_size_eqn size_const T) constrs) (descr' ~~ size_consts ~~ recTs)
  end;

fun prove_size_thms (info : datatype_info) head_len thy =
  let
    val descr' = #descr info;
    val sorts = #sorts info;
    val reccomb_names = #rec_names info;
    val primrec_thms = #rec_rewrites info;
    val recTs = get_rec_types descr' sorts;

    val size_names = replicate head_len size_name @
      map (Sign.full_name thy) (DatatypeProp.indexify_names
        (map (fn T => name_of_typ T ^ size_suffix) (Library.drop (head_len, recTs))));
    val def_names = map (fn s => s ^ "_def") (DatatypeProp.indexify_names
      (map (fn T => name_of_typ T ^ size_suffix) recTs));

    fun make_sizefun (_, cargs) =
      let
        val Ts = map (typ_of_dtyp descr' sorts) cargs;
        val k = length (filter is_rec_type cargs);
        val ts = map Bound (k - 1 downto 0);
        val t = if null ts then HOLogic.zero else
          Library.foldl plus (hd ts, tl ts @ [HOLogic.Suc_zero]);

      in
        foldr (fn (T, t') => Abs ("x", T, t')) t (Ts @ replicate k HOLogic.natT)
      end;

    val fs = maps (fn (_, (_, _, constrs)) => map make_sizefun constrs) descr';
    val fTs = map fastype_of fs;

    val (size_def_thms, thy') =
      thy
      |> Sign.add_consts_i (map (fn (s, T) =>
           (Sign.base_name s, T --> HOLogic.natT, NoSyn))
           (Library.drop (head_len, size_names ~~ recTs)))
      |> fold (fn (_, (name, _, _)) => instance_size_class name) descr'
      |> PureThy.add_defs_i true (map (Thm.no_attributes o (fn (((s, T), def_name), rec_name) =>
           (def_name, Logic.mk_equals (Const (s, T --> HOLogic.natT),
            list_comb (Const (rec_name, fTs @ [T] ---> HOLogic.natT), fs)))))
            (size_names ~~ recTs ~~ def_names ~~ reccomb_names));

    val rewrites = size_def_thms @ map mk_meta_eq primrec_thms;

    val size_thms = map (fn t => Goal.prove_global thy' [] [] t
      (fn _ => EVERY [rewrite_goals_tac rewrites, rtac refl 1]))
        (make_size head_len descr' sorts recTs thy')

  in
    thy'
    |> PureThy.add_thmss [((size_name_base, size_thms), [])]
    |>> flat
  end;

fun axiomatize_size_thms (info : datatype_info) head_len thy =
  let
    val descr' = #descr info;
    val sorts = #sorts info;
    val recTs = get_rec_types descr' sorts;

    val used = map fst (fold Term.add_tfreesT recTs []);

    val size_names = DatatypeProp.indexify_names
      (map (fn T => name_of_typ T ^ size_suffix) (Library.drop (head_len, recTs)));

    val thy' = thy |> fold (fn (s, T) =>
        snd o Theory.specify_const [] (Sign.base_name s, T --> HOLogic.natT, NoSyn) [])
      (size_names ~~ Library.drop (head_len, recTs))
    val size_axs = make_size head_len descr' sorts recTs thy';
  in
    thy'
    |> add_axioms size_name_base size_axs []
    ||> fold (fn (_, (name, _, _)) => instance_size_class name) descr'
    |>> flat
  end;

fun add_size_thms (name :: _) thy =
  let
    val info = DatatypePackage.the_datatype thy name;
    val descr' = #descr info;
    val head_len = #head_len info;
    val typnames = map (#1 o snd) (curry Library.take head_len descr');
    val prefix = space_implode "_" (map NameSpace.base typnames);
    val no_size = exists (fn (_, (_, _, constrs)) => exists (fn (_, cargs) => exists (fn dt =>
      is_rec_type dt andalso not (null (fst (strip_dtyp dt)))) cargs) constrs)
        (#descr info)
  in if no_size then thy
    else
      thy
      |> Sign.add_path prefix
      |> (if ! quick_and_dirty
        then axiomatize_size_thms info head_len
        else prove_size_thms info head_len)
      ||> Sign.parent_path
      |-> (fn thms => PureThy.add_thmss [(("", thms),
            [Simplifier.simp_add, Thm.declaration_attribute
              (fn thm => Context.mapping (Code.add_default_func thm) I)])])
      |-> (fn thms => SizeData.map (fold (fn typname => Symtab.update_new
            (typname, flat thms)) typnames))
  end;

fun size_thms thy = the o Symtab.lookup (SizeData.get thy);

val setup = DatatypePackage.interpretation add_size_thms;

end;