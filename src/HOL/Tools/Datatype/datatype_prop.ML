(*  Title:      HOL/Tools/Datatype/datatype_prop.ML
    Author:     Stefan Berghofer, TU Muenchen

Datatype package: characteristic properties of datatypes.
*)

signature DATATYPE_PROP =
sig
  type descr = Datatype_Aux.descr
  val indexify_names: string list -> string list
  val make_tnames: typ list -> string list
  val make_injs : descr list -> term list list
  val make_distincts : descr list -> term list list (*no symmetric inequalities*)
  val make_ind : descr list -> term
  val make_casedists : descr list -> term list
  val make_primrec_Ts : descr list -> string list -> typ list * typ list
  val make_primrecs : string list -> descr list -> theory -> term list
  val make_cases : string list -> descr list -> theory -> term list list
  val make_splits : string list -> descr list -> theory -> (term * term) list
  val make_case_combs : string list -> descr list -> theory -> string -> term list
  val make_weak_case_congs : string list -> descr list -> theory -> term list
  val make_case_congs : string list -> descr list -> theory -> term list
  val make_nchotomys : descr list -> term list
end;

structure Datatype_Prop : DATATYPE_PROP =
struct

type descr = Datatype_Aux.descr;


fun indexify_names names =
  let
    fun index (x :: xs) tab =
        (case AList.lookup (op =) tab x of
          NONE =>
            if member (op =) xs x
            then (x ^ "1") :: index xs ((x, 2) :: tab)
            else x :: index xs tab
        | SOME i => (x ^ string_of_int i) :: index xs ((x, i + 1) :: tab))
      | index [] _ = [];
  in index names [] end;

fun make_tnames Ts =
  let
    fun type_name (TFree (name, _)) = unprefix "'" name
      | type_name (Type (name, _)) =
          let val name' = Long_Name.base_name name
          in if Lexicon.is_identifier name' then name' else "x" end;
  in indexify_names (map type_name Ts) end;


(************************* injectivity of constructors ************************)

fun make_injs descr =
  let
    val descr' = flat descr;
    fun make_inj T (cname, cargs) =
      if null cargs then I
      else
        let
          val Ts = map (Datatype_Aux.typ_of_dtyp descr') cargs;
          val constr_t = Const (cname, Ts ---> T);
          val tnames = make_tnames Ts;
          val frees = map Free (tnames ~~ Ts);
          val frees' = map Free (map (suffix "'") tnames ~~ Ts);
        in
          cons (HOLogic.mk_Trueprop (HOLogic.mk_eq
            (HOLogic.mk_eq (list_comb (constr_t, frees), list_comb (constr_t, frees')),
             foldr1 (HOLogic.mk_binop @{const_name HOL.conj})
               (map HOLogic.mk_eq (frees ~~ frees')))))
        end;
  in
    map2 (fn d => fn T => fold_rev (make_inj T) (#3 (snd d)) [])
      (hd descr) (take (length (hd descr)) (Datatype_Aux.get_rec_types descr'))
  end;


(************************* distinctness of constructors ***********************)

fun make_distincts descr =
  let
    val descr' = flat descr;
    val recTs = Datatype_Aux.get_rec_types descr';
    val newTs = take (length (hd descr)) recTs;

    fun prep_constr (cname, cargs) = (cname, map (Datatype_Aux.typ_of_dtyp descr') cargs);

    fun make_distincts' _ [] = []
      | make_distincts' T ((cname, cargs) :: constrs) =
          let
            val frees = map Free (make_tnames cargs ~~ cargs);
            val t = list_comb (Const (cname, cargs ---> T), frees);

            fun make_distincts'' (cname', cargs') =
              let
                val frees' = map Free (map (suffix "'") (make_tnames cargs') ~~ cargs');
                val t' = list_comb (Const (cname', cargs' ---> T), frees');
              in
                HOLogic.mk_Trueprop (HOLogic.Not $ HOLogic.mk_eq (t, t'))
              end;
          in map make_distincts'' constrs @ make_distincts' T constrs end;
  in
    map2 (fn ((_, (_, _, constrs))) => fn T =>
      make_distincts' T (map prep_constr constrs)) (hd descr) newTs
  end;


(********************************* induction **********************************)

fun make_ind descr =
  let
    val descr' = flat descr;
    val recTs = Datatype_Aux.get_rec_types descr';
    val pnames =
      if length descr' = 1 then ["P"]
      else map (fn i => "P" ^ string_of_int i) (1 upto length descr');

    fun make_pred i T =
      let val T' = T --> HOLogic.boolT
      in Free (nth pnames i, T') end;

    fun make_ind_prem k T (cname, cargs) =
      let
        fun mk_prem ((dt, s), T) =
          let val (Us, U) = strip_type T
          in
            Logic.list_all (map (pair "x") Us,
              HOLogic.mk_Trueprop
                (make_pred (Datatype_Aux.body_index dt) U $
                  Datatype_Aux.app_bnds (Free (s, T)) (length Us)))
          end;

        val recs = filter Datatype_Aux.is_rec_type cargs;
        val Ts = map (Datatype_Aux.typ_of_dtyp descr') cargs;
        val recTs' = map (Datatype_Aux.typ_of_dtyp descr') recs;
        val tnames = Name.variant_list pnames (make_tnames Ts);
        val rec_tnames = map fst (filter (Datatype_Aux.is_rec_type o snd) (tnames ~~ cargs));
        val frees = tnames ~~ Ts;
        val prems = map mk_prem (recs ~~ rec_tnames ~~ recTs');
      in
        fold_rev (Logic.all o Free) frees
          (Logic.list_implies (prems,
            HOLogic.mk_Trueprop (make_pred k T $
              list_comb (Const (cname, Ts ---> T), map Free frees))))
      end;

    val prems =
      maps (fn ((i, (_, _, constrs)), T) => map (make_ind_prem i T) constrs) (descr' ~~ recTs);
    val tnames = make_tnames recTs;
    val concl =
      HOLogic.mk_Trueprop (foldr1 (HOLogic.mk_binop @{const_name HOL.conj})
        (map (fn (((i, _), T), tname) => make_pred i T $ Free (tname, T))
          (descr' ~~ recTs ~~ tnames)));

  in Logic.list_implies (prems, concl) end;

(******************************* case distinction *****************************)

fun make_casedists descr =
  let
    val descr' = flat descr;

    fun make_casedist_prem T (cname, cargs) =
      let
        val Ts = map (Datatype_Aux.typ_of_dtyp descr') cargs;
        val frees = Name.variant_list ["P", "y"] (make_tnames Ts) ~~ Ts;
        val free_ts = map Free frees;
      in
        fold_rev (Logic.all o Free) frees
          (Logic.mk_implies (HOLogic.mk_Trueprop
            (HOLogic.mk_eq (Free ("y", T), list_comb (Const (cname, Ts ---> T), free_ts))),
              HOLogic.mk_Trueprop (Free ("P", HOLogic.boolT))))
      end;

    fun make_casedist ((_, (_, _, constrs))) T =
      let val prems = map (make_casedist_prem T) constrs
      in Logic.list_implies (prems, HOLogic.mk_Trueprop (Free ("P", HOLogic.boolT))) end;

  in
    map2 make_casedist (hd descr)
      (take (length (hd descr)) (Datatype_Aux.get_rec_types descr'))
  end;

(*************** characteristic equations for primrec combinator **************)

fun make_primrec_Ts descr used =
  let
    val descr' = flat descr;

    val rec_result_Ts =
      map TFree
        (Name.variant_list used (replicate (length descr') "'t") ~~
          replicate (length descr') HOLogic.typeS);

    val reccomb_fn_Ts = maps (fn (i, (_, _, constrs)) =>
      map (fn (_, cargs) =>
        let
          val Ts = map (Datatype_Aux.typ_of_dtyp descr') cargs;
          val recs = filter (Datatype_Aux.is_rec_type o fst) (cargs ~~ Ts);

          fun mk_argT (dt, T) =
            binder_types T ---> nth rec_result_Ts (Datatype_Aux.body_index dt);

          val argTs = Ts @ map mk_argT recs
        in argTs ---> nth rec_result_Ts i end) constrs) descr';

  in (rec_result_Ts, reccomb_fn_Ts) end;

fun make_primrecs reccomb_names descr thy =
  let
    val descr' = flat descr;
    val recTs = Datatype_Aux.get_rec_types descr';
    val used = fold Term.add_tfree_namesT recTs [];

    val (rec_result_Ts, reccomb_fn_Ts) = make_primrec_Ts descr used;

    val rec_fns =
      map (uncurry (Datatype_Aux.mk_Free "f"))
        (reccomb_fn_Ts ~~ (1 upto (length reccomb_fn_Ts)));

    val reccombs =
      map (fn ((name, T), T') => list_comb (Const (name, reccomb_fn_Ts @ [T] ---> T'), rec_fns))
        (reccomb_names ~~ recTs ~~ rec_result_Ts);

    fun make_primrec T comb_t (cname, cargs) (ts, f :: fs) =
      let
        val recs = filter Datatype_Aux.is_rec_type cargs;
        val Ts = map (Datatype_Aux.typ_of_dtyp descr') cargs;
        val recTs' = map (Datatype_Aux.typ_of_dtyp descr') recs;
        val tnames = make_tnames Ts;
        val rec_tnames = map fst (filter (Datatype_Aux.is_rec_type o snd) (tnames ~~ cargs));
        val frees = map Free (tnames ~~ Ts);
        val frees' = map Free (rec_tnames ~~ recTs');

        fun mk_reccomb ((dt, T), t) =
          let val (Us, U) = strip_type T in
            fold_rev (Term.abs o pair "x") Us
              (nth reccombs (Datatype_Aux.body_index dt) $ Datatype_Aux.app_bnds t (length Us))
          end;

        val reccombs' = map mk_reccomb (recs ~~ recTs' ~~ frees');

      in
        (ts @ [HOLogic.mk_Trueprop
          (HOLogic.mk_eq (comb_t $ list_comb (Const (cname, Ts ---> T), frees),
            list_comb (f, frees @ reccombs')))], fs)
      end;
  in
    fold (fn ((dt, T), comb_t) => fold (make_primrec T comb_t) (#3 (snd dt)))
      (descr' ~~ recTs ~~ reccombs) ([], rec_fns)
    |> fst
  end;

(****************** make terms of form  t_case f1 ... fn  *********************)

fun make_case_combs case_names descr thy fname =
  let
    val descr' = flat descr;
    val recTs = Datatype_Aux.get_rec_types descr';
    val used = fold Term.add_tfree_namesT recTs [];
    val newTs = take (length (hd descr)) recTs;
    val T' = TFree (singleton (Name.variant_list used) "'t", HOLogic.typeS);

    val case_fn_Ts = map (fn (i, (_, _, constrs)) =>
      map (fn (_, cargs) =>
        let val Ts = map (Datatype_Aux.typ_of_dtyp descr') cargs
        in Ts ---> T' end) constrs) (hd descr);
  in
    map (fn ((name, Ts), T) => list_comb
      (Const (name, Ts @ [T] ---> T'),
        map (uncurry (Datatype_Aux.mk_Free fname)) (Ts ~~ (1 upto length Ts))))
          (case_names ~~ case_fn_Ts ~~ newTs)
  end;

(**************** characteristic equations for case combinator ****************)

fun make_cases case_names descr thy =
  let
    val descr' = flat descr;
    val recTs = Datatype_Aux.get_rec_types descr';
    val newTs = take (length (hd descr)) recTs;

    fun make_case T comb_t ((cname, cargs), f) =
      let
        val Ts = map (Datatype_Aux.typ_of_dtyp descr') cargs;
        val frees = map Free ((make_tnames Ts) ~~ Ts);
      in
        HOLogic.mk_Trueprop
          (HOLogic.mk_eq (comb_t $ list_comb (Const (cname, Ts ---> T), frees),
            list_comb (f, frees)))
      end;
  in
    map (fn (((_, (_, _, constrs)), T), comb_t) =>
      map (make_case T comb_t) (constrs ~~ snd (strip_comb comb_t)))
        (hd descr ~~ newTs ~~ make_case_combs case_names descr thy "f")
  end;


(*************************** the "split" - equations **************************)

fun make_splits case_names descr thy =
  let
    val descr' = flat descr;
    val recTs = Datatype_Aux.get_rec_types descr';
    val used' = fold Term.add_tfree_namesT recTs [];
    val newTs = take (length (hd descr)) recTs;
    val T' = TFree (singleton (Name.variant_list used') "'t", HOLogic.typeS);
    val P = Free ("P", T' --> HOLogic.boolT);

    fun make_split (((_, (_, _, constrs)), T), comb_t) =
      let
        val (_, fs) = strip_comb comb_t;
        val used = ["P", "x"] @ map (fst o dest_Free) fs;

        fun process_constr ((cname, cargs), f) (t1s, t2s) =
          let
            val Ts = map (Datatype_Aux.typ_of_dtyp descr') cargs;
            val frees = map Free (Name.variant_list used (make_tnames Ts) ~~ Ts);
            val eqn = HOLogic.mk_eq (Free ("x", T), list_comb (Const (cname, Ts ---> T), frees));
            val P' = P $ list_comb (f, frees);
          in
           (fold_rev (fn Free (s, T) => fn t => HOLogic.mk_all (s, T, t)) frees
             (HOLogic.imp $ eqn $ P') :: t1s,
            fold_rev (fn Free (s, T) => fn t => HOLogic.mk_exists (s, T, t)) frees
             (HOLogic.conj $ eqn $ (HOLogic.Not $ P')) :: t2s)
          end;

        val (t1s, t2s) = fold_rev process_constr (constrs ~~ fs) ([], []);
        val lhs = P $ (comb_t $ Free ("x", T));
      in
        (HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, Datatype_Aux.mk_conj t1s)),
         HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, HOLogic.Not $ Datatype_Aux.mk_disj t2s)))
      end

  in
    map make_split (hd descr ~~ newTs ~~ make_case_combs case_names descr thy "f")
  end;

(************************* additional rules for TFL ***************************)

fun make_weak_case_congs case_names descr thy =
  let
    val case_combs = make_case_combs case_names descr thy "f";

    fun mk_case_cong comb =
      let
        val Type ("fun", [T, _]) = fastype_of comb;
        val M = Free ("M", T);
        val M' = Free ("M'", T);
      in
        Logic.mk_implies (HOLogic.mk_Trueprop (HOLogic.mk_eq (M, M')),
          HOLogic.mk_Trueprop (HOLogic.mk_eq (comb $ M, comb $ M')))
      end;
  in
    map mk_case_cong case_combs
  end;


(*---------------------------------------------------------------------------
 * Structure of case congruence theorem looks like this:
 *
 *    (M = M')
 *    ==> (!!x1,...,xk. (M' = C1 x1..xk) ==> (f1 x1..xk = g1 x1..xk))
 *    ==> ...
 *    ==> (!!x1,...,xj. (M' = Cn x1..xj) ==> (fn x1..xj = gn x1..xj))
 *    ==>
 *      (ty_case f1..fn M = ty_case g1..gn M')
 *---------------------------------------------------------------------------*)

fun make_case_congs case_names descr thy =
  let
    val case_combs = make_case_combs case_names descr thy "f";
    val case_combs' = make_case_combs case_names descr thy "g";

    fun mk_case_cong ((comb, comb'), (_, (_, _, constrs))) =
      let
        val Type ("fun", [T, _]) = fastype_of comb;
        val (_, fs) = strip_comb comb;
        val (_, gs) = strip_comb comb';
        val used = ["M", "M'"] @ map (fst o dest_Free) (fs @ gs);
        val M = Free ("M", T);
        val M' = Free ("M'", T);

        fun mk_clause ((f, g), (cname, _)) =
          let
            val Ts = binder_types (fastype_of f);
            val tnames = Name.variant_list used (make_tnames Ts);
            val frees = map Free (tnames ~~ Ts);
          in
            fold_rev Logic.all frees
              (Logic.mk_implies
                (HOLogic.mk_Trueprop
                  (HOLogic.mk_eq (M', list_comb (Const (cname, Ts ---> T), frees))),
                 HOLogic.mk_Trueprop
                  (HOLogic.mk_eq (list_comb (f, frees), list_comb (g, frees)))))
          end;
      in
        Logic.list_implies (HOLogic.mk_Trueprop (HOLogic.mk_eq (M, M')) ::
          map mk_clause (fs ~~ gs ~~ constrs),
            HOLogic.mk_Trueprop (HOLogic.mk_eq (comb $ M, comb' $ M')))
      end;
  in
    map mk_case_cong (case_combs ~~ case_combs' ~~ hd descr)
  end;

(*---------------------------------------------------------------------------
 * Structure of exhaustion theorem looks like this:
 *
 *    !v. (? y1..yi. v = C1 y1..yi) | ... | (? y1..yj. v = Cn y1..yj)
 *---------------------------------------------------------------------------*)

fun make_nchotomys descr =
  let
    val descr' = flat descr;
    val recTs = Datatype_Aux.get_rec_types descr';
    val newTs = take (length (hd descr)) recTs;

    fun mk_eqn T (cname, cargs) =
      let
        val Ts = map (Datatype_Aux.typ_of_dtyp descr') cargs;
        val tnames = Name.variant_list ["v"] (make_tnames Ts);
        val frees = tnames ~~ Ts;
      in
        fold_rev (fn (s, T') => fn t => HOLogic.mk_exists (s, T', t)) frees
          (HOLogic.mk_eq (Free ("v", T),
            list_comb (Const (cname, Ts ---> T), map Free frees)))
      end;
  in
    map (fn ((_, (_, _, constrs)), T) =>
        HOLogic.mk_Trueprop
          (HOLogic.mk_all ("v", T, Datatype_Aux.mk_disj (map (mk_eqn T) constrs))))
      (hd descr ~~ newTs)
  end;

end;
