(*  Title:      HOL/Tools/datatype_prop.ML
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Characteristic properties of datatypes.
*)

signature DATATYPE_PROP =
sig
  val dtK : int ref
  val indexify_names: string list -> string list
  val make_injs : (int * (string * DatatypeAux.dtyp list *
    (string * DatatypeAux.dtyp list) list)) list list -> (string * sort) list ->
      term list list
  val make_ind : (int * (string * DatatypeAux.dtyp list *
    (string * DatatypeAux.dtyp list) list)) list list -> (string * sort) list -> term
  val make_casedists : (int * (string * DatatypeAux.dtyp list *
    (string * DatatypeAux.dtyp list) list)) list list -> (string * sort) list -> term list
  val make_primrecs : string list -> (int * (string * DatatypeAux.dtyp list *
    (string * DatatypeAux.dtyp list) list)) list list -> (string * sort) list ->
      theory -> term list
  val make_cases : string list -> (int * (string * DatatypeAux.dtyp list *
    (string * DatatypeAux.dtyp list) list)) list list -> (string * sort) list ->
      theory -> term list list
  val make_distincts : string list -> (int * (string * DatatypeAux.dtyp list *
    (string * DatatypeAux.dtyp list) list)) list list -> (string * sort) list ->
      theory -> term list list
  val make_splits : string list -> (int * (string * DatatypeAux.dtyp list *
    (string * DatatypeAux.dtyp list) list)) list list -> (string * sort) list ->
      theory -> (term * term) list
  val make_case_trrules : string list -> (int * (string * DatatypeAux.dtyp list *
    (string * DatatypeAux.dtyp list) list)) list list -> ast Syntax.trrule list
  val make_size : (int * (string * DatatypeAux.dtyp list *
    (string * DatatypeAux.dtyp list) list)) list list -> (string * sort) list ->
      theory -> term list
  val make_weak_case_congs : string list -> (int * (string * DatatypeAux.dtyp list *
    (string * DatatypeAux.dtyp list) list)) list list -> (string * sort) list ->
      theory -> term list
  val make_case_congs : string list -> (int * (string * DatatypeAux.dtyp list *
    (string * DatatypeAux.dtyp list) list)) list list -> (string * sort) list ->
      theory -> term list
  val make_nchotomys : (int * (string * DatatypeAux.dtyp list *
    (string * DatatypeAux.dtyp list) list)) list list -> (string * sort) list -> term list
end;

structure DatatypeProp : DATATYPE_PROP =
struct

open DatatypeAux;

(*the kind of distinctiveness axioms depends on number of constructors*)
val dtK = ref 7;

fun indexify_names names =
  let
    fun index (x :: xs) tab =
      (case assoc (tab, x) of
        None => if x mem xs then (x ^ "1") :: index xs ((x, 2) :: tab) else x :: index xs tab
      | Some i => (x ^ Library.string_of_int i) :: index xs ((x, i + 1) :: tab))
    | index [] _ = [];
  in index names [] end;

fun make_tnames Ts =
  let
    fun type_name (TFree (name, _)) = implode (tl (explode name))
      | type_name (Type (name, _)) = 
          let val name' = Sign.base_name name
          in if Syntax.is_identifier name' then name' else "x" end;
  in indexify_names (map type_name Ts) end;



(************************* injectivity of constructors ************************)

fun make_injs descr sorts =
  let
    val descr' = flat descr;

    fun make_inj T ((cname, cargs), injs) =
      if null cargs then injs else
        let
          val Ts = map (typ_of_dtyp descr' sorts) cargs;
          val constr_t = Const (cname, Ts ---> T);
          val tnames = make_tnames Ts;
          val frees = map Free (tnames ~~ Ts);
          val frees' = map Free ((map ((op ^) o (rpair "'")) tnames) ~~ Ts);
        in (HOLogic.mk_Trueprop (HOLogic.mk_eq
          (HOLogic.mk_eq (list_comb (constr_t, frees), list_comb (constr_t, frees')),
           foldr1 (HOLogic.mk_binop "op &")
             (map HOLogic.mk_eq (frees ~~ frees')))))::injs
        end;

  in map (fn (d, T) => foldr (make_inj T) (#3 (snd d), []))
    ((hd descr) ~~ take (length (hd descr), get_rec_types descr' sorts))
  end;

(********************************* induction **********************************)

fun make_ind descr sorts =
  let
    val descr' = flat descr;
    val recTs = get_rec_types descr' sorts;
    val pnames = if length descr' = 1 then ["P"]
      else map (fn i => "P" ^ string_of_int i) (1 upto length descr');

    fun make_pred i T =
      let val T' = T --> HOLogic.boolT
      in Free (nth_elem (i, pnames), T') end;

    fun make_ind_prem k T (cname, cargs) =
      let
        fun mk_prem ((DtRec k, s), T) = HOLogic.mk_Trueprop
              (make_pred k T $ Free (s, T))
          | mk_prem ((DtType ("fun", [_, DtRec k]), s), T' as Type ("fun", [T, U])) =
              (Const (InductivePackage.inductive_forall_name,
                  [T --> HOLogic.boolT] ---> HOLogic.boolT) $
                Abs ("x", T, make_pred k U $ (Free (s, T') $ Bound 0))) |> HOLogic.mk_Trueprop;

        val recs = filter is_rec_type cargs;
        val Ts = map (typ_of_dtyp descr' sorts) cargs;
        val recTs' = map (typ_of_dtyp descr' sorts) recs;
        val tnames = variantlist (make_tnames Ts, pnames);
        val rec_tnames = map fst (filter (is_rec_type o snd) (tnames ~~ cargs));
        val frees = tnames ~~ Ts;
        val prems = map mk_prem (recs ~~ rec_tnames ~~ recTs');

      in list_all_free (frees, Logic.list_implies (prems,
        HOLogic.mk_Trueprop (make_pred k T $ 
          list_comb (Const (cname, Ts ---> T), map Free frees))))
      end;

    val prems = flat (map (fn ((i, (_, _, constrs)), T) =>
      map (make_ind_prem i T) constrs) (descr' ~~ recTs));
    val tnames = make_tnames recTs;
    val concl = HOLogic.mk_Trueprop (foldr1 (HOLogic.mk_binop "op &")
      (map (fn (((i, _), T), tname) => make_pred i T $ Free (tname, T))
        (descr' ~~ recTs ~~ tnames)))

  in Logic.list_implies (prems, concl) end;

(******************************* case distinction *****************************)

fun make_casedists descr sorts =
  let
    val descr' = flat descr;

    fun make_casedist_prem T (cname, cargs) =
      let
        val Ts = map (typ_of_dtyp descr' sorts) cargs;
        val frees = variantlist (make_tnames Ts, ["P", "y"]) ~~ Ts;
        val free_ts = map Free frees
      in list_all_free (frees, Logic.mk_implies (HOLogic.mk_Trueprop
        (HOLogic.mk_eq (Free ("y", T), list_comb (Const (cname, Ts ---> T), free_ts))),
          HOLogic.mk_Trueprop (Free ("P", HOLogic.boolT))))
      end;

    fun make_casedist ((_, (_, _, constrs)), T) =
      let val prems = map (make_casedist_prem T) constrs
      in Logic.list_implies (prems, HOLogic.mk_Trueprop (Free ("P", HOLogic.boolT)))
      end

  in map make_casedist
    ((hd descr) ~~ take (length (hd descr), get_rec_types descr' sorts))
  end;

(*************** characteristic equations for primrec combinator **************)

fun make_primrecs new_type_names descr sorts thy =
  let
    val o_name = "Fun.op o";

    val sign = Theory.sign_of thy;

    val descr' = flat descr;
    val recTs = get_rec_types descr' sorts;
    val used = foldr add_typ_tfree_names (recTs, []);

    val rec_result_Ts = map TFree (variantlist (replicate (length descr') "'t", used) ~~
      replicate (length descr') HOLogic.termS);

    val reccomb_fn_Ts = flat (map (fn (i, (_, _, constrs)) =>
      map (fn (_, cargs) =>
        let
          val Ts = map (typ_of_dtyp descr' sorts) cargs;
          val recs = filter (is_rec_type o fst) (cargs ~~ Ts);

          fun mk_argT (DtRec k, _) = nth_elem (k, rec_result_Ts)
            | mk_argT (DtType ("fun", [_, DtRec k]), Type ("fun", [T, _])) =
               T --> nth_elem (k, rec_result_Ts);

          val argTs = Ts @ map mk_argT recs
        in argTs ---> nth_elem (i, rec_result_Ts)
        end) constrs) descr');

    val rec_fns = map (uncurry (mk_Free "f"))
      (reccomb_fn_Ts ~~ (1 upto (length reccomb_fn_Ts)));

    val big_reccomb_name = (space_implode "_" new_type_names) ^ "_rec";
    val reccomb_names = map (Sign.intern_const sign)
      (if length descr' = 1 then [big_reccomb_name] else
        (map ((curry (op ^) (big_reccomb_name ^ "_")) o string_of_int)
          (1 upto (length descr'))));
    val reccombs = map (fn ((name, T), T') => list_comb
      (Const (name, reccomb_fn_Ts @ [T] ---> T'), rec_fns))
        (reccomb_names ~~ recTs ~~ rec_result_Ts);

    fun make_primrec T comb_t ((ts, f::fs), (cname, cargs)) =
      let
        val recs = filter is_rec_type cargs;
        val Ts = map (typ_of_dtyp descr' sorts) cargs;
        val recTs' = map (typ_of_dtyp descr' sorts) recs;
        val tnames = make_tnames Ts;
        val rec_tnames = map fst (filter (is_rec_type o snd) (tnames ~~ cargs));
        val frees = map Free (tnames ~~ Ts);
        val frees' = map Free (rec_tnames ~~ recTs');

        fun mk_reccomb (DtRec i, _) = nth_elem (i, reccombs)
          | mk_reccomb (DtType ("fun", [_, DtRec i]), Type ("fun", [T, U])) =
              let val T' = nth_elem (i, rec_result_Ts)
              in Const (o_name, [U --> T', T --> U, T] ---> T') $ nth_elem (i, reccombs)
              end;

        val reccombs' = map mk_reccomb (recs ~~ recTs')

      in (ts @ [HOLogic.mk_Trueprop (HOLogic.mk_eq
        (comb_t $ list_comb (Const (cname, Ts ---> T), frees),
         list_comb (f, frees @ (map (op $) (reccombs' ~~ frees')))))], fs)
      end

  in fst (foldl (fn (x, ((dt, T), comb_t)) =>
    foldl (make_primrec T comb_t) (x, #3 (snd dt)))
      (([], rec_fns), descr' ~~ recTs ~~ reccombs))
  end;

(****************** make terms of form  t_case f1 ... fn  *********************)

fun make_case_combs new_type_names descr sorts thy fname =
  let
    val descr' = flat descr;
    val recTs = get_rec_types descr' sorts;
    val used = foldr add_typ_tfree_names (recTs, []);
    val newTs = take (length (hd descr), recTs);
    val T' = TFree (variant used "'t", HOLogic.termS);

    val case_fn_Ts = map (fn (i, (_, _, constrs)) =>
      map (fn (_, cargs) =>
        let val Ts = map (typ_of_dtyp descr' sorts) cargs
        in Ts ---> T' end) constrs) (hd descr);

    val case_names = map (fn s =>
      Sign.intern_const (Theory.sign_of thy) (s ^ "_case")) new_type_names
  in
    map (fn ((name, Ts), T) => list_comb
      (Const (name, Ts @ [T] ---> T'),
        map (uncurry (mk_Free fname)) (Ts ~~ (1 upto length Ts))))
          (case_names ~~ case_fn_Ts ~~ newTs)
  end;

(**************** characteristic equations for case combinator ****************)

fun make_cases new_type_names descr sorts thy =
  let
    val descr' = flat descr;
    val recTs = get_rec_types descr' sorts;
    val newTs = take (length (hd descr), recTs);

    fun make_case T comb_t ((cname, cargs), f) =
      let
        val Ts = map (typ_of_dtyp descr' sorts) cargs;
        val frees = map Free ((make_tnames Ts) ~~ Ts)
      in HOLogic.mk_Trueprop (HOLogic.mk_eq
        (comb_t $ list_comb (Const (cname, Ts ---> T), frees),
         list_comb (f, frees)))
      end

  in map (fn (((_, (_, _, constrs)), T), comb_t) =>
    map (make_case T comb_t) (constrs ~~ (snd (strip_comb comb_t))))
      ((hd descr) ~~ newTs ~~ (make_case_combs new_type_names descr sorts thy "f"))
  end;

(************************* distinctness of constructors ***********************)

fun make_distincts new_type_names descr sorts thy =
  let
    val descr' = flat descr;
    val recTs = get_rec_types descr' sorts;
    val newTs = take (length (hd descr), recTs);

    (**** number of constructors < dtK : C_i ... ~= C_j ... ****)

    fun make_distincts_1 _ [] = []
      | make_distincts_1 T ((cname, cargs)::constrs) =
          let
            val Ts = map (typ_of_dtyp descr' sorts) cargs;
            val frees = map Free ((make_tnames Ts) ~~ Ts);
            val t = list_comb (Const (cname, Ts ---> T), frees);

            fun make_distincts' [] = []
              | make_distincts' ((cname', cargs')::constrs') =
                  let
                    val Ts' = map (typ_of_dtyp descr' sorts) cargs';
                    val frees' = map Free ((map ((op ^) o (rpair "'"))
                      (make_tnames Ts')) ~~ Ts');
                    val t' = list_comb (Const (cname', Ts' ---> T), frees')
                  in
                    (HOLogic.mk_Trueprop (HOLogic.Not $ HOLogic.mk_eq (t, t')))::
                    (HOLogic.mk_Trueprop (HOLogic.Not $ HOLogic.mk_eq (t', t)))::
                      (make_distincts' constrs')
                  end

          in (make_distincts' constrs) @ (make_distincts_1 T constrs)
          end;

  in map (fn (((_, (_, _, constrs)), T), tname) =>
      if length constrs < !dtK then make_distincts_1 T constrs else [])
        ((hd descr) ~~ newTs ~~ new_type_names)
  end;


(*************************** the "split" - equations **************************)

fun make_splits new_type_names descr sorts thy =
  let
    val descr' = flat descr;
    val recTs = get_rec_types descr' sorts;
    val used' = foldr add_typ_tfree_names (recTs, []);
    val newTs = take (length (hd descr), recTs);
    val T' = TFree (variant used' "'t", HOLogic.termS);
    val P = Free ("P", T' --> HOLogic.boolT);

    fun make_split (((_, (_, _, constrs)), T), comb_t) =
      let
        val (_, fs) = strip_comb comb_t;
        val used = ["P", "x"] @ (map (fst o dest_Free) fs);

        fun process_constr (((cname, cargs), f), (t1s, t2s)) =
          let
            val Ts = map (typ_of_dtyp descr' sorts) cargs;
            val frees = map Free (variantlist (make_tnames Ts, used) ~~ Ts);
            val eqn = HOLogic.mk_eq (Free ("x", T),
              list_comb (Const (cname, Ts ---> T), frees));
            val P' = P $ list_comb (f, frees)
          in ((foldr (fn (Free (s, T), t) => HOLogic.mk_all (s, T, t))
                (frees, HOLogic.imp $ eqn $ P'))::t1s,
              (foldr (fn (Free (s, T), t) => HOLogic.mk_exists (s, T, t))
                (frees, HOLogic.conj $ eqn $ (HOLogic.Not $ P')))::t2s)
          end;

        val (t1s, t2s) = foldr process_constr (constrs ~~ fs, ([], []));
        val lhs = P $ (comb_t $ Free ("x", T))
      in
        (HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, mk_conj t1s)),
         HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, HOLogic.Not $ mk_disj t2s)))
      end

  in map make_split ((hd descr) ~~ newTs ~~
    (make_case_combs new_type_names descr sorts thy "f"))
  end;

(************************ translation rules for case **************************)

fun make_case_trrules new_type_names descr =
  let
    fun mk_asts i j ((cname, cargs)::constrs) =
      let
        val k = length cargs;
        val xs = map (fn i => Variable ("x" ^ string_of_int i)) (i upto i + k - 1);
        val t = Variable ("t" ^ string_of_int j);
        val ast = Syntax.mk_appl (Constant "_case1")
          [Syntax.mk_appl (Constant (Sign.base_name cname)) xs, t];
        val ast' = foldr (fn (x, y) =>
          Syntax.mk_appl (Constant "_abs") [x, y]) (xs, t)
      in
        (case constrs of
            [] => (ast, [ast'])
          | cs => let val (ast'', asts) = mk_asts (i + k) (j + 1) cs
              in (Syntax.mk_appl (Constant "_case2") [ast, ast''],
                  ast'::asts)
              end)
      end;

    fun mk_trrule ((_, (_, _, constrs)), tname) =
      let val (ast, asts) = mk_asts 1 1 constrs
      in Syntax.ParsePrintRule
        (Syntax.mk_appl (Constant "_case_syntax") [Variable "t", ast],
         Syntax.mk_appl (Constant (tname ^ "_case"))
           (asts @ [Variable "t"]))
      end

  in
    map mk_trrule (hd descr ~~ new_type_names)
  end;

(******************************* size functions *******************************)

fun make_size descr sorts thy =
  let
    val descr' = flat descr;
    val recTs = get_rec_types descr' sorts;

    val size_name = "Nat.size";
    val size_names = replicate (length (hd descr)) size_name @
      map (Sign.intern_const (Theory.sign_of thy)) (indexify_names
        (map (fn T => name_of_typ T ^ "_size") (drop (length (hd descr), recTs))));
    val size_consts = map (fn (s, T) =>
      Const (s, T --> HOLogic.natT)) (size_names ~~ recTs);

    fun plus (t1, t2) = Const ("op +", [HOLogic.natT, HOLogic.natT] ---> HOLogic.natT) $ t1 $ t2;

    fun make_size_eqn size_const T (cname, cargs) =
      let
        val recs = filter is_rec_type cargs;
        val Ts = map (typ_of_dtyp descr' sorts) cargs;
        val recTs = map (typ_of_dtyp descr' sorts) recs;
        val tnames = make_tnames Ts;
        val rec_tnames = map fst (filter (is_rec_type o snd) (tnames ~~ cargs));
        val ts = map (fn ((r, s), T) => nth_elem (dest_DtRec r, size_consts) $
          Free (s, T)) (recs ~~ rec_tnames ~~ recTs);
        val t = if ts = [] then HOLogic.zero else
          foldl1 plus (ts @ [HOLogic.mk_nat 1])
      in
        HOLogic.mk_Trueprop (HOLogic.mk_eq (size_const $
          list_comb (Const (cname, Ts ---> T), map Free (tnames ~~ Ts)), t))
      end

  in
    flat (map (fn (((_, (_, _, constrs)), size_const), T) =>
      map (make_size_eqn size_const T) constrs) (descr' ~~ size_consts ~~ recTs))
  end;

(************************* additional rules for TFL ***************************)

fun make_weak_case_congs new_type_names descr sorts thy =
  let
    val case_combs = make_case_combs new_type_names descr sorts thy "f";

    fun mk_case_cong comb =
      let 
        val Type ("fun", [T, _]) = fastype_of comb;
        val M = Free ("M", T);
        val M' = Free ("M'", T);
      in
        Logic.mk_implies (HOLogic.mk_Trueprop (HOLogic.mk_eq (M, M')),
          HOLogic.mk_Trueprop (HOLogic.mk_eq (comb $ M, comb $ M')))
      end
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

fun make_case_congs new_type_names descr sorts thy =
  let
    val case_combs = make_case_combs new_type_names descr sorts thy "f";
    val case_combs' = make_case_combs new_type_names descr sorts thy "g";

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
            val (Ts, _) = strip_type (fastype_of f);
            val tnames = variantlist (make_tnames Ts, used);
            val frees = map Free (tnames ~~ Ts)
          in
            list_all_free (tnames ~~ Ts, Logic.mk_implies
              (HOLogic.mk_Trueprop
                (HOLogic.mk_eq (M', list_comb (Const (cname, Ts ---> T), frees))),
               HOLogic.mk_Trueprop
                (HOLogic.mk_eq (list_comb (f, frees), list_comb (g, frees)))))
          end

      in
        Logic.list_implies (HOLogic.mk_Trueprop (HOLogic.mk_eq (M, M')) ::
          map mk_clause (fs ~~ gs ~~ constrs),
            HOLogic.mk_Trueprop (HOLogic.mk_eq (comb $ M, comb' $ M')))
      end

  in
    map mk_case_cong (case_combs ~~ case_combs' ~~ hd descr)
  end;

(*---------------------------------------------------------------------------
 * Structure of exhaustion theorem looks like this:
 *
 *    !v. (? y1..yi. v = C1 y1..yi) | ... | (? y1..yj. v = Cn y1..yj)
 *---------------------------------------------------------------------------*)

fun make_nchotomys descr sorts =
  let
    val descr' = flat descr;
    val recTs = get_rec_types descr' sorts;
    val newTs = take (length (hd descr), recTs);

    fun mk_eqn T (cname, cargs) =
      let
        val Ts = map (typ_of_dtyp descr' sorts) cargs;
        val tnames = variantlist (make_tnames Ts, ["v"]);
        val frees = tnames ~~ Ts
      in
        foldr (fn ((s, T'), t) => HOLogic.mk_exists (s, T', t))
          (frees, HOLogic.mk_eq (Free ("v", T),
            list_comb (Const (cname, Ts ---> T), map Free frees)))
      end

  in map (fn ((_, (_, _, constrs)), T) =>
    HOLogic.mk_Trueprop (HOLogic.mk_all ("v", T, mk_disj (map (mk_eqn T) constrs))))
      (hd descr ~~ newTs)
  end;

end;
