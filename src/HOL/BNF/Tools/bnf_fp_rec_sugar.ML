(*  Title:      HOL/BNF/Tools/bnf_fp_rec_sugar.ML
    Author:     Lorenz Panny, TU Muenchen
    Copyright   2013

Recursor and corecursor sugar.
*)

signature BNF_FP_REC_SUGAR =
sig
  val add_primrec_cmd: (binding * string option * mixfix) list ->
    (Attrib.binding * string) list -> local_theory -> local_theory;
  val add_primcorec_cmd: bool ->
    (binding * string option * mixfix) list * (Attrib.binding * string) list -> Proof.context ->
    Proof.state
end;

structure BNF_FP_Rec_Sugar : BNF_FP_REC_SUGAR =
struct

open BNF_Util
open BNF_FP_Util
open BNF_FP_Rec_Sugar_Util
open BNF_FP_Rec_Sugar_Tactics

exception Primrec_Error of string * term list;

fun primrec_error str = raise Primrec_Error (str, []);
fun primrec_error_eqn str eqn = raise Primrec_Error (str, [eqn]);
fun primrec_error_eqns str eqns = raise Primrec_Error (str, eqns);

fun finds eq = fold_map (fn x => List.partition (curry eq x) #>> pair x);

val free_name = try (fn Free (v, _) => v);
val const_name = try (fn Const (v, _) => v);
val undef_const = Const (@{const_name undefined}, dummyT);

fun permute_args n t = list_comb (t, map Bound (0 :: (n downto 1)))
  |> fold (K (fn u => Abs (Name.uu, dummyT, u))) (0 upto n);
val abs_tuple = HOLogic.tupled_lambda o HOLogic.mk_tuple;
fun drop_All t = subst_bounds (strip_qnt_vars @{const_name all} t |> map Free |> rev,
  strip_qnt_body @{const_name all} t)
fun mk_not @{const True} = @{const False}
  | mk_not @{const False} = @{const True}
  | mk_not (@{const Not} $ t) = t
  | mk_not (@{const Trueprop} $ t) = @{const Trueprop} $ mk_not t
  | mk_not t = HOLogic.mk_not t
val mk_conjs = try (foldr1 HOLogic.mk_conj) #> the_default @{const True};
val mk_disjs = try (foldr1 HOLogic.mk_disj) #> the_default @{const False};

fun invert_prems [t] = map mk_not (HOLogic.disjuncts t)
  | invert_prems ts = [mk_disjs (map mk_not ts)];

val simp_attrs = @{attributes [simp]};

fun abstract n vs (t $ u) = abstract n vs t $ abstract n vs u
  | abstract n vs (Abs (v, T, b)) = Abs (v, T, abstract (n + 1) vs b)
  | abstract n vs t = let val idx = find_index (equal t) vs in
      if idx < 0 then t else Bound (n + idx) end;


(* Primrec *)

type eqn_data = {
  fun_name: string,
  rec_type: typ,
  ctr: term,
  ctr_args: term list,
  left_args: term list,
  right_args: term list,
  res_type: typ,
  rhs_term: term,
  user_eqn: term
};

fun dissect_eqn lthy fun_names eqn' =
  let
    val eqn = drop_All eqn' |> HOLogic.dest_Trueprop
      handle TERM _ =>
        primrec_error_eqn "malformed function equation (expected \"lhs = rhs\")" eqn';
    val (lhs, rhs) = HOLogic.dest_eq eqn
        handle TERM _ =>
          primrec_error_eqn "malformed function equation (expected \"lhs = rhs\")" eqn';
    val (fun_name, args) = strip_comb lhs
      |>> (fn x => if is_Free x then fst (dest_Free x)
          else primrec_error_eqn "malformed function equation (does not start with free)" eqn);
    val (left_args, rest) = take_prefix is_Free args;
    val (nonfrees, right_args) = take_suffix is_Free rest;
    val _ = length nonfrees = 1 orelse if length nonfrees = 0 then
      primrec_error_eqn "constructor pattern missing in left-hand side" eqn else
      primrec_error_eqn "more than one non-variable argument in left-hand side" eqn;
    val _ = member (op =) fun_names fun_name orelse
      primrec_error_eqn "malformed function equation (does not start with function name)" eqn

    val (ctr, ctr_args) = strip_comb (the_single nonfrees);
    val _ = try (num_binder_types o fastype_of) ctr = SOME (length ctr_args) orelse
      primrec_error_eqn "partially applied constructor in pattern" eqn;
    val _ = let val d = duplicates (op =) (left_args @ ctr_args @ right_args) in null d orelse
      primrec_error_eqn ("duplicate variable \"" ^ Syntax.string_of_term lthy (hd d) ^
        "\" in left-hand side") eqn end;
    val _ = forall is_Free ctr_args orelse
      primrec_error_eqn "non-primitive pattern in left-hand side" eqn;
    val _ =
      let val b = fold_aterms (fn x as Free (v, _) =>
        if (not (member (op =) (left_args @ ctr_args @ right_args) x) andalso
        not (member (op =) fun_names v) andalso
        not (Variable.is_fixed lthy v)) then cons x else I | _ => I) rhs []
      in
        null b orelse
        primrec_error_eqn ("extra variable(s) in right-hand side: " ^
          commas (map (Syntax.string_of_term lthy) b)) eqn
      end;
  in
    {fun_name = fun_name,
     rec_type = body_type (type_of ctr),
     ctr = ctr,
     ctr_args = ctr_args,
     left_args = left_args,
     right_args = right_args,
     res_type = map fastype_of (left_args @ right_args) ---> fastype_of rhs,
     rhs_term = rhs,
     user_eqn = eqn'}
  end;

fun rewrite_map_arg get_ctr_pos rec_type res_type =
  let
    val pT = HOLogic.mk_prodT (rec_type, res_type);

    val maybe_suc = Option.map (fn x => x + 1);
    fun subst d (t as Bound d') = t |> d = SOME d' ? curry (op $) (fst_const pT)
      | subst d (Abs (v, T, b)) = Abs (v, if d = SOME ~1 then pT else T, subst (maybe_suc d) b)
      | subst d t =
        let
          val (u, vs) = strip_comb t;
          val ctr_pos = try (get_ctr_pos o the) (free_name u) |> the_default ~1;
        in
          if ctr_pos >= 0 then
            if d = SOME ~1 andalso length vs = ctr_pos then
              list_comb (permute_args ctr_pos (snd_const pT), vs)
            else if length vs > ctr_pos andalso is_some d
                andalso d = try (fn Bound n => n) (nth vs ctr_pos) then
              list_comb (snd_const pT $ nth vs ctr_pos, map (subst d) (nth_drop ctr_pos vs))
            else
              primrec_error_eqn ("recursive call not directly applied to constructor argument") t
          else if d = SOME ~1 andalso const_name u = SOME @{const_name comp} then
            list_comb (map_types (K dummyT) u, map2 subst [NONE, d] vs)
          else
            list_comb (u, map (subst (d |> d = SOME ~1 ? K NONE)) vs)
        end
  in
    subst (SOME ~1)
  end;

fun subst_rec_calls lthy get_ctr_pos has_call ctr_args direct_calls indirect_calls t =
  let
    fun subst bound_Ts (Abs (v, T, b)) = Abs (v, T, subst (T :: bound_Ts) b)
      | subst bound_Ts (t as g' $ y) =
        let
          val maybe_direct_y' = AList.lookup (op =) direct_calls y;
          val maybe_indirect_y' = AList.lookup (op =) indirect_calls y;
          val (g, g_args) = strip_comb g';
          val ctr_pos = try (get_ctr_pos o the) (free_name g) |> the_default ~1;
          val _ = ctr_pos < 0 orelse length g_args >= ctr_pos orelse
            primrec_error_eqn "too few arguments in recursive call" t;
        in
          if not (member (op =) ctr_args y) then
            pairself (subst bound_Ts) (g', y) |> (op $)
          else if ctr_pos >= 0 then
            list_comb (the maybe_direct_y', g_args)
          else if is_some maybe_indirect_y' then
            (if has_call g' then t else y)
            |> massage_indirect_rec_call lthy has_call
              (rewrite_map_arg get_ctr_pos) bound_Ts y (the maybe_indirect_y')
            |> (if has_call g' then I else curry (op $) g')
          else
            t
        end
      | subst _ t = t
  in
    subst [] t
    |> tap (fn u => has_call u andalso (* FIXME detect this case earlier *)
      primrec_error_eqn "recursive call not directly applied to constructor argument" t)
  end;

fun build_rec_arg lthy funs_data has_call ctr_spec maybe_eqn_data =
  if is_none maybe_eqn_data then undef_const else
    let
      val eqn_data = the maybe_eqn_data;
      val t = #rhs_term eqn_data;
      val ctr_args = #ctr_args eqn_data;

      val calls = #calls ctr_spec;
      val n_args = fold (curry (op +) o (fn Direct_Rec _ => 2 | _ => 1)) calls 0;

      val no_calls' = tag_list 0 calls
        |> map_filter (try (apsnd (fn No_Rec n => n | Direct_Rec (n, _) => n)));
      val direct_calls' = tag_list 0 calls
        |> map_filter (try (apsnd (fn Direct_Rec (_, n) => n)));
      val indirect_calls' = tag_list 0 calls
        |> map_filter (try (apsnd (fn Indirect_Rec n => n)));

      fun make_direct_type T = dummyT; (* FIXME? *)

      val rec_res_type_list = map (fn (x :: _) => (#rec_type x, #res_type x)) funs_data;

      fun make_indirect_type (Type (Tname, Ts)) = Type (Tname, Ts |> map (fn T =>
        let val maybe_res_type = AList.lookup (op =) rec_res_type_list T in
          if is_some maybe_res_type
          then HOLogic.mk_prodT (T, the maybe_res_type)
          else make_indirect_type T end))
        | make_indirect_type T = T;

      val args = replicate n_args ("", dummyT)
        |> Term.rename_wrt_term t
        |> map Free
        |> fold (fn (ctr_arg_idx, arg_idx) =>
            nth_map arg_idx (K (nth ctr_args ctr_arg_idx)))
          no_calls'
        |> fold (fn (ctr_arg_idx, arg_idx) =>
            nth_map arg_idx (K (nth ctr_args ctr_arg_idx |> map_types make_direct_type)))
          direct_calls'
        |> fold (fn (ctr_arg_idx, arg_idx) =>
            nth_map arg_idx (K (nth ctr_args ctr_arg_idx |> map_types make_indirect_type)))
          indirect_calls';

      val fun_name_ctr_pos_list =
        map (fn (x :: _) => (#fun_name x, length (#left_args x))) funs_data;
      val get_ctr_pos = try (the o AList.lookup (op =) fun_name_ctr_pos_list) #> the_default ~1;
      val direct_calls = map (apfst (nth ctr_args) o apsnd (nth args)) direct_calls';
      val indirect_calls = map (apfst (nth ctr_args) o apsnd (nth args)) indirect_calls';

      val abstractions = args @ #left_args eqn_data @ #right_args eqn_data;
    in
      t
      |> subst_rec_calls lthy get_ctr_pos has_call ctr_args direct_calls indirect_calls
      |> fold_rev lambda abstractions
    end;

fun build_defs lthy bs mxs funs_data rec_specs has_call =
  let
    val n_funs = length funs_data;

    val ctr_spec_eqn_data_list' =
      (take n_funs rec_specs |> map #ctr_specs) ~~ funs_data
      |> maps (uncurry (finds (fn (x, y) => #ctr x = #ctr y))
          ##> (fn x => null x orelse
            primrec_error_eqns "excess equations in definition" (map #rhs_term x)) #> fst);
    val _ = ctr_spec_eqn_data_list' |> map (fn (_, x) => length x <= 1 orelse
      primrec_error_eqns ("multiple equations for constructor") (map #user_eqn x));

    val ctr_spec_eqn_data_list =
      ctr_spec_eqn_data_list' @ (drop n_funs rec_specs |> maps #ctr_specs |> map (rpair []));

    val recs = take n_funs rec_specs |> map #recx;
    val rec_args = ctr_spec_eqn_data_list
      |> sort ((op <) o pairself (#offset o fst) |> make_ord)
      |> map (uncurry (build_rec_arg lthy funs_data has_call) o apsnd (try the_single));
    val ctr_poss = map (fn x =>
      if length (distinct ((op =) o pairself (length o #left_args)) x) <> 1 then
        primrec_error ("inconstant constructor pattern position for function " ^
          quote (#fun_name (hd x)))
      else
        hd x |> #left_args |> length) funs_data;
  in
    (recs, ctr_poss)
    |-> map2 (fn recx => fn ctr_pos => list_comb (recx, rec_args) |> permute_args ctr_pos)
    |> Syntax.check_terms lthy
    |> map3 (fn b => fn mx => fn t => ((b, mx), ((Binding.map_name Thm.def_name b, []), t))) bs mxs
  end;

fun find_rec_calls has_call eqn_data =
  let
    fun find (Abs (_, _, b)) ctr_arg = find b ctr_arg
      | find (t as _ $ _) ctr_arg =
        let
          val (f', args') = strip_comb t;
          val n = find_index (equal ctr_arg) args';
        in
          if n < 0 then
            find f' ctr_arg @ maps (fn x => find x ctr_arg) args'
          else
            let val (f, args) = chop n args' |>> curry list_comb f' in
              if has_call f then
                f :: maps (fn x => find x ctr_arg) args
              else
                find f ctr_arg @ maps (fn x => find x ctr_arg) args
            end
        end
      | find _ _ = [];
  in
    map (find (#rhs_term eqn_data)) (#ctr_args eqn_data)
    |> (fn [] => NONE | callss => SOME (#ctr eqn_data, callss))
  end;

fun add_primrec fixes specs lthy =
  let
    val (bs, mxs) = map_split (apfst fst) fixes;
    val fun_names = map Binding.name_of bs;
    val eqns_data = map (snd #> dissect_eqn lthy fun_names) specs;
    val funs_data = eqns_data
      |> partition_eq ((op =) o pairself #fun_name)
      |> finds (fn (x, y) => x = #fun_name (hd y)) fun_names |> fst
      |> map (fn (x, y) => the_single y handle List.Empty =>
          primrec_error ("missing equations for function " ^ quote x));

    val has_call = exists_subterm (map (fst #>> Binding.name_of #> Free) fixes |> member (op =));
    val arg_Ts = map (#rec_type o hd) funs_data;
    val res_Ts = map (#res_type o hd) funs_data;
    val callssss = funs_data
      |> map (partition_eq ((op =) o pairself #ctr))
      |> map (maps (map_filter (find_rec_calls has_call)));

    fun get_indices t = map (fst #>> Binding.name_of #> Free) fixes
      |> map_index (fn (i, v) => if exists_subterm (equal v) t then SOME i else NONE)
      |> map_filter I;
    val ((nontriv, rec_specs, _, induct_thm, induct_thms), lthy') =
      rec_specs_of bs arg_Ts res_Ts get_indices callssss lthy;

    val actual_nn = length funs_data;

    val _ = let val ctrs = (maps (map #ctr o #ctr_specs) rec_specs) in
      map (fn {ctr, user_eqn, ...} => member (op =) ctrs ctr orelse
        primrec_error_eqn ("argument " ^ quote (Syntax.string_of_term lthy' ctr) ^
          " is not a constructor in left-hand side") user_eqn) eqns_data end;

    val defs = build_defs lthy' bs mxs funs_data rec_specs has_call;

    fun prove def_thms' {ctr_specs, nested_map_idents, nested_map_comps, ...} induct_thm fun_data
        lthy =
      let
        val fun_name = #fun_name (hd fun_data);
        val def_thms = map (snd o snd) def_thms';
        val simp_thms = finds (fn (x, y) => #ctr x = #ctr y) fun_data ctr_specs
          |> fst
          |> map_filter (try (fn (x, [y]) =>
            (#user_eqn x, length (#left_args x) + length (#right_args x), #rec_thm y)))
          |> map (fn (user_eqn, num_extra_args, rec_thm) =>
            mk_primrec_tac lthy num_extra_args nested_map_idents nested_map_comps def_thms rec_thm
            |> K |> Goal.prove lthy [] [] user_eqn)

        val notes =
          [(inductN, if actual_nn > 1 then [induct_thm] else [], []),
           (simpsN, simp_thms, simp_attrs)]
          |> filter_out (null o #2)
          |> map (fn (thmN, thms, attrs) =>
            ((Binding.qualify true fun_name (Binding.name thmN), attrs), [(thms, [])]));
      in
        lthy |> Local_Theory.notes notes
      end;

    val common_name = mk_common_name fun_names;

    val common_notes =
      [(inductN, if nontriv andalso actual_nn > 1 then [induct_thm] else [], [])]
      |> filter_out (null o #2)
      |> map (fn (thmN, thms, attrs) =>
        ((Binding.qualify true common_name (Binding.name thmN), attrs), [(thms, [])]));
  in
    lthy'
    |> fold_map Local_Theory.define defs
    |-> snd oo (fn def_thms' => fold_map3 (prove def_thms') (take actual_nn rec_specs)
      (take actual_nn induct_thms) funs_data)
    |> snd o Local_Theory.notes common_notes
  end;

fun add_primrec_cmd raw_fixes raw_specs lthy =
  let
    val _ = let val d = duplicates (op =) (map (Binding.name_of o #1) raw_fixes) in null d orelse
      primrec_error ("duplicate function name(s): " ^ commas d) end;
    val (fixes, specs) = fst (Specification.read_spec raw_fixes raw_specs lthy);
  in
    add_primrec fixes specs lthy
      handle ERROR str => primrec_error str
  end
  handle Primrec_Error (str, eqns) =>
    if null eqns
    then error ("primrec_new error:\n  " ^ str)
    else error ("primrec_new error:\n  " ^ str ^ "\nin\n  " ^
      space_implode "\n  " (map (quote o Syntax.string_of_term lthy) eqns))



(* Primcorec *)

type co_eqn_data_disc = {
  fun_name: string,
  fun_args: term list,
  ctr_no: int, (*###*)
  prems: term list,
  user_eqn: term
};
type co_eqn_data_sel = {
  fun_name: string,
  fun_args: term list,
  ctr: term,
  sel: term,
  rhs_term: term,
  user_eqn: term
};
datatype co_eqn_data =
  Disc of co_eqn_data_disc |
  Sel of co_eqn_data_sel;

fun co_dissect_eqn_disc sequential fun_names corec_specs prems' concl matchedss =
  let
    fun find_subterm p = let (* FIXME \<exists>? *)
      fun f (t as u $ v) = if p t then SOME t else merge_options (f u, f v)
        | f t = if p t then SOME t else NONE
      in f end;

    val applied_fun = concl
      |> find_subterm (member ((op =) o apsnd SOME) fun_names o try (fst o dest_Free o head_of))
      |> the
      handle Option.Option => primrec_error_eqn "malformed discriminator equation" concl;
    val (fun_name, fun_args) = strip_comb applied_fun |>> fst o dest_Free;
    val corec_spec = the (AList.lookup (op =) (fun_names ~~ corec_specs) fun_name);

    val discs = #ctr_specs corec_spec |> map #disc;
    val ctrs = #ctr_specs corec_spec |> map #ctr;
    val not_disc = head_of concl = @{term Not};
    val _ = not_disc andalso length ctrs <> 2 andalso
      primrec_error_eqn "\<not>ed discriminator for a type with \<noteq> 2 constructors" concl;
    val disc = find_subterm (member (op =) discs o head_of) concl;
    val eq_ctr0 = concl |> perhaps (try (HOLogic.dest_not)) |> try (HOLogic.dest_eq #> snd)
        |> (fn SOME t => let val n = find_index (equal t) ctrs in
          if n >= 0 then SOME n else NONE end | _ => NONE);
    val _ = is_some disc orelse is_some eq_ctr0 orelse
      primrec_error_eqn "no discriminator in equation" concl;
    val ctr_no' =
      if is_none disc then the eq_ctr0 else find_index (equal (head_of (the disc))) discs;
    val ctr_no = if not_disc then 1 - ctr_no' else ctr_no';

    val catch_all = try (fst o dest_Free o the_single) prems' = SOME Name.uu_;
    val matcheds = AList.lookup (op =) matchedss fun_name |> the_default [];
    val prems = map (abstract 0 (List.rev fun_args)) prems';
    val real_prems = (if catch_all orelse sequential then invert_prems matcheds else []) @
      (if catch_all then [] else prems);

    val matchedss' = AList.delete (op =) fun_name matchedss
      |> cons (fun_name, if sequential then prems @ matcheds else real_prems @ matcheds);

    val user_eqn =
      (real_prems, betapply (#disc (nth (#ctr_specs corec_spec) ctr_no), applied_fun))
      |>> map HOLogic.mk_Trueprop ||> HOLogic.mk_Trueprop
      |> Logic.list_implies;
  in
    (Disc {
      fun_name = fun_name,
      fun_args = fun_args,
      ctr_no = ctr_no,
      prems = real_prems,
      user_eqn = user_eqn
    }, matchedss')
  end;

fun co_dissect_eqn_sel fun_names corec_specs eqn' eqn =
  let
    val (lhs, rhs) = HOLogic.dest_eq eqn
      handle TERM _ =>
        primrec_error_eqn "malformed function equation (expected \"lhs = rhs\")" eqn;
    val sel = head_of lhs;
    val (fun_name, fun_args) = dest_comb lhs |> snd |> strip_comb |> apfst (fst o dest_Free)
      handle TERM _ =>
        primrec_error_eqn "malformed selector argument in left-hand side" eqn;
    val corec_spec = the (AList.lookup (op =) (fun_names ~~ corec_specs) fun_name)
      handle Option.Option => primrec_error_eqn "malformed selector argument in left-hand side" eqn;
    val (ctr_spec, sel) = #ctr_specs corec_spec
      |> the o get_index (try (the o find_first (equal sel) o #sels))
      |>> nth (#ctr_specs corec_spec);
    val user_eqn = drop_All eqn';
  in
    Sel {
      fun_name = fun_name,
      fun_args = fun_args,
      ctr = #ctr ctr_spec,
      sel = sel,
      rhs_term = rhs,
      user_eqn = user_eqn
    }
  end;

fun co_dissect_eqn_ctr sequential fun_names corec_specs eqn' imp_prems imp_rhs matchedss =
  let 
    val (lhs, rhs) = HOLogic.dest_eq imp_rhs;
    val fun_name = head_of lhs |> fst o dest_Free;
    val corec_spec = the (AList.lookup (op =) (fun_names ~~ corec_specs) fun_name);
    val (ctr, ctr_args) = strip_comb rhs;
    val ctr_spec = the (find_first (equal ctr o #ctr) (#ctr_specs corec_spec))
      handle Option.Option => primrec_error_eqn "not a constructor" ctr;

    val disc_imp_rhs = betapply (#disc ctr_spec, lhs);
    val (maybe_eqn_data_disc, matchedss') = if length (#ctr_specs corec_spec) = 1
      then (NONE, matchedss)
      else apfst SOME (co_dissect_eqn_disc
          sequential fun_names corec_specs imp_prems disc_imp_rhs matchedss);

    val sel_imp_rhss = (#sels ctr_spec ~~ ctr_args)
      |> map (fn (sel, ctr_arg) => HOLogic.mk_eq (betapply (sel, lhs), ctr_arg));

val _ = tracing ("reduced\n    " ^ Syntax.string_of_term @{context} imp_rhs ^ "\nto\n    \<cdot> " ^
 (is_some maybe_eqn_data_disc ? K (Syntax.string_of_term @{context} disc_imp_rhs ^ "\n    \<cdot> ")) "" ^
 space_implode "\n    \<cdot> " (map (Syntax.string_of_term @{context}) sel_imp_rhss));

    val eqns_data_sel =
      map (co_dissect_eqn_sel fun_names corec_specs eqn') sel_imp_rhss;
  in
    (the_list maybe_eqn_data_disc @ eqns_data_sel, matchedss')
  end;

fun co_dissect_eqn sequential fun_names corec_specs eqn' matchedss =
  let
    val eqn = drop_All eqn'
      handle TERM _ => primrec_error_eqn "malformed function equation" eqn';
    val (imp_prems, imp_rhs) = Logic.strip_horn eqn
      |> apfst (map HOLogic.dest_Trueprop) o apsnd HOLogic.dest_Trueprop;

    val head = imp_rhs
      |> perhaps (try HOLogic.dest_not) |> perhaps (try (fst o HOLogic.dest_eq))
      |> head_of;

    val maybe_rhs = imp_rhs |> perhaps (try (HOLogic.dest_not)) |> try (snd o HOLogic.dest_eq);

    val discs = maps #ctr_specs corec_specs |> map #disc;
    val sels = maps #ctr_specs corec_specs |> maps #sels;
    val ctrs = maps #ctr_specs corec_specs |> map #ctr;
  in
    if member (op =) discs head orelse
      is_some maybe_rhs andalso
        member (op =) (filter (null o binder_types o fastype_of) ctrs) (the maybe_rhs) then
      co_dissect_eqn_disc sequential fun_names corec_specs imp_prems imp_rhs matchedss
      |>> single
    else if member (op =) sels head then
      ([co_dissect_eqn_sel fun_names corec_specs eqn' imp_rhs], matchedss)
    else if is_Free head andalso member (op =) fun_names (fst (dest_Free head)) then
      co_dissect_eqn_ctr sequential fun_names corec_specs eqn' imp_prems imp_rhs matchedss
    else
      primrec_error_eqn "malformed function equation" eqn
  end;

fun build_corec_arg_disc ctr_specs {fun_args, ctr_no, prems, ...} =
  if is_none (#pred (nth ctr_specs ctr_no)) then I else
    mk_conjs prems
    |> curry subst_bounds (List.rev fun_args)
    |> HOLogic.tupled_lambda (HOLogic.mk_tuple fun_args)
    |> K |> nth_map (the (#pred (nth ctr_specs ctr_no)));

fun build_corec_arg_no_call sel_eqns sel = find_first (equal sel o #sel) sel_eqns
  |> try (fn SOME sel_eqn => (#fun_args sel_eqn, #rhs_term sel_eqn))
  |> the_default ([], undef_const)
  |-> abs_tuple
  |> K;

fun build_corec_arg_direct_call lthy has_call sel_eqns sel =
  let
    val maybe_sel_eqn = find_first (equal sel o #sel) sel_eqns;
    fun rewrite is_end U _ t =
      if U = @{typ bool} then @{term True} |> has_call t ? K @{term False} (* stop? *)
      else if is_end = has_call t then undef_const
      else if is_end then t (* end *)
      else HOLogic.mk_tuple (snd (strip_comb t)); (* continue *)
    fun massage rhs_term is_end t = massage_direct_corec_call
      lthy has_call (rewrite is_end) [] (range_type (fastype_of t)) rhs_term;
  in
    if is_none maybe_sel_eqn then K I else
      abs_tuple (#fun_args (the maybe_sel_eqn)) oo massage (#rhs_term (the maybe_sel_eqn))
  end;

fun build_corec_arg_indirect_call lthy has_call sel_eqns sel =
  let
    val maybe_sel_eqn = find_first (equal sel o #sel) sel_eqns;
    fun rewrite _ _ =
      let
        fun subst (Abs (v, T, b)) = Abs (v, T, subst b)
          | subst (t as _ $ _) =
            let val (u, vs) = strip_comb t in
              if is_Free u andalso has_call u then
                Const (@{const_name Inr}, dummyT) $ (*HOLogic.mk_tuple vs*)
                  (try (foldr1 (fn (x, y) => Const (@{const_name Pair}, dummyT) $ x $ y)) vs
                    |> the_default (hd vs))
              else if try (fst o dest_Const) u = SOME @{const_name prod_case} then
                list_comb (u |> map_types (K dummyT), map subst vs)
              else
                list_comb (subst u, map subst vs)
            end
          | subst t = t;
      in
        subst
      end;
    fun massage rhs_term t = massage_indirect_corec_call
      lthy has_call rewrite [] (fastype_of t |> range_type) rhs_term;
  in
    if is_none maybe_sel_eqn then I else
      abs_tuple (#fun_args (the maybe_sel_eqn)) o massage (#rhs_term (the maybe_sel_eqn))
  end;

fun build_corec_args_sel lthy has_call all_sel_eqns ctr_spec =
  let val sel_eqns = filter (equal (#ctr ctr_spec) o #ctr) all_sel_eqns in
    if null sel_eqns then I else
      let
        val sel_call_list = #sels ctr_spec ~~ #calls ctr_spec;

        val no_calls' = map_filter (try (apsnd (fn No_Corec n => n))) sel_call_list;
        val direct_calls' = map_filter (try (apsnd (fn Direct_Corec n => n))) sel_call_list;
        val indirect_calls' = map_filter (try (apsnd (fn Indirect_Corec n => n))) sel_call_list;
      in
        I
        #> fold (fn (sel, n) => nth_map n
          (build_corec_arg_no_call sel_eqns sel)) no_calls'
        #> fold (fn (sel, (q, g, h)) =>
          let val f = build_corec_arg_direct_call lthy has_call sel_eqns sel in
            nth_map h (f false) o nth_map g (f true) o nth_map q (f true) end) direct_calls'
        #> fold (fn (sel, n) => nth_map n
          (build_corec_arg_indirect_call lthy has_call sel_eqns sel)) indirect_calls'
      end
  end;

fun mk_real_disc_eqns ctr_specs disc_eqns =
  let
    val real_disc_eqns =
      if length disc_eqns = 0 then disc_eqns
      else if length disc_eqns = length ctr_specs - 1 then
        let
          val n = 0 upto length ctr_specs
            |> the(*###*) o find_first (fn idx => not (exists (equal idx o #ctr_no) disc_eqns));
          val extra_disc_eqn = {
            fun_name = #fun_name (hd disc_eqns),
            fun_args = #fun_args (hd disc_eqns),
            ctr_no = n,
            prems = maps (invert_prems o #prems) disc_eqns,
            user_eqn = Const (@{const_name undefined}, dummyT)};
        in
          chop n disc_eqns ||> cons extra_disc_eqn |> (op @)
        end
      else disc_eqns;
  in
    real_disc_eqns
  end;

fun co_build_defs lthy bs mxs has_call arg_Tss corec_specs disc_eqnss sel_eqnss =
  let
    val _ = disc_eqnss |> map (fn x =>
      let val d = duplicates ((op =) o pairself #ctr_no) x in null d orelse
        primrec_error_eqns "excess discriminator equations in definition"
          (maps (fn t => filter (equal (#ctr_no t) o #ctr_no) x) d |> map #user_eqn) end);
    val corec_specs' = take (length bs) corec_specs;
    val corecs = map #corec corec_specs';
    val ctr_specss = map #ctr_specs corec_specs';
    val real_disc_eqnss = map2 mk_real_disc_eqns ctr_specss disc_eqnss;
    val corec_args = hd corecs
      |> fst o split_last o binder_types o fastype_of
      |> map (Const o pair @{const_name undefined})
      |> fold2 (fold o build_corec_arg_disc) ctr_specss real_disc_eqnss
      |> fold2 (fold o build_corec_args_sel lthy has_call) sel_eqnss ctr_specss;
    fun currys Ts t = if length Ts <= 1 then t else
      t $ foldr1 (fn (u, v) => HOLogic.pair_const dummyT dummyT $ u $ v)
        (length Ts - 1 downto 0 |> map Bound)
      |> fold_rev (fn T => fn u => Abs (Name.uu, T, u)) Ts;

val _ = tracing ("corecursor arguments:\n    \<cdot> " ^
 space_implode "\n    \<cdot> " (map (Syntax.string_of_term lthy) corec_args));

    val exclss' =
      real_disc_eqnss
      |> map (map (fn {fun_args, ctr_no, prems, ...} => (fun_args, ctr_no, prems))
        #> fst o (fn xs => fold_map (fn x => fn ys => ((x, ys), ys @ [x])) xs [])
        #> maps (uncurry (map o pair)
          #> map (fn ((fun_args, c, x), (_, c', y)) => ((c, c'), (x, mk_not (mk_conjs y)))
            ||> apfst (map HOLogic.mk_Trueprop) o apsnd HOLogic.mk_Trueprop
            ||> Logic.list_implies
            ||> curry Logic.list_all (map dest_Free fun_args))))
  in
    map (list_comb o rpair corec_args) corecs
    |> map2 (fn Ts => fn t => if length Ts = 0 then t $ HOLogic.unit else t) arg_Tss
    |> map2 currys arg_Tss
    |> Syntax.check_terms lthy
    |> map3 (fn b => fn mx => fn t => ((b, mx), ((Binding.map_name Thm.def_name b, []), t))) bs mxs
    |> rpair exclss'
  end;

fun add_primcorec sequential fixes specs lthy =
  let
    val (bs, mxs) = map_split (apfst fst) fixes;
    val (arg_Ts, res_Ts) = map (strip_type o snd o fst #>> HOLogic.mk_tupleT) fixes |> split_list;

    (* copied from primrec_new *)
    fun get_indices t = map (fst #>> Binding.name_of #> Free) fixes
      |> map_index (fn (i, v) => if exists_subterm (equal v) t then SOME i else NONE)
      |> map_filter I;

    val callssss = []; (* FIXME *)

    val ((nontriv, corec_specs', _, coinduct_thm, strong_co_induct_thm, coinduct_thmss,
          strong_coinduct_thmss), lthy') =
      corec_specs_of bs arg_Ts res_Ts get_indices callssss lthy;

    val fun_names = map Binding.name_of bs;
    val corec_specs = take (length fun_names) corec_specs'; (*###*)

    val (eqns_data, _) =
      fold_map (co_dissect_eqn sequential fun_names corec_specs) (map snd specs) []
      |>> flat;

    val disc_eqnss = map_filter (try (fn Disc x => x)) eqns_data
      |> partition_eq ((op =) o pairself #fun_name)
      |> finds (fn (x, ({fun_name, ...} :: _)) => x = fun_name) fun_names |> fst
      |> map (sort ((op <) o pairself #ctr_no |> make_ord) o flat o snd);

    val sel_eqnss = map_filter (try (fn Sel x => x)) eqns_data
      |> partition_eq ((op =) o pairself #fun_name)
      |> finds (fn (x, ({fun_name, ...} :: _)) => x = fun_name) fun_names |> fst
      |> map (flat o snd);

    val has_call = exists_subterm (map (fst #>> Binding.name_of #> Free) fixes |> member (op =));
    val arg_Tss = map (binder_types o snd o fst) fixes;
    val (defs, exclss') =
      co_build_defs lthy' bs mxs has_call arg_Tss corec_specs disc_eqnss sel_eqnss;

    (* try to prove (automatically generated) tautologies by ourselves *)
    val exclss'' = exclss'
      |> map (map (apsnd
        (`(try (fn t => Goal.prove lthy [] [] t (mk_primcorec_taut_tac lthy |> K))))));
    val taut_thmss = map (map (apsnd (the o fst)) o filter (is_some o fst o snd)) exclss'';
    val (obligation_idxss, obligationss) = exclss''
      |> map (map (apsnd (rpair [] o snd)) o filter (is_none o fst o snd))
      |> split_list o map split_list;

    fun prove thmss' def_thms' lthy =
      let
        val def_thms = map (snd o snd) def_thms';

        val exclss' = map (op ~~) (obligation_idxss ~~ thmss');
        fun mk_exclsss excls n =
          (excls, map (fn k => replicate k [TrueI] @ replicate (n - k) []) (0 upto n - 1))
          |-> fold (fn ((c, c'), thm) => nth_map c (nth_map c' (K [thm])));
        val exclssss = (exclss' ~~ taut_thmss |> map (op @), fun_names ~~ corec_specs)
          |-> map2 (fn excls => fn (_, {ctr_specs, ...}) => mk_exclsss excls (length ctr_specs));

        fun prove_disc {ctr_specs, ...} exclsss
            {fun_name, fun_args, ctr_no, prems, ...} =
          let
            val disc_corec = nth ctr_specs ctr_no |> #disc_corec;
            val k = 1 + ctr_no;
            val m = length prems;
            val t =
              (* FIXME use applied_fun from dissect_\<dots> instead? *)
              list_comb (Free (fun_name, dummyT), map Bound (length fun_args - 1 downto 0))
              |> curry betapply (#disc (nth ctr_specs ctr_no)) (*###*)
              |> HOLogic.mk_Trueprop
              |> curry Logic.list_implies (map HOLogic.mk_Trueprop prems)
              |> curry Logic.list_all (map dest_Free fun_args)
              |> Syntax.check_term lthy(*###*);
          in
            mk_primcorec_disc_tac lthy def_thms disc_corec k m exclsss
            |> K |> Goal.prove lthy [] [] t
          end;

        (* FIXME don't use user_eqn (cf. constructor view reduction),
                 instead generate "sel" and "code" theorems ourselves *)
        fun prove_sel
          ((fun_name, {ctr_specs, nested_maps, nested_map_idents, nested_map_comps, ...}),
            disc_eqns) exclsss sel_eqn =
          let
            val (SOME ctr_spec) = find_first (equal (#ctr sel_eqn) o #ctr) ctr_specs;
            val ctr_no = find_index (equal (#ctr sel_eqn) o #ctr) ctr_specs;
            val prems = the_default (maps (invert_prems o #prems) disc_eqns)
                (find_first (equal ctr_no o #ctr_no) disc_eqns |> Option.map #prems);
            val sel_corec = find_index (equal (#sel sel_eqn)) (#sels ctr_spec)
              |> nth (#sel_corecs ctr_spec);
            val k = 1 + ctr_no;
            val m = length prems;
            val t = #user_eqn sel_eqn
              |> abstract 0 (List.rev (#fun_args sel_eqn)) (* FIXME do this in dissect_\<dots> *)
              |> curry Logic.list_implies (map HOLogic.mk_Trueprop prems)
              |> curry Logic.list_all (map dest_Free (#fun_args sel_eqn));
          in
            mk_primcorec_eq_tac lthy def_thms sel_corec k m exclsss
              nested_maps nested_map_idents nested_map_comps
            |> K |> Goal.prove lthy [] [] t
          end;

        val disc_notes =
          fun_names ~~
            map3 (map oo prove_disc) (take (length disc_eqnss) corec_specs) exclssss disc_eqnss
          |> map (fn (fun_name, thms) =>
            ((Binding.qualify true fun_name (@{binding disc}), simp_attrs), [(thms, [])]));
        val sel_notes =
          fun_names ~~
            map3 (map oo prove_sel) (fun_names ~~ corec_specs ~~ disc_eqnss) exclssss sel_eqnss
          |> map (fn (fun_name, thms) =>
            ((Binding.qualify true fun_name (@{binding sel}), simp_attrs), [(thms, [])]));
      in
        lthy |> snd o Local_Theory.notes (disc_notes @ sel_notes)
      end;
  in
    lthy'
    |> Proof.theorem NONE (curry (op #->) (fold_map Local_Theory.define defs) o prove) obligationss
    |> Proof.refine (Method.primitive_text I)
    |> Seq.hd
  end

fun add_primcorec_cmd seq (raw_fixes, raw_specs) lthy =
  let
    val (fixes, specs) = fst (Specification.read_spec raw_fixes raw_specs lthy);
  in
    add_primcorec seq fixes specs lthy
    handle ERROR str => primrec_error str
  end
  handle Primrec_Error (str, eqns) =>
    if null eqns
    then error ("primcorec error:\n  " ^ str)
    else error ("primcorec error:\n  " ^ str ^ "\nin\n  " ^
      space_implode "\n  " (map (quote o Syntax.string_of_term lthy) eqns))

end;
