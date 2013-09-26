(*  Title:      HOL/BNF/Tools/bnf_fp_rec_sugar.ML
    Author:     Lorenz Panny, TU Muenchen
    Copyright   2013

Recursor and corecursor sugar.
*)

signature BNF_FP_REC_SUGAR =
sig
  val add_primrec_cmd: (binding * string option * mixfix) list ->
    (Attrib.binding * string) list -> local_theory -> local_theory;
  val add_primcorecursive_cmd: bool ->
    (binding * string option * mixfix) list * ((Attrib.binding * string) * string option) list ->
    Proof.context -> Proof.state
  val add_primcorec_cmd: bool ->
    (binding * string option * mixfix) list * ((Attrib.binding * string) * string option) list ->
    local_theory -> local_theory
end;

structure BNF_FP_Rec_Sugar : BNF_FP_REC_SUGAR =
struct

open BNF_Util
open BNF_FP_Util
open BNF_FP_Rec_Sugar_Util
open BNF_FP_Rec_Sugar_Tactics

val codeN = "code"
val ctrN = "ctr"
val discN = "disc"
val selN = "sel"

val nitpick_attrs = @{attributes [nitpick_simp]};
val code_nitpick_simp_attrs = Code.add_default_eqn_attrib :: nitpick_attrs;
val simp_attrs = @{attributes [simp]};

exception Primrec_Error of string * term list;

fun primrec_error str = raise Primrec_Error (str, []);
fun primrec_error_eqn str eqn = raise Primrec_Error (str, [eqn]);
fun primrec_error_eqns str eqns = raise Primrec_Error (str, eqns);

fun finds eq = fold_map (fn x => List.partition (curry eq x) #>> pair x);

val free_name = try (fn Free (v, _) => v);
val const_name = try (fn Const (v, _) => v);
val undef_const = Const (@{const_name undefined}, dummyT);

fun permute_args n t = list_comb (t, map Bound (0 :: (n downto 1)))
  |> fold (K (Term.abs (Name.uu, dummyT))) (0 upto n);
val abs_tuple = HOLogic.tupled_lambda o HOLogic.mk_tuple;
fun drop_All t = subst_bounds (strip_qnt_vars @{const_name all} t |> map Free |> rev,
  strip_qnt_body @{const_name all} t)
fun abstract vs =
  let fun a n (t $ u) = a n t $ a n u
        | a n (Abs (v, T, b)) = Abs (v, T, a (n + 1) b)
        | a n t = let val idx = find_index (equal t) vs in
            if idx < 0 then t else Bound (n + idx) end
  in a 0 end;
fun mk_prod1 Ts (t, u) = HOLogic.pair_const (fastype_of1 (Ts, t)) (fastype_of1 (Ts, u)) $ t $ u;
fun mk_tuple1 Ts = the_default HOLogic.unit o try (foldr1 (mk_prod1 Ts));

fun get_indices fixes t = map (fst #>> Binding.name_of #> Free) fixes
  |> map_index (fn (i, v) => if exists_subterm (equal v) t then SOME i else NONE)
  |> map_filter I;


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
    val num_nonfrees = length nonfrees;
    val _ = num_nonfrees = 1 orelse if num_nonfrees = 0 then
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

      fun make_direct_type _ = dummyT; (* FIXME? *)

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

    val ((n2m, rec_specs, _, induct_thm, induct_thms), lthy') =
      rec_specs_of bs arg_Ts res_Ts (get_indices fixes) callssss lthy;

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
          [(inductN, if n2m then [induct_thm] else [], []),
           (simpsN, simp_thms, code_nitpick_simp_attrs @ simp_attrs)]
          |> filter_out (null o #2)
          |> map (fn (thmN, thms, attrs) =>
            ((Binding.qualify true fun_name (Binding.name thmN), attrs), [(thms, [])]));
      in
        lthy |> Local_Theory.notes notes
      end;

    val common_name = mk_common_name fun_names;

    val common_notes =
      [(inductN, if n2m then [induct_thm] else [], [])]
      |> filter_out (null o #2)
      |> map (fn (thmN, thms, attrs) =>
        ((Binding.qualify true common_name (Binding.name thmN), attrs), [(thms, [])]));
  in
    lthy'
    |> fold_map Local_Theory.define defs
    |-> snd oo (fn def_thms' => fold_map3 (prove def_thms') (take actual_nn rec_specs)
      (take actual_nn induct_thms) funs_data)
    |> Local_Theory.notes common_notes |> snd
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
      space_implode "\n  " (map (quote o Syntax.string_of_term lthy) eqns));



(* Primcorec *)

type co_eqn_data_disc = {
  fun_name: string,
  fun_T: typ,
  fun_args: term list,
  ctr: term,
  ctr_no: int, (*###*)
  disc: term,
  prems: term list,
  auto_gen: bool,
  user_eqn: term
};
type co_eqn_data_sel = {
  fun_name: string,
  fun_T: typ,
  fun_args: term list,
  ctr: term,
  sel: term,
  rhs_term: term,
  user_eqn: term
};
datatype co_eqn_data =
  Disc of co_eqn_data_disc |
  Sel of co_eqn_data_sel;

fun co_dissect_eqn_disc sequential fun_names corec_specs prems' concl matchedsss =
  let
    fun find_subterm p = let (* FIXME \<exists>? *)
      fun f (t as u $ v) = if p t then SOME t else merge_options (f u, f v)
        | f t = if p t then SOME t else NONE
      in f end;

    val applied_fun = concl
      |> find_subterm (member ((op =) o apsnd SOME) fun_names o try (fst o dest_Free o head_of))
      |> the
      handle Option.Option => primrec_error_eqn "malformed discriminator equation" concl;
    val ((fun_name, fun_T), fun_args) = strip_comb applied_fun |>> dest_Free;
    val {ctr_specs, ...} = the (AList.lookup (op =) (fun_names ~~ corec_specs) fun_name);

    val discs = map #disc ctr_specs;
    val ctrs = map #ctr ctr_specs;
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
    val ctr = #ctr (nth ctr_specs ctr_no);

    val catch_all = try (fst o dest_Free o the_single) prems' = SOME Name.uu_;
    val matchedss = AList.lookup (op =) matchedsss fun_name |> the_default [];
    val prems = map (abstract (List.rev fun_args)) prems';
    val real_prems =
      (if catch_all orelse sequential then maps negate_disj matchedss else []) @
      (if catch_all then [] else prems);

    val matchedsss' = AList.delete (op =) fun_name matchedsss
      |> cons (fun_name, if sequential then matchedss @ [prems] else matchedss @ [real_prems]);

    val user_eqn =
      (real_prems, betapply (#disc (nth ctr_specs ctr_no), applied_fun))
      |>> map HOLogic.mk_Trueprop ||> HOLogic.mk_Trueprop
      |> Logic.list_implies;
  in
    (Disc {
      fun_name = fun_name,
      fun_T = fun_T,
      fun_args = fun_args,
      ctr = ctr,
      ctr_no = ctr_no,
      disc = #disc (nth ctr_specs ctr_no),
      prems = real_prems,
      auto_gen = catch_all,
      user_eqn = user_eqn
    }, matchedsss')
  end;

fun co_dissect_eqn_sel fun_names corec_specs eqn' of_spec eqn =
  let
    val (lhs, rhs) = HOLogic.dest_eq eqn
      handle TERM _ =>
        primrec_error_eqn "malformed function equation (expected \"lhs = rhs\")" eqn;
    val sel = head_of lhs;
    val ((fun_name, fun_T), fun_args) = dest_comb lhs |> snd |> strip_comb |> apfst dest_Free
      handle TERM _ =>
        primrec_error_eqn "malformed selector argument in left-hand side" eqn;
    val corec_spec = the (AList.lookup (op =) (fun_names ~~ corec_specs) fun_name)
      handle Option.Option => primrec_error_eqn "malformed selector argument in left-hand side" eqn;
    val ctr_spec =
      if is_some of_spec
      then the (find_first (equal (the of_spec) o #ctr) (#ctr_specs corec_spec))
      else #ctr_specs corec_spec |> filter (exists (equal sel) o #sels) |> the_single
        handle List.Empty => primrec_error_eqn "ambiguous selector - use \"of\"" eqn;
    val user_eqn = drop_All eqn';
  in
    Sel {
      fun_name = fun_name,
      fun_T = fun_T,
      fun_args = fun_args,
      ctr = #ctr ctr_spec,
      sel = sel,
      rhs_term = rhs,
      user_eqn = user_eqn
    }
  end;

fun co_dissect_eqn_ctr sequential fun_names corec_specs eqn' imp_prems imp_rhs matchedsss =
  let
    val (lhs, rhs) = HOLogic.dest_eq imp_rhs;
    val fun_name = head_of lhs |> fst o dest_Free;
    val {ctr_specs, ...} = the (AList.lookup (op =) (fun_names ~~ corec_specs) fun_name);
    val (ctr, ctr_args) = strip_comb rhs;
    val {disc, sels, ...} = the (find_first (equal ctr o #ctr) ctr_specs)
      handle Option.Option => primrec_error_eqn "not a constructor" ctr;

    val disc_imp_rhs = betapply (disc, lhs);
    val (maybe_eqn_data_disc, matchedsss') = if length ctr_specs = 1
      then (NONE, matchedsss)
      else apfst SOME (co_dissect_eqn_disc
          sequential fun_names corec_specs imp_prems disc_imp_rhs matchedsss);

    val sel_imp_rhss = (sels ~~ ctr_args)
      |> map (fn (sel, ctr_arg) => HOLogic.mk_eq (betapply (sel, lhs), ctr_arg));

(*
val _ = tracing ("reduced\n    " ^ Syntax.string_of_term @{context} imp_rhs ^ "\nto\n    \<cdot> " ^
 (is_some maybe_eqn_data_disc ? K (Syntax.string_of_term @{context} disc_imp_rhs ^ "\n    \<cdot> ")) "" ^
 space_implode "\n    \<cdot> " (map (Syntax.string_of_term @{context}) sel_imp_rhss));
*)

    val eqns_data_sel =
      map (co_dissect_eqn_sel fun_names corec_specs eqn' (SOME ctr)) sel_imp_rhss;
  in
    (the_list maybe_eqn_data_disc @ eqns_data_sel, matchedsss')
  end;

fun co_dissect_eqn sequential fun_names corec_specs eqn' of_spec matchedsss =
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
      co_dissect_eqn_disc sequential fun_names corec_specs imp_prems imp_rhs matchedsss
      |>> single
    else if member (op =) sels head then
      ([co_dissect_eqn_sel fun_names corec_specs eqn' of_spec imp_rhs], matchedsss)
    else if is_Free head andalso member (op =) fun_names (fst (dest_Free head)) then
      co_dissect_eqn_ctr sequential fun_names corec_specs eqn' imp_prems imp_rhs matchedsss
    else
      primrec_error_eqn "malformed function equation" eqn
  end;

fun build_corec_arg_disc ctr_specs {fun_args, ctr_no, prems, ...} =
  if is_none (#pred (nth ctr_specs ctr_no)) then I else
    mk_conjs prems
    |> curry subst_bounds (List.rev fun_args)
    |> HOLogic.tupled_lambda (HOLogic.mk_tuple fun_args)
    |> K |> nth_map (the (#pred (nth ctr_specs ctr_no)));

fun build_corec_arg_no_call sel_eqns sel =
  find_first (equal sel o #sel) sel_eqns
  |> try (fn SOME {fun_args, rhs_term, ...} => abs_tuple fun_args rhs_term)
  |> the_default undef_const
  |> K;

fun build_corec_args_direct_call lthy has_call sel_eqns sel =
  let
    val maybe_sel_eqn = find_first (equal sel o #sel) sel_eqns;
  in
    if is_none maybe_sel_eqn then (I, I, I) else
    let
      val {fun_args, rhs_term, ... } = the maybe_sel_eqn;
      fun rewrite_q _ t = if has_call t then @{term False} else @{term True};
      fun rewrite_g _ t = if has_call t then undef_const else t;
      fun rewrite_h bound_Ts t =
        if has_call t then mk_tuple1 bound_Ts (snd (strip_comb t)) else undef_const;
      fun massage f t = massage_direct_corec_call lthy has_call f [] rhs_term |> abs_tuple fun_args;
    in
      (massage rewrite_q,
       massage rewrite_g,
       massage rewrite_h)
    end
  end;

fun build_corec_arg_indirect_call lthy has_call sel_eqns sel =
  let
    val maybe_sel_eqn = find_first (equal sel o #sel) sel_eqns;
  in
    if is_none maybe_sel_eqn then I else
    let
      val {fun_args, rhs_term, ...} = the maybe_sel_eqn;
      fun rewrite bound_Ts U T (Abs (v, V, b)) = Abs (v, V, rewrite (V :: bound_Ts) U T b)
        | rewrite bound_Ts U T (t as _ $ _) =
          let val (u, vs) = strip_comb t in
            if is_Free u andalso has_call u then
              Inr_const U T $ mk_tuple1 bound_Ts vs
            else if try (fst o dest_Const) u = SOME @{const_name prod_case} then
              map (rewrite bound_Ts U T) vs |> chop 1 |>> HOLogic.mk_split o the_single |> list_comb
            else
              list_comb (rewrite bound_Ts U T u, map (rewrite bound_Ts U T) vs)
          end
        | rewrite _ U T t =
          if is_Free t andalso has_call t then Inr_const U T $ HOLogic.unit else t;
      fun massage t =
        massage_indirect_corec_call lthy has_call rewrite [] (range_type (fastype_of t)) rhs_term
        |> abs_tuple fun_args;
    in
      massage
    end
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
        #> fold (fn (sel, n) => nth_map n (build_corec_arg_no_call sel_eqns sel)) no_calls'
        #> fold (fn (sel, (q, g, h)) =>
          let val (fq, fg, fh) = build_corec_args_direct_call lthy has_call sel_eqns sel in
            nth_map q fq o nth_map g fg o nth_map h fh end) direct_calls'
        #> fold (fn (sel, n) => nth_map n
          (build_corec_arg_indirect_call lthy has_call sel_eqns sel)) indirect_calls'
      end
  end;

fun co_build_defs lthy bs mxs has_call arg_Tss corec_specs disc_eqnss sel_eqnss =
  let
    val corec_specs' = take (length bs) corec_specs;
    val corecs = map #corec corec_specs';
    val ctr_specss = map #ctr_specs corec_specs';
    val corec_args = hd corecs
      |> fst o split_last o binder_types o fastype_of
      |> map (Const o pair @{const_name undefined})
      |> fold2 (fold o build_corec_arg_disc) ctr_specss disc_eqnss
      |> fold2 (fold o build_corec_args_sel lthy has_call) sel_eqnss ctr_specss;
    fun currys [] t = t
      | currys Ts t = t $ mk_tuple1 (List.rev Ts) (map Bound (length Ts - 1 downto 0))
          |> fold_rev (Term.abs o pair Name.uu) Ts;

(*
val _ = tracing ("corecursor arguments:\n    \<cdot> " ^
 space_implode "\n    \<cdot> " (map (Syntax.string_of_term lthy) corec_args));
*)

    val exclss' =
      disc_eqnss
      |> map (map (fn x => (#fun_args x, #ctr_no x, #prems x, #auto_gen x))
        #> fst o (fn xs => fold_map (fn x => fn ys => ((x, ys), ys @ [x])) xs [])
        #> maps (uncurry (map o pair)
          #> map (fn ((fun_args, c, x, a), (_, c', y, a')) =>
              ((c, c', a orelse a'), (x, s_not (mk_conjs y)))
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

fun mk_real_disc_eqns fun_binding arg_Ts {ctr_specs, ...} sel_eqns disc_eqns =
  if length disc_eqns <> length ctr_specs - 1 then disc_eqns else
    let
      val n = 0 upto length ctr_specs
        |> the o find_first (fn idx => not (exists (equal idx o #ctr_no) disc_eqns));
      val fun_args = (try (#fun_args o hd) disc_eqns, try (#fun_args o hd) sel_eqns)
        |> the_default (map (curry Free Name.uu) arg_Ts) o merge_options;
      val extra_disc_eqn = {
        fun_name = Binding.name_of fun_binding,
        fun_T = arg_Ts ---> body_type (fastype_of (#ctr (hd ctr_specs))),
        fun_args = fun_args,
        ctr = #ctr (nth ctr_specs n),
        ctr_no = n,
        disc = #disc (nth ctr_specs n),
        prems = maps (negate_conj o #prems) disc_eqns,
        auto_gen = true,
        user_eqn = undef_const};
    in
      chop n disc_eqns ||> cons extra_disc_eqn |> (op @)
    end;

fun add_primcorec simple sequential fixes specs of_specs lthy =
  let
    val (bs, mxs) = map_split (apfst fst) fixes;
    val (arg_Ts, res_Ts) = map (strip_type o snd o fst #>> HOLogic.mk_tupleT) fixes |> split_list;

    val callssss = []; (* FIXME *)

    val ((n2m, corec_specs', _, coinduct_thm, strong_coinduct_thm, coinduct_thms,
          strong_coinduct_thms), lthy') =
      corec_specs_of bs arg_Ts res_Ts (get_indices fixes) callssss lthy;

    val actual_nn = length bs;
    val fun_names = map Binding.name_of bs;
    val corec_specs = take actual_nn corec_specs'; (*###*)

    val eqns_data =
      fold_map2 (co_dissect_eqn sequential fun_names corec_specs) (map snd specs) of_specs []
      |> flat o fst;

    val disc_eqnss' = map_filter (try (fn Disc x => x)) eqns_data
      |> partition_eq ((op =) o pairself #fun_name)
      |> fst o finds (fn (x, ({fun_name, ...} :: _)) => x = fun_name) fun_names
      |> map (sort ((op <) o pairself #ctr_no |> make_ord) o flat o snd);
    val _ = disc_eqnss' |> map (fn x =>
      let val d = duplicates ((op =) o pairself #ctr_no) x in null d orelse
        primrec_error_eqns "excess discriminator equations in definition"
          (maps (fn t => filter (equal (#ctr_no t) o #ctr_no) x) d |> map #user_eqn) end);

    val sel_eqnss = map_filter (try (fn Sel x => x)) eqns_data
      |> partition_eq ((op =) o pairself #fun_name)
      |> fst o finds (fn (x, ({fun_name, ...} :: _)) => x = fun_name) fun_names
      |> map (flat o snd);

    val has_call = exists_subterm (map (fst #>> Binding.name_of #> Free) fixes |> member (op =));
    val arg_Tss = map (binder_types o snd o fst) fixes;
    val disc_eqnss = map5 mk_real_disc_eqns bs arg_Tss corec_specs sel_eqnss disc_eqnss';
    val (defs, exclss') =
      co_build_defs lthy' bs mxs has_call arg_Tss corec_specs disc_eqnss sel_eqnss;

    fun excl_tac (c, c', a) =
      if a orelse c = c' orelse sequential then SOME (K (mk_primcorec_assumption_tac lthy []))
      else if simple then SOME (K (auto_tac lthy))
      else NONE;

(*
val _ = tracing ("exclusiveness properties:\n    \<cdot> " ^
 space_implode "\n    \<cdot> " (maps (map (Syntax.string_of_term lthy o snd)) exclss'));
*)

    val exclss'' = exclss' |> map (map (fn (idx, t) =>
      (idx, (Option.map (Goal.prove lthy [] [] t) (excl_tac idx), t))));
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
          |-> fold (fn ((c, c', _), thm) => nth_map c (nth_map c' (K [thm])));
        val exclssss = (exclss' ~~ taut_thmss |> map (op @), fun_names ~~ corec_specs)
          |-> map2 (fn excls => fn (_, {ctr_specs, ...}) => mk_exclsss excls (length ctr_specs));

        fun prove_disc {ctr_specs, ...} exclsss
            {fun_name, fun_T, fun_args, ctr_no, prems, user_eqn, ...} =
          if Term.aconv_untyped (#disc (nth ctr_specs ctr_no), @{term "\<lambda>x. x = x"}) then [] else
            let
              val {disc_corec, ...} = nth ctr_specs ctr_no;
              val k = 1 + ctr_no;
              val m = length prems;
              val t =
                list_comb (Free (fun_name, fun_T), map Bound (length fun_args - 1 downto 0))
                |> curry betapply (#disc (nth ctr_specs ctr_no)) (*###*)
                |> HOLogic.mk_Trueprop
                |> curry Logic.list_implies (map HOLogic.mk_Trueprop prems)
                |> curry Logic.list_all (map dest_Free fun_args);
            in
              mk_primcorec_disc_tac lthy def_thms disc_corec k m exclsss
              |> K |> Goal.prove lthy [] [] t
              |> pair (#disc (nth ctr_specs ctr_no))
              |> single
            end;

        fun prove_sel {ctr_specs, nested_maps, nested_map_idents, nested_map_comps, ...}
            disc_eqns exclsss {fun_name, fun_T, fun_args, ctr, sel, rhs_term, ...} =
          let
            val SOME ctr_spec = find_first (equal ctr o #ctr) ctr_specs;
            val ctr_no = find_index (equal ctr o #ctr) ctr_specs;
            val prems = the_default (maps (negate_conj o #prems) disc_eqns)
                (find_first (equal ctr_no o #ctr_no) disc_eqns |> Option.map #prems);
            val sel_corec = find_index (equal sel) (#sels ctr_spec)
              |> nth (#sel_corecs ctr_spec);
            val k = 1 + ctr_no;
            val m = length prems;
            val t =
              list_comb (Free (fun_name, fun_T), map Bound (length fun_args - 1 downto 0))
              |> curry betapply sel
              |> rpair (abstract (List.rev fun_args) rhs_term)
              |> HOLogic.mk_Trueprop o HOLogic.mk_eq
              |> curry Logic.list_implies (map HOLogic.mk_Trueprop prems)
              |> curry Logic.list_all (map dest_Free fun_args);
            val (distincts, _, sel_splits, sel_split_asms) = case_thms_of_term lthy [] rhs_term;
          in
            mk_primcorec_sel_tac lthy def_thms distincts sel_splits sel_split_asms nested_maps
              nested_map_idents nested_map_comps sel_corec k m exclsss
            |> K |> Goal.prove lthy [] [] t
            |> pair sel
          end;

        fun prove_ctr disc_alist sel_alist disc_eqns sel_eqns {ctr, disc, sels, collapse, ...} =
          if not (exists (equal ctr o #ctr) disc_eqns)
              andalso not (exists (equal ctr o #ctr) sel_eqns)
            orelse (* don't try to prove theorems when some sel_eqns are missing *)
              filter (equal ctr o #ctr) sel_eqns
              |> fst o finds ((op =) o apsnd #sel) sels
              |> exists (null o snd)
          then [] else
            let
              val (fun_name, fun_T, fun_args, prems) =
                (find_first (equal ctr o #ctr) disc_eqns, find_first (equal ctr o #ctr) sel_eqns)
                |>> Option.map (fn x => (#fun_name x, #fun_T x, #fun_args x, #prems x))
                ||> Option.map (fn x => (#fun_name x, #fun_T x, #fun_args x, []))
                |> the o merge_options;
              val m = length prems;
              val t = filter (equal ctr o #ctr) sel_eqns
                |> fst o finds ((op =) o apsnd #sel) sels
                |> map (snd #> (fn [x] => (List.rev (#fun_args x), #rhs_term x)) #-> abstract)
                |> curry list_comb ctr
                |> curry HOLogic.mk_eq (list_comb (Free (fun_name, fun_T),
                  map Bound (length fun_args - 1 downto 0)))
                |> HOLogic.mk_Trueprop
                |> curry Logic.list_implies (map HOLogic.mk_Trueprop prems)
                |> curry Logic.list_all (map dest_Free fun_args);
              val maybe_disc_thm = AList.lookup (op =) disc_alist disc;
              val sel_thms = map snd (filter (member (op =) sels o fst) sel_alist);
            in
              mk_primcorec_ctr_of_dtr_tac lthy m collapse maybe_disc_thm sel_thms
              |> K |> Goal.prove lthy [] [] t
              |> single
            end;

        val disc_alists = map3 (maps oo prove_disc) corec_specs exclssss disc_eqnss;
        val sel_alists = map4 (map ooo prove_sel) corec_specs disc_eqnss exclssss sel_eqnss;

        val disc_thmss = map (map snd) disc_alists;
        val sel_thmss = map (map snd) sel_alists;
        val ctr_thmss = map5 (maps oooo prove_ctr) disc_alists sel_alists disc_eqnss sel_eqnss
          (map #ctr_specs corec_specs);

        val safess = map (map (not o exists_subterm (member (op =) (map SOME fun_names) o
          try (fst o dest_Free)) o snd o HOLogic.dest_eq o HOLogic.dest_Trueprop o
          Logic.strip_imp_concl o drop_All o prop_of)) ctr_thmss;
        val safe_ctr_thmss = map (map snd o filter fst o (op ~~)) (safess ~~ ctr_thmss);

        val simp_thmss =
          map3 (fn x => fn y => fn z => x @ y @ z) disc_thmss sel_thmss safe_ctr_thmss;

        val common_name = mk_common_name fun_names;

        val anonymous_notes =
          [(flat safe_ctr_thmss, simp_attrs)]
          |> map (fn (thms, attrs) => ((Binding.empty, attrs), [(thms, [])]));

        val notes =
          [(coinductN, map (if n2m then single else K []) coinduct_thms, []),
           (codeN, ctr_thmss(*FIXME*), code_nitpick_simp_attrs),
           (ctrN, ctr_thmss, []),
           (discN, disc_thmss, simp_attrs),
           (selN, sel_thmss, simp_attrs),
           (simpsN, simp_thmss, []),
           (strong_coinductN, map (if n2m then single else K []) strong_coinduct_thms, [])]
          |> maps (fn (thmN, thmss, attrs) =>
            map2 (fn fun_name => fn thms =>
                ((Binding.qualify true fun_name (Binding.name thmN), attrs), [(thms, [])]))
              fun_names (take actual_nn thmss))
          |> filter_out (null o fst o hd o snd);

        val common_notes =
          [(coinductN, if n2m then [coinduct_thm] else [], []),
           (strong_coinductN, if n2m then [strong_coinduct_thm] else [], [])]
          |> filter_out (null o #2)
          |> map (fn (thmN, thms, attrs) =>
            ((Binding.qualify true common_name (Binding.name thmN), attrs), [(thms, [])]));
      in
        lthy |> Local_Theory.notes (anonymous_notes @ notes @ common_notes) |> snd
      end;

    fun after_qed thmss' = fold_map Local_Theory.define defs #-> prove thmss';

    val _ = if not simple orelse forall null obligationss then () else
      primrec_error "need exclusiveness proofs - use primcorecursive instead of primcorec";
  in
    if simple then
      lthy'
      |> after_qed (map (fn [] => []) obligationss)
      |> pair NONE o SOME
    else
      lthy'
      |> Proof.theorem NONE after_qed obligationss
      |> Proof.refine (Method.primitive_text I)
      |> Seq.hd
      |> rpair NONE o SOME
  end;

fun add_primcorec_ursive_cmd simple seq (raw_fixes, raw_specs') lthy =
  let
    val (raw_specs, of_specs) = split_list raw_specs' ||> map (Option.map (Syntax.read_term lthy));
    val ((fixes, specs), _) = Specification.read_spec raw_fixes raw_specs lthy;
  in
    add_primcorec simple seq fixes specs of_specs lthy
    handle ERROR str => primrec_error str
  end
  handle Primrec_Error (str, eqns) =>
    if null eqns
    then error ("primcorec error:\n  " ^ str)
    else error ("primcorec error:\n  " ^ str ^ "\nin\n  " ^
      space_implode "\n  " (map (quote o Syntax.string_of_term lthy) eqns));

val add_primcorecursive_cmd = (the o fst) ooo add_primcorec_ursive_cmd false;
val add_primcorec_cmd = (the o snd) ooo add_primcorec_ursive_cmd true;

end;
