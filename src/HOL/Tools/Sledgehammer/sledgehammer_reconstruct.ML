(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_reconstruct.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Steffen Juilf Smolka, TU Muenchen

*)

signature SLEDGEHAMMER_PROOF_RECONSTRUCT =
sig
  type isar_params = ATP_Proof_Reconstruct.isar_params
  type one_line_params = ATP_Proof_Reconstruct.one_line_params
  val isar_proof_text :
    Proof.context -> bool -> isar_params -> one_line_params -> string
  val proof_text :
    Proof.context -> bool -> isar_params -> int -> one_line_params -> string
end;

structure Sledgehammer_Reconstruct : SLEDGEHAMMER_PROOF_RECONSTRUCT =
struct

open ATP_Util
open ATP_Proof
open ATP_Problem_Generate
open ATP_Proof_Reconstruct
open String_Redirect

(** Type annotations **)

fun post_traverse_term_type' f _ (t as Const (_, T)) s = f t T s
  | post_traverse_term_type' f _ (t as Free (_, T)) s = f t T s
  | post_traverse_term_type' f _ (t as Var (_, T)) s = f t T s
  | post_traverse_term_type' f env (t as Bound i) s = f t (nth env i) s
  | post_traverse_term_type' f env (Abs (x, T1, b)) s =
    let
      val ((b', s'), T2) = post_traverse_term_type' f (T1 :: env) b s
    in f (Abs (x, T1, b')) (T1 --> T2) s' end
  | post_traverse_term_type' f env (u $ v) s =
    let
      val ((u', s'), Type (_, [_, T])) = post_traverse_term_type' f env u s
      val ((v', s''), _) = post_traverse_term_type' f env v s'
    in f (u' $ v') T s'' end

fun post_traverse_term_type f s t =
  post_traverse_term_type' (fn t => fn T => fn s => (f t T s, T)) [] t s |> fst
fun post_fold_term_type f s t =
  post_traverse_term_type (fn t => fn T => fn s => (t, f t T s)) s t |> snd

(* Data structures, orders *)
val cost_ord = prod_ord int_ord (prod_ord int_ord int_ord)

structure Var_Set_Tab = Table(
  type key = indexname list
  val ord = list_ord Term_Ord.fast_indexname_ord)

(* (1) Generalize Types *)
fun generalize_types ctxt t =
  t |> map_types (fn _ => dummyT)
    |> Syntax.check_term
         (Proof_Context.set_mode Proof_Context.mode_pattern ctxt)

(* (2) Typing-spot Table *)
local
fun key_of_atype (TVar (idxn, _)) =
    Ord_List.insert Term_Ord.fast_indexname_ord idxn
  | key_of_atype _ = I
fun key_of_type T = fold_atyps key_of_atype T []
fun update_tab t T (tab, pos) =
  (case key_of_type T of
     [] => tab
   | key =>
     let val cost = (size_of_typ T, (size_of_term t, pos)) in
       case Var_Set_Tab.lookup tab key of
         NONE => Var_Set_Tab.update_new (key, cost) tab
       | SOME old_cost =>
         (case cost_ord (cost, old_cost) of
            LESS => Var_Set_Tab.update (key, cost) tab
          | _ => tab)
     end,
   pos + 1)
in
val typing_spot_table =
  post_fold_term_type update_tab (Var_Set_Tab.empty, 0) #> fst
end

(* (3) Reverse-Greedy *)
fun reverse_greedy typing_spot_tab =
  let
    fun update_count z =
      fold (fn tvar => fn tab =>
        let val c = Vartab.lookup tab tvar |> the_default 0 in
          Vartab.update (tvar, c + z) tab
        end)
    fun superfluous tcount =
      forall (fn tvar => the (Vartab.lookup tcount tvar) > 1)
    fun drop_superfluous (tvars, (_, (_, spot))) (spots, tcount) =
      if superfluous tcount tvars then (spots, update_count ~1 tvars tcount)
      else (spot :: spots, tcount)
    val (typing_spots, tvar_count_tab) =
      Var_Set_Tab.fold
        (fn kv as (k, _) => apfst (cons kv) #> apsnd (update_count 1 k))
        typing_spot_tab ([], Vartab.empty)
      |>> sort_distinct (rev_order o cost_ord o pairself snd)
  in fold drop_superfluous typing_spots ([], tvar_count_tab) |> fst end

(* (4) Introduce Annotations *)
fun introduce_annotations thy spots t t' =
  let
    val get_types = post_fold_term_type (K cons) []
    fun match_types tp =
      fold (Sign.typ_match thy) (op ~~ (pairself get_types tp)) Vartab.empty
    fun unica' b x [] = if b then [x] else []
      | unica' b x (y :: ys) =
        if x = y then unica' false x ys
        else unica' true y ys |> b ? cons x
    fun unica ord xs =
      case sort ord xs of x :: ys => unica' true x ys | [] => []
    val add_all_tfree_namesT = fold_atyps (fn TFree (x, _) => cons x | _ => I)
    fun erase_unica_tfrees env =
      let
        val unica =
          Vartab.fold (add_all_tfree_namesT o snd o snd) env []
          |> unica fast_string_ord
        val erase_unica = map_atyps
          (fn T as TFree (s, _) =>
              if Ord_List.member fast_string_ord unica s then dummyT else T
            | T => T)
      in Vartab.map (K (apsnd erase_unica)) env end
    val env = match_types (t', t) |> erase_unica_tfrees
    fun get_annot env (TFree _) = (false, (env, dummyT))
      | get_annot env (T as TVar (v, S)) =
        let val T' = Envir.subst_type env T in
          if T' = dummyT then (false, (env, dummyT))
          else (true, (Vartab.update (v, (S, dummyT)) env, T'))
        end
      | get_annot env (Type (S, Ts)) =
        (case fold_rev (fn T => fn (b, (env, Ts)) =>
                  let
                    val (b', (env', T)) = get_annot env T
                  in (b orelse b', (env', T :: Ts)) end)
                Ts (false, (env, [])) of
           (true, (env', Ts)) => (true, (env', Type (S, Ts)))
         | (false, (env', _)) => (false, (env', dummyT)))
    fun post1 _ T (env, cp, ps as p :: ps', annots) =
        if p <> cp then
          (env, cp + 1, ps, annots)
        else
          let val (_, (env', T')) = get_annot env T in
            (env', cp + 1, ps', (p, T') :: annots)
          end
      | post1 _ _ accum = accum
    val (_, _, _, annots) = post_fold_term_type post1 (env, 0, spots, []) t'
    fun post2 t _ (cp, annots as (p, T) :: annots') =
        if p <> cp then (t, (cp + 1, annots))
        else (Type.constraint T t, (cp + 1, annots'))
      | post2 t _ x = (t, x)
  in post_traverse_term_type post2 (0, rev annots) t |> fst end

(* (5) Annotate *)
fun annotate_types ctxt t =
  let
    val thy = Proof_Context.theory_of ctxt
    val t' = generalize_types ctxt t
    val typing_spots =
      t' |> typing_spot_table
         |> reverse_greedy
         |> sort int_ord
  in introduce_annotations thy typing_spots t t' end

fun string_for_proof ctxt type_enc lam_trans i n =
  let
    fun fix_print_mode f x =
      Print_Mode.setmp (filter (curry (op =) Symbol.xsymbolsN)
                               (print_mode_value ())) f x
    fun do_indent ind = replicate_string (ind * indent_size) " "
    fun do_free (s, T) =
      maybe_quote s ^ " :: " ^
      maybe_quote (fix_print_mode (Syntax.string_of_typ ctxt) T)
    fun do_label l = if l = no_label then "" else string_for_label l ^ ": "
    fun do_have qs =
      (if member (op =) qs Moreover then "moreover " else "") ^
      (if member (op =) qs Ultimately then "ultimately " else "") ^
      (if member (op =) qs Then then
         if member (op =) qs Show then "thus" else "hence"
       else
         if member (op =) qs Show then "show" else "have")
    val do_term =
      maybe_quote o fix_print_mode (Syntax.string_of_term ctxt)
      o annotate_types ctxt
    val reconstr = Metis (type_enc, lam_trans)
    fun do_facts (ls, ss) =
      reconstructor_command reconstr 1 1 [] 0
          (ls |> sort_distinct (prod_ord string_ord int_ord),
           ss |> sort_distinct string_ord)
    and do_step ind (Fix xs) =
        do_indent ind ^ "fix " ^ space_implode " and " (map do_free xs) ^ "\n"
      | do_step ind (Let (t1, t2)) =
        do_indent ind ^ "let " ^ do_term t1 ^ " = " ^ do_term t2 ^ "\n"
      | do_step ind (Assume (l, t)) =
        do_indent ind ^ "assume " ^ do_label l ^ do_term t ^ "\n"
      | do_step ind (Prove (qs, l, t, By_Metis facts)) =
        do_indent ind ^ do_have qs ^ " " ^
        do_label l ^ do_term t ^ " " ^ do_facts facts ^ "\n"
      | do_step ind (Prove (qs, l, t, Case_Split (proofs, facts))) =
        implode (map (prefix (do_indent ind ^ "moreover\n") o do_block ind)
                     proofs) ^
        do_indent ind ^ do_have qs ^ " " ^ do_label l ^ do_term t ^ " " ^
        do_facts facts ^ "\n"
    and do_steps prefix suffix ind steps =
      let val s = implode (map (do_step ind) steps) in
        replicate_string (ind * indent_size - size prefix) " " ^ prefix ^
        String.extract (s, ind * indent_size,
                        SOME (size s - ind * indent_size - 1)) ^
        suffix ^ "\n"
      end
    and do_block ind proof = do_steps "{ " " }" (ind + 1) proof
    (* One-step proofs are pointless; better use the Metis one-liner
       directly. *)
    and do_proof [Prove (_, _, _, By_Metis _)] = ""
      | do_proof proof =
        (if i <> 1 then "prefer " ^ string_of_int i ^ "\n" else "") ^
        do_indent 0 ^ "proof -\n" ^ do_steps "" "" 1 proof ^ do_indent 0 ^
        (if n <> 1 then "next" else "qed")
  in do_proof end

fun minimize_locally ctxt type_enc lam_trans proof =
  let
    (* Merging spots, greedy algorithm *)
    fun cost (Prove (_, _ , t, _)) = Term.size_of_term t
      | cost _ = ~1
    fun can_merge (Prove (_, lbl, _, By_Metis _))
                  (Prove (_, _, _, By_Metis _)) =
        (lbl = no_label)
      | can_merge _ _ = false
    val merge_spots = 
      fold_index (fn (i, s2) => fn (s1, pile) =>
          (s2, pile |> can_merge s1 s2 ? cons (i, cost s1)))
        (tl proof) (hd proof, [])
    |> snd |> sort (rev_order o int_ord o pairself snd) |> map fst

    (* Enrich context with facts *)
    val thy = Proof_Context.theory_of ctxt
    fun sorry t = Skip_Proof.make_thm thy (HOLogic.mk_Trueprop t) (* FIXME: mk_Trueprop always ok? *)
    fun enrich_ctxt' (Prove (_, lbl, t, _)) ctxt = 
        ctxt |> lbl <> no_label
          ? Proof_Context.put_thms false (string_for_label lbl, SOME [sorry t])
      | enrich_ctxt' _ ctxt = ctxt
    val rich_ctxt = fold enrich_ctxt' proof ctxt

    (* Timing *)
    fun take_time tac arg =
      let
        val t_start = Timing.start ()
      in
        (tac arg ; Timing.result t_start |> #cpu)
      end
    fun try_metis (Prove (qs, _, t, By_Metis fact_names)) s0 =
      let
        fun thmify (Prove (_, _, t, _)) = sorry t
        val facts =
          fact_names
          |>> map string_for_label
          |> op @
          |> map (Proof_Context.get_thm rich_ctxt)
          |> (if member (op =) qs Then then cons (the s0 |> thmify) else I)
        val goal = Goal.prove ctxt [] [] (HOLogic.mk_Trueprop t) (* FIXME: mk_Trueprop always ok? *)
        fun tac {context = ctxt, prems = _} =
          Metis_Tactic.metis_tac [type_enc] lam_trans ctxt facts 1
      in
        take_time (fn () => goal tac)
      end
  
    (* Merging *)
    fun merge (Prove (qs1, _, _, By_Metis (ls1, ss1))) 
              (Prove (qs2, lbl , t, By_Metis (ls2, ss2))) =
      let
        val qs =
          inter (op =) qs1 qs2 (* FIXME: Is this correct? *)
          |> member (op =) (union (op =) qs1 qs2) Ultimately ? cons Ultimately
          |> member (op =) qs2 Show ? cons Show
      in Prove (qs, lbl, t, By_Metis (ls1 @ ls2, ss1 @ ss2)) end
    fun try_merge proof i =
      let
        val (front, s0, s1, s2, tail) = 
          case (proof, i) of
            ((s1 :: s2 :: proof), 0) => ([], NONE, s1, s2, proof)
          | _ =>
            let val (front, s0 :: s1 :: s2 :: tail) = chop (i - 1) proof in
              (front, SOME s0, s1, s2, tail)
            end
        val s12 = merge s1 s2
        val t1 = try_metis s1 s0 ()
        val t2 = try_metis s2 (SOME s1) ()
        val tlimit = t1 + t2 |> Time.toReal |> curry Real.* 1.2 |> Time.fromReal
      in
        (TimeLimit.timeLimit tlimit (try_metis s12 s0) ();
         SOME (front @ (case s0 of
                          NONE => s12 :: tail
                        | SOME s => s :: s12 :: tail)))
        handle _ => NONE
      end
    fun merge_steps proof [] = proof
      | merge_steps proof (i :: is) = 
        case try_merge proof i of 
          NONE => merge_steps proof is
        | SOME proof' =>
          merge_steps proof' (map (fn j => if j > i then j - 1 else j) is)
  in merge_steps proof merge_spots end

fun isar_proof_text ctxt isar_proof_requested
        (debug, isar_shrink_factor, pool, fact_names, sym_tab, atp_proof, goal)
        (one_line_params as (_, _, _, _, subgoal, subgoal_count)) =
  let
    val isar_shrink_factor =
      (if isar_proof_requested then 1 else 2) * isar_shrink_factor
    val (params, hyp_ts, concl_t) = strip_subgoal ctxt goal subgoal
    val frees = fold Term.add_frees (concl_t :: hyp_ts) []
    val one_line_proof = one_line_proof_text 0 one_line_params
    val type_enc =
      if is_typed_helper_used_in_atp_proof atp_proof then full_typesN
      else partial_typesN
    val lam_trans = lam_trans_from_atp_proof atp_proof metis_default_lam_trans

    fun isar_proof_of () =
      let
        val atp_proof =
          atp_proof
          |> clean_up_atp_proof_dependencies
          |> nasty_atp_proof pool
          |> map_term_names_in_atp_proof repair_name
          |> decode_lines ctxt sym_tab
          |> rpair [] |-> fold_rev (add_line fact_names)
          |> repair_waldmeister_endgame
          |> rpair [] |-> fold_rev add_nontrivial_line
          |> rpair (0, [])
          |-> fold_rev (add_desired_line isar_shrink_factor fact_names frees)
          |> snd
        val conj_name = conjecture_prefix ^ string_of_int (length hyp_ts)
        val conjs =
          atp_proof
          |> map_filter (fn Inference_Step (name as (_, ss), _, _, []) =>
                            if member (op =) ss conj_name then SOME name else NONE
                          | _ => NONE)
        fun dep_of_step (Definition_Step _) = NONE
          | dep_of_step (Inference_Step (name, _, _, from)) = SOME (from, name)
        val ref_graph = atp_proof |> map_filter dep_of_step |> make_ref_graph
        val axioms = axioms_of_ref_graph ref_graph conjs
        val tainted = tainted_atoms_of_ref_graph ref_graph conjs
        val props =
          Symtab.empty
          |> fold (fn Definition_Step _ => I (* FIXME *)
                    | Inference_Step ((s, _), t, _, _) =>
                      Symtab.update_new (s,
                          t |> fold forall_of (map Var (Term.add_vars t []))
                            |> member (op = o apsnd fst) tainted s ? s_not))
                  atp_proof
        fun prop_of_clause c =
          fold (curry s_disj) (map_filter (Symtab.lookup props o fst) c)
               @{term False}
        fun label_of_clause [name] = raw_label_for_name name
          | label_of_clause c = (space_implode "___" (map fst c), 0)
        fun maybe_show outer c =
          (outer andalso length c = 1 andalso subset (op =) (c, conjs))
          ? cons Show
        fun do_have outer qs (gamma, c) =
          Prove (maybe_show outer c qs, label_of_clause c, prop_of_clause c,
                 By_Metis (fold (add_fact_from_dependency fact_names
                                 o the_single) gamma ([], [])))
        fun do_inf outer (Have z) = do_have outer [] z
          | do_inf outer (Hence z) = do_have outer [Then] z
          | do_inf outer (Cases cases) =
            let val c = succedent_of_cases cases in
              Prove (maybe_show outer c [Ultimately], label_of_clause c,
                     prop_of_clause c,
                     Case_Split (map (do_case false) cases, ([], [])))
            end
        and do_case outer (c, infs) =
          Assume (label_of_clause c, prop_of_clause c) ::
          map (do_inf outer) infs
        val isar_proof =
          (if null params then [] else [Fix params]) @
           (ref_graph
           |> redirect_graph axioms tainted
           |> chain_direct_proof
           |> map (do_inf true)
           |> kill_duplicate_assumptions_in_proof
           |> kill_useless_labels_in_proof
           |> relabel_proof
           |> minimize_locally ctxt type_enc lam_trans)
          |> string_for_proof ctxt type_enc lam_trans subgoal subgoal_count
      in
        case isar_proof of
          "" =>
          if isar_proof_requested then
            "\nNo structured proof available (proof too short)."
          else
            ""
        | _ =>
          "\n\n" ^ (if isar_proof_requested then "Structured proof"
                    else "Perhaps this will work") ^
          ":\n" ^ Markup.markup Isabelle_Markup.sendback isar_proof
      end
    val isar_proof =
      if debug then
        isar_proof_of ()
      else case try isar_proof_of () of
        SOME s => s
      | NONE => if isar_proof_requested then
                  "\nWarning: The Isar proof construction failed."
                else
                  ""
  in one_line_proof ^ isar_proof end

fun proof_text ctxt isar_proof isar_params num_chained
               (one_line_params as (preplay, _, _, _, _, _)) =
  (if case preplay of Failed_to_Play _ => true | _ => isar_proof then
     isar_proof_text ctxt isar_proof isar_params
   else
     one_line_proof_text num_chained) one_line_params

end;
