(*  Title:      HOL/Tools/choice_specification.ML
    Author:     Sebastian Skalberg, TU Muenchen

Package for defining constants by specification.
*)

signature CHOICE_SPECIFICATION =
sig
  val close_form : term -> term
  val add_specification: (bstring * xstring * bool) list -> theory * thm -> theory * thm
end

structure Choice_Specification: CHOICE_SPECIFICATION =
struct

local

fun mk_definitional [] arg = arg
  | mk_definitional ((thname, cname, covld) :: cos) (thy, thm) =
      (case HOLogic.dest_Trueprop (Thm.concl_of thm) of
        Const (\<^const_name>\<open>Ex\<close>, _) $ P =>
          let
            val ctype = domain_type (type_of P)
            val cname_full = Sign.intern_const thy cname
            val cdefname =
              if thname = ""
              then Thm.def_name (Long_Name.base_name cname)
              else thname
            val def_eq =
              Logic.mk_equals (Const (cname_full, ctype), HOLogic.choice_const ctype $ P)
            val (thms, thy') =
              Global_Theory.add_defs covld [((Binding.name cdefname, def_eq), [])] thy
            val thm' = [thm,hd thms] MRS @{thm exE_some}
          in
            mk_definitional cos (thy',thm')
          end
      | _ => raise THM ("Bad specification theorem", 0, [thm]))

in

fun add_specification cos =
  mk_definitional cos #> apsnd Drule.export_without_context

end


(* Collect all intances of constants in term *)

fun collect_consts (t $ u, tms) = collect_consts (u, collect_consts (t, tms))
  | collect_consts (Abs (_, _, t), tms) = collect_consts (t, tms)
  | collect_consts (tm as Const _, tms) = insert (op aconv) tm tms
  | collect_consts (_, tms) = tms


(* Complementing Type.varify_global... *)

fun unvarify_global t fmap =
  let
    val fmap' = map Library.swap fmap
    fun unthaw (f as (a, S)) =
      (case AList.lookup (op =) fmap' a of
        NONE => TVar f
      | SOME (b, _) => TFree (b, S))
  in map_types (map_type_tvar unthaw) t end


(* The syntactic meddling needed to setup add_specification for work *)

fun close_form t =
  fold_rev (fn (s, T) => fn t => HOLogic.mk_all (s, T, t))
    (map dest_Free (Misc_Legacy.term_frees t)) t

fun zip3 [] [] [] = []
  | zip3 (x::xs) (y::ys) (z::zs) = (x,y,z)::zip3 xs ys zs
  | zip3 _ _ _ = raise Fail "Choice_Specification.process_spec internal error"

fun myfoldr f [x] = x
  | myfoldr f (x::xs) = f (x,myfoldr f xs)
  | myfoldr f [] = raise Fail "Choice_Specification.process_spec internal error"

fun process_spec cos alt_props thy =
  let
    val ctxt = Proof_Context.init_global thy

    val rew_imps = alt_props |>
      map (Object_Logic.atomize ctxt o Thm.cterm_of ctxt o Syntax.read_prop_global thy o snd)
    val props' = rew_imps |>
      map (HOLogic.dest_Trueprop o Thm.term_of o snd o Thm.dest_equals o Thm.cprop_of)

    fun proc_single prop =
      let
        val frees = Misc_Legacy.term_frees prop
        val _ = forall (fn v => Sign.of_sort thy (type_of v, \<^sort>\<open>type\<close>)) frees
          orelse error "Specificaton: Only free variables of sort 'type' allowed"
        val prop_closed = close_form prop
      in (prop_closed, frees) end

    val props'' = map proc_single props'
    val frees = map snd props''
    val prop = myfoldr HOLogic.mk_conj (map fst props'')

    val (vmap, prop_thawed) = Type.varify_global TFrees.empty prop
    val thawed_prop_consts = collect_consts (prop_thawed, [])
    val (altcos, overloaded) = split_list cos
    val (names, sconsts) = split_list altcos
    val consts = map (Syntax.read_term_global thy) sconsts
    val _ = not (Library.exists (not o Term.is_Const) consts)
      orelse error "Specification: Non-constant found as parameter"

    fun proc_const c =
      let
        val (_, c') = Type.varify_global TFrees.empty c
        val (cname,ctyp) = dest_Const c'
      in
        (case filter (fn t =>
            let val (name, typ) = dest_Const t
            in name = cname andalso Sign.typ_equiv thy (typ, ctyp)
            end) thawed_prop_consts of
          [] =>
            error ("Specification: No suitable instances of constant \"" ^
              Syntax.string_of_term_global thy c ^ "\" found")
        | [cf] => unvarify_global cf vmap
        | _ => error ("Specification: Several variations of \"" ^
            Syntax.string_of_term_global thy c ^ "\" found (try applying explicit type constraints)"))
      end
    val proc_consts = map proc_const consts
    fun mk_exist c prop =
      let
        val T = type_of c
        val cname = Long_Name.base_name (fst (dest_Const c))
        val vname = if Symbol_Pos.is_identifier cname then cname else "x"
      in HOLogic.exists_const T $ Abs(vname,T,Term.abstract_over (c, prop)) end
    val ex_prop = fold_rev mk_exist proc_consts prop
    val cnames = map (fst o dest_Const) proc_consts
    fun post_process (arg as (thy,thm)) =
      let
        fun inst_all thy v thm =
          let
            val cv = Thm.global_cterm_of thy v
            val cT = Thm.ctyp_of_cterm cv
            val spec' = Thm.instantiate' [SOME cT] [NONE, SOME cv] spec
          in thm RS spec' end
        fun remove_alls frees (thm, thy) = (fold (inst_all thy) frees thm, thy)
        fun process_single ((name, atts), rew_imp, frees) args =
          let
            fun undo_imps thm = Thm.equal_elim (Thm.symmetric rew_imp) thm

            fun add_final (thm, thy) =
              if name = ""
              then (thm, thy)
              else (writeln ("  " ^ name ^ ": " ^ Thm.string_of_thm_global thy thm);
                Global_Theory.store_thm (Binding.name name, thm) thy)
          in
            swap args
            |> remove_alls frees
            |> apfst undo_imps
            |> apfst Drule.export_without_context
            |-> Thm.theory_attributes
              (map (Attrib.attribute_cmd_global thy)
                (@{attributes [nitpick_choice_spec]} @ atts))
            |> add_final
            |> swap
          end

        fun process_all [proc_arg] args =
            process_single proc_arg args
          | process_all (proc_arg::rest) (thy,thm) =
              let
                val single_th = thm RS conjunct1
                val rest_th = thm RS conjunct2
                val (thy', _) = process_single proc_arg (thy, single_th)
              in process_all rest (thy', rest_th) end
          | process_all [] _ = raise Fail "Choice_Specification.process_spec internal error"
        val alt_names = map fst alt_props
        val _ =
          if exists (fn (name, _) => name <> "") alt_names
          then writeln "specification"
          else ()
      in
        arg
        |> apsnd (Thm.unvarify_global thy)
        |> process_all (zip3 alt_names rew_imps frees)
      end

    fun after_qed [[thm]] = Proof_Context.background_theory (fn thy =>
      #1 (post_process (add_specification (zip3 names cnames overloaded) (thy, thm))));
  in
    thy
    |> Proof_Context.init_global
    |> Variable.declare_term ex_prop
    |> Proof.theorem NONE after_qed [[(HOLogic.mk_Trueprop ex_prop, [])]]
  end


(* outer syntax *)

val opt_name = Scan.optional (Parse.name --| \<^keyword>\<open>:\<close>) ""
val opt_overloaded = Parse.opt_keyword "overloaded"

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>specification\<close> "define constants by specification"
    (\<^keyword>\<open>(\<close> |-- Scan.repeat1 (opt_name -- Parse.term -- opt_overloaded) --| \<^keyword>\<open>)\<close> --
      Scan.repeat1 ((Parse_Spec.opt_thm_name ":" >> apfst Binding.name_of) -- Parse.prop)
      >> (fn (cos, alt_props) => Toplevel.theory_to_proof (process_spec cos alt_props)))

end
