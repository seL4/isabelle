(*  Title:      HOL/Tools/choice_specification.ML
    Author:     Sebastian Skalberg, TU Muenchen

Package for defining constants by specification.
*)

signature CHOICE_SPECIFICATION =
sig
  val close_form : term -> term
  val add_specification: string option -> (bstring * xstring * bool) list ->
    theory * thm -> theory * thm
end

structure Choice_Specification: CHOICE_SPECIFICATION =
struct

(* actual code *)

fun close_form t =
    fold_rev (fn (s, T) => fn t => HOLogic.mk_all (s, T, t))
             (map dest_Free (Misc_Legacy.term_frees t)) t

local
    fun mk_definitional [] arg = arg
      | mk_definitional ((thname,cname,covld)::cos) (thy,thm) =
        case HOLogic.dest_Trueprop (concl_of thm) of
            Const(@{const_name Ex},_) $ P =>
            let
                val ctype = domain_type (type_of P)
                val cname_full = Sign.intern_const thy cname
                val cdefname = if thname = ""
                               then Thm.def_name (Long_Name.base_name cname)
                               else thname
                val def_eq = Logic.mk_equals (Const(cname_full,ctype),
                                              HOLogic.choice_const ctype $  P)
                val (thms, thy') = Global_Theory.add_defs covld [((Binding.name cdefname, def_eq),[])] thy
                val thm' = [thm,hd thms] MRS @{thm exE_some}
            in
                mk_definitional cos (thy',thm')
            end
          | _ => raise THM ("Internal error: Bad specification theorem",0,[thm])

    fun mk_axiomatic axname cos arg =
        let
            fun process [] (thy,tm) =
                let
                    val (thm, thy') =
                      Specification.axiom ((Binding.name axname, []), HOLogic.mk_Trueprop tm) thy
                in
                    (thy', Drule.export_without_context thm)
                end
              | process ((thname,cname,covld)::cos) (thy,tm) =
                case tm of
                    Const(@{const_name Ex},_) $ P =>
                    let
                        val ctype = domain_type (type_of P)
                        val cname_full = Sign.intern_const thy cname
                        val cdefname = if thname = ""
                                       then Thm.def_name (Long_Name.base_name cname)
                                       else thname
                        val co = Const(cname_full,ctype)
                        val thy' = Theory.add_finals_i covld [co] thy
                        val tm' = case P of
                                      Abs(_, _, bodt) => subst_bound (co, bodt)
                                    | _ => P $ co
                    in
                        process cos (thy',tm')
                    end
                  | _ => raise TERM ("Internal error: Bad specification theorem",[tm])
        in
            process cos arg
        end

in
fun proc_exprop axiomatic cos arg =
    case axiomatic of
        SOME axname => mk_axiomatic axname cos (apsnd (HOLogic.dest_Trueprop o concl_of) arg)
      | NONE => mk_definitional cos arg
end

fun add_specification axiomatic cos =
    proc_exprop axiomatic cos
    #> apsnd Drule.export_without_context


(* Collect all intances of constants in term *)

fun collect_consts (        t $ u,tms) = collect_consts (u,collect_consts (t,tms))
  | collect_consts (   Abs(_,_,t),tms) = collect_consts (t,tms)
  | collect_consts (tm as Const _,tms) = insert (op aconv) tm tms
  | collect_consts (            _,tms) = tms

(* Complementing Type.varify_global... *)

fun unvarify_global t fmap =
    let
        val fmap' = map Library.swap fmap
        fun unthaw (f as (a, S)) =
            (case AList.lookup (op =) fmap' a of
                 NONE => TVar f
               | SOME (b, _) => TFree (b, S))
    in
        map_types (map_type_tvar unthaw) t
    end

(* The syntactic meddling needed to setup add_specification for work *)

fun process_spec axiomatic cos alt_props thy =
    let
        fun zip3 [] [] [] = []
          | zip3 (x::xs) (y::ys) (z::zs) = (x,y,z)::zip3 xs ys zs
          | zip3 _ _ _ = error "Choice_Specification.process_spec internal error"

        fun myfoldr f [x] = x
          | myfoldr f (x::xs) = f (x,myfoldr f xs)
          | myfoldr f [] = error "Choice_Specification.process_spec internal error"

        val rew_imps = alt_props |>
          map (Object_Logic.atomize o Thm.cterm_of thy o Syntax.read_prop_global thy o snd)
        val props' = rew_imps |>
          map (HOLogic.dest_Trueprop o term_of o snd o Thm.dest_equals o cprop_of)

        fun proc_single prop =
            let
                val frees = Misc_Legacy.term_frees prop
                val _ = forall (fn v => Sign.of_sort thy (type_of v,HOLogic.typeS)) frees
                  orelse error "Specificaton: Only free variables of sort 'type' allowed"
                val prop_closed = close_form prop
            in
                (prop_closed,frees)
            end

        val props'' = map proc_single props'
        val frees = map snd props''
        val prop  = myfoldr HOLogic.mk_conj (map fst props'')
        val cprop = cterm_of thy (HOLogic.mk_Trueprop prop)

        val (vmap, prop_thawed) = Type.varify_global [] prop
        val thawed_prop_consts = collect_consts (prop_thawed,[])
        val (altcos,overloaded) = Library.split_list cos
        val (names,sconsts) = Library.split_list altcos
        val consts = map (Syntax.read_term_global thy) sconsts
        val _ = not (Library.exists (not o Term.is_Const) consts)
          orelse error "Specification: Non-constant found as parameter"

        fun proc_const c =
            let
                val (_, c') = Type.varify_global [] c
                val (cname,ctyp) = dest_Const c'
            in
                case filter (fn t => let val (name,typ) = dest_Const t
                                     in name = cname andalso Sign.typ_equiv thy (typ, ctyp)
                                     end) thawed_prop_consts of
                    [] => error ("Specification: No suitable instances of constant \"" ^ Syntax.string_of_term_global thy c ^ "\" found")
                  | [cf] => unvarify_global cf vmap
                  | _ => error ("Specification: Several variations of \"" ^ Syntax.string_of_term_global thy c ^ "\" found (try applying explicit type constraints)")
            end
        val proc_consts = map proc_const consts
        fun mk_exist c prop =
            let
                val T = type_of c
                val cname = Long_Name.base_name (fst (dest_Const c))
                val vname = if Lexicon.is_identifier cname
                            then cname
                            else "x"
            in
                HOLogic.exists_const T $ Abs(vname,T,Term.abstract_over (c,prop))
            end
        val ex_prop = fold_rev mk_exist proc_consts prop
        val cnames = map (fst o dest_Const) proc_consts
        fun post_process (arg as (thy,thm)) =
            let
                fun inst_all thy v thm =
                    let
                        val cv = cterm_of thy v
                        val cT = ctyp_of_term cv
                        val spec' = instantiate' [SOME cT] [NONE,SOME cv] spec
                    in
                        thm RS spec'
                    end
                fun remove_alls frees thm =
                    fold (inst_all (Thm.theory_of_thm thm)) frees thm
                fun process_single ((name,atts),rew_imp,frees) args =
                    let
                        fun undo_imps thm =
                            Thm.equal_elim (Thm.symmetric rew_imp) thm

                        fun add_final (thm, thy) =
                            if name = ""
                            then (thm, thy)
                            else (writeln ("  " ^ name ^ ": " ^ Display.string_of_thm_global thy thm);
                                  Global_Theory.store_thm (Binding.name name, thm) thy)
                    in
                        swap args
                             |> apfst (remove_alls frees)
                             |> apfst undo_imps
                             |> apfst Drule.export_without_context
                             |-> Thm.theory_attributes
                                (map (Attrib.attribute thy)
                                  (@{attributes [nitpick_choice_spec]} @ atts))
                             |> add_final
                             |> swap
                    end

                fun process_all [proc_arg] args =
                    process_single proc_arg args
                  | process_all (proc_arg::rest) (thy,thm) =
                    let
                        val single_th = thm RS conjunct1
                        val rest_th   = thm RS conjunct2
                        val (thy',_)  = process_single proc_arg (thy,single_th)
                    in
                        process_all rest (thy',rest_th)
                    end
                  | process_all [] _ = error "Choice_Specification.process_spec internal error"
                val alt_names = map fst alt_props
                val _ = if exists (fn(name,_) => not (name = "")) alt_names
                        then writeln "specification"
                        else ()
            in
                arg |> apsnd Thm.unvarify_global
                    |> process_all (zip3 alt_names rew_imps frees)
            end

      fun after_qed [[thm]] = Proof_Context.background_theory (fn thy =>
        #1 (post_process (add_specification axiomatic (zip3 names cnames overloaded) (thy, thm))));
    in
      thy
      |> Proof_Context.init_global
      |> Variable.declare_term ex_prop
      |> Proof.theorem NONE after_qed [[(HOLogic.mk_Trueprop ex_prop, [])]]
    end;


(* outer syntax *)

val opt_name = Scan.optional (Parse.name --| @{keyword ":"}) ""
val opt_overloaded = Parse.opt_keyword "overloaded"

val _ =
  Outer_Syntax.command @{command_spec "specification"} "define constants by specification"
    (@{keyword "("} |-- Scan.repeat1 (opt_name -- Parse.term -- opt_overloaded) --| @{keyword ")"} --
      Scan.repeat1 ((Parse_Spec.opt_thm_name ":" >> apfst Binding.name_of) -- Parse.prop)
      >> (fn (cos, alt_props) => Toplevel.print o
          (Toplevel.theory_to_proof (process_spec NONE cos alt_props))))

val _ =
  Outer_Syntax.command @{command_spec "ax_specification"} "define constants by specification"
    (Parse.name --
      (@{keyword "("} |-- Scan.repeat1 (opt_name -- Parse.term -- opt_overloaded) --| @{keyword ")"} --
        Scan.repeat1 ((Parse_Spec.opt_thm_name ":" >> apfst Binding.name_of) -- Parse.prop))
      >> (fn (axname, (cos, alt_props)) =>
           Toplevel.print o (Toplevel.theory_to_proof (process_spec (SOME axname) cos alt_props))))

end
