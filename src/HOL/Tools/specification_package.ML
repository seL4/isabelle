(*  Title:      HOL/Tools/specification_package.ML
    ID:         $Id$
    Author:     Sebastian Skalberg, TU Muenchen

Package for defining constants by specification.
*)

signature SPECIFICATION_PACKAGE =
sig
  val quiet_mode: bool ref
  val add_specification: string option -> (bstring * xstring * bool) list ->
    theory * thm -> theory * thm
end

structure SpecificationPackage: SPECIFICATION_PACKAGE =
struct

(* messages *)

val quiet_mode = ref false
fun message s = if ! quiet_mode then () else writeln s


(* Actual code *)

local
    val exE_some = thm "exE_some";

    fun mk_definitional [] arg = arg
      | mk_definitional ((thname,cname,covld)::cos) (thy,thm) =
        case HOLogic.dest_Trueprop (concl_of thm) of
            Const("Ex",_) $ P =>
            let
                val ctype = domain_type (type_of P)
                val cname_full = Sign.intern_const (sign_of thy) cname
                val cdefname = if thname = ""
                               then Thm.def_name (Sign.base_name cname)
                               else thname
                val def_eq = Logic.mk_equals (Const(cname_full,ctype),
                                              HOLogic.choice_const ctype $  P)
                val (thms, thy') = PureThy.add_defs_i covld [((cdefname,def_eq),[])] thy
                val thm' = [thm,hd thms] MRS exE_some
            in
                mk_definitional cos (thy',thm')
            end
          | _ => raise THM ("Internal error: Bad specification theorem",0,[thm])

    fun mk_axiomatic axname cos arg =
        let
            fun process [] (thy,tm) =
                let
                    val (thms, thy') = PureThy.add_axioms_i [((axname,HOLogic.mk_Trueprop tm),[])] thy
                in
                    (thy',hd thms)
                end
              | process ((thname,cname,covld)::cos) (thy,tm) =
                case tm of
                    Const("Ex",_) $ P =>
                    let
                        val ctype = domain_type (type_of P)
                        val cname_full = Sign.intern_const (sign_of thy) cname
                        val cdefname = if thname = ""
                                       then Thm.def_name (Sign.base_name cname)
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

fun add_specification axiomatic cos arg =
    arg |> apsnd freezeT
        |> proc_exprop axiomatic cos
        |> apsnd standard

fun add_spec x y (context, thm) =
  (Context.the_theory context, thm) |> add_specification x y |>> Context.Theory;


(* Collect all intances of constants in term *)

fun collect_consts (        t $ u,tms) = collect_consts (u,collect_consts (t,tms))
  | collect_consts (   Abs(_,_,t),tms) = collect_consts (t,tms)
  | collect_consts (tm as Const _,tms) = insert (op aconv) tm tms
  | collect_consts (            _,tms) = tms

(* Complementing Type.varify... *)

fun unvarify t fmap =
    let
        val fmap' = map Library.swap fmap
        fun unthaw (f as (a, S)) =
            (case AList.lookup (op =) fmap' a of
                 NONE => TVar f
               | SOME (b, _) => TFree (b, S))
    in
        map_term_types (map_type_tvar unthaw) t
    end

(* The syntactic meddling needed to setup add_specification for work *)

fun process_spec axiomatic cos alt_props thy =
    let
        fun zip3 [] [] [] = []
          | zip3 (x::xs) (y::ys) (z::zs) = (x,y,z)::zip3 xs ys zs
          | zip3 _ _ _ = error "SpecificationPackage.process_spec internal error"

        fun myfoldr f [x] = x
          | myfoldr f (x::xs) = f (x,myfoldr f xs)
          | myfoldr f [] = error "SpecificationPackage.process_spec internal error"

        val rew_imps = alt_props |>
          map (ObjectLogic.atomize_cterm o Thm.read_cterm thy o rpair Term.propT o snd)
        val props' = rew_imps |>
          map (HOLogic.dest_Trueprop o term_of o snd o dest_equals o cprop_of)

        fun proc_single prop =
            let
                val frees = Term.term_frees prop
                val tsig = Sign.tsig_of (sign_of thy)
                val _ = assert (forall (fn v => Type.of_sort tsig (type_of v,HOLogic.typeS)) frees)
                               "Specificaton: Only free variables of sort 'type' allowed"
                val prop_closed = foldr (fn ((vname,T),prop) => HOLogic.mk_all (vname,T,prop)) prop (map dest_Free frees)
            in
                (prop_closed,frees)
            end

        val props'' = map proc_single props'
        val frees = map snd props''
        val prop  = myfoldr HOLogic.mk_conj (map fst props'')
        val cprop = cterm_of thy (HOLogic.mk_Trueprop prop)

        val (prop_thawed,vmap) = Type.varify (prop,[])
        val thawed_prop_consts = collect_consts (prop_thawed,[])
        val (altcos,overloaded) = Library.split_list cos
        val (names,sconsts) = Library.split_list altcos
        val consts = map (term_of o Thm.read_cterm thy o rpair TypeInfer.logicT) sconsts
        val _ = assert (not (Library.exists (not o Term.is_Const) consts))
                       "Specification: Non-constant found as parameter"

        fun proc_const c =
            let
                val c' = fst (Type.varify (c,[]))
                val (cname,ctyp) = dest_Const c'
            in
                case List.filter (fn t => let val (name,typ) = dest_Const t
                                     in name = cname andalso Sign.typ_equiv thy (typ, ctyp)
                                     end) thawed_prop_consts of
                    [] => error ("Specification: No suitable instances of constant \"" ^ (Sign.string_of_term thy c) ^ "\" found")
                  | [cf] => unvarify cf vmap
                  | _ => error ("Specification: Several variations of \"" ^ (Sign.string_of_term thy c) ^ "\" found (try applying explicit type constraints)")
            end
        val proc_consts = map proc_const consts
        fun mk_exist (c,prop) =
            let
                val T = type_of c
                val cname = Sign.base_name (fst (dest_Const c))
                val vname = if Syntax.is_identifier cname
                            then cname
                            else "x"
            in
                HOLogic.exists_const T $ Abs(vname,T,Term.abstract_over (c,prop))
            end
        val ex_prop = foldr mk_exist prop proc_consts
        val cnames = map (fst o dest_Const) proc_consts
        fun post_process (arg as (thy,thm)) =
            let
                fun inst_all thy (thm,v) =
                    let
                        val cv = cterm_of thy v
                        val cT = ctyp_of_term cv
                        val spec' = instantiate' [SOME cT] [NONE,SOME cv] spec
                    in
                        thm RS spec'
                    end
                fun remove_alls frees thm = Library.foldl (inst_all (sign_of_thm thm)) (thm,frees)
                fun process_single ((name,atts),rew_imp,frees) args =
                    let
                        fun undo_imps thm =
                            equal_elim (symmetric rew_imp) thm

                        fun add_final (arg as (thy, thm)) =
                            if name = ""
                            then arg |> Library.swap
                            else (writeln ("  " ^ name ^ ": " ^ (string_of_thm thm));
                                  PureThy.store_thm ((name, thm), []) thy)
                    in
                        args |> apsnd (remove_alls frees)
                             |> apsnd undo_imps
                             |> apsnd standard
                             |> Thm.theory_attributes (map (Attrib.attribute thy) atts)
                             |> add_final
                             |> Library.swap
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
                  | process_all [] _ = error "SpecificationPackage.process_spec internal error"
                val alt_names = map fst alt_props
                val _ = if exists (fn(name,_) => not (name = "")) alt_names
                        then writeln "specification"
                        else ()
            in
                arg |> apsnd freezeT
                    |> process_all (zip3 alt_names rew_imps frees)
            end
            fun post_proc (context, th) =
                post_process (Context.theory_of context, th) |>> Context.Theory;
    in
      IsarThy.theorem_i PureThy.internalK
        ("", [add_spec axiomatic (zip3 names cnames overloaded), post_proc])
        (HOLogic.mk_Trueprop ex_prop, ([], [])) thy
    end


(* outer syntax *)

local structure P = OuterParse and K = OuterKeyword in

val opt_name = Scan.optional (P.name --| P.$$$ ":") ""
val opt_overloaded = P.opt_keyword "overloaded";

val specification_decl =
  P.$$$ "(" |-- Scan.repeat1 (opt_name -- P.term -- opt_overloaded) --| P.$$$ ")" --
          Scan.repeat1 (P.opt_thm_name ":" -- P.prop)

val specificationP =
  OuterSyntax.command "specification" "define constants by specification" K.thy_goal
    (specification_decl >> (fn (cos,alt_props) =>
                               Toplevel.print o (Toplevel.theory_to_proof
                                                     (process_spec NONE cos alt_props))))

val ax_specification_decl =
    P.name --
    (P.$$$ "(" |-- Scan.repeat1 (opt_name -- P.term -- opt_overloaded) --| P.$$$ ")" --
           Scan.repeat1 (P.opt_thm_name ":" -- P.prop))

val ax_specificationP =
  OuterSyntax.command "ax_specification" "define constants by specification" K.thy_goal
    (ax_specification_decl >> (fn (axname,(cos,alt_props)) =>
                               Toplevel.print o (Toplevel.theory_to_proof
                                                     (process_spec (SOME axname) cos alt_props))))

val _ = OuterSyntax.add_parsers [specificationP,ax_specificationP]

end


end
