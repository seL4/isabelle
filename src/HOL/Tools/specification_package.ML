(*  Title:      HOL/Tools/specification_package.ML
    ID:         $Id$
    Author:     Sebastian Skalberg, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Package for defining constants by specification.
*)

signature SPECIFICATION_PACKAGE =
sig
    val quiet_mode: bool ref
    val add_specification_i: (bstring * xstring * bool) list
			     -> theory * thm -> theory * thm
end

structure SpecificationPackage : SPECIFICATION_PACKAGE =
struct

(* messages *)

val quiet_mode = ref false
fun message s = if ! quiet_mode then () else writeln s

local
    val _ = Goal "[| Ex P ; c == Eps P |] ==> P c"
    val _ = by (Asm_simp_tac 1)
    val _ = by (rtac (thm "someI_ex") 1)
    val _ = ba 1
in
val helper = Goals.result()
end

(* Akin to HOLogic.exists_const *)
fun choice_const T = Const("Hilbert_Choice.Eps",(T-->HOLogic.boolT)-->T)

(* Actual code *)

fun proc_exprop [] arg = arg
  | proc_exprop ((thname,cname,covld)::cos) (thy,thm) =
    case concl_of thm of
	Const("Trueprop",_) $ (Const("Ex",_) $ P) =>
	let
	    val ctype = domain_type (type_of P)
	    val cname_full = Sign.intern_const (sign_of thy) cname
	    val cdefname = if thname = ""
			   then Thm.def_name (Sign.base_name cname)
			   else thname
	    val def_eq = Logic.mk_equals (Const(cname_full,ctype),choice_const ctype $  P)
	    val (thy',thms) = PureThy.add_defs_i covld [((cdefname,def_eq),[])] thy
	    val thm' = [thm,hd thms] MRS helper
	in
	    proc_exprop cos (thy',thm')
	end
      | _ => raise THM ("Internal error: Bad specification theorem",0,[thm])

fun add_specification_i cos arg =
    arg |> apsnd freezeT
	|> proc_exprop cos
	|> apsnd standard

(* Collect all intances of constants in term *)

fun collect_consts (        t $ u,tms) = collect_consts (u,collect_consts (t,tms))
  | collect_consts (   Abs(_,_,t),tms) = collect_consts (t,tms)
  | collect_consts (tm as Const _,tms) = gen_ins (op aconv) (tm,tms)
  | collect_consts (            _,tms) = tms

(* Complementing Type.varify... *)

fun unvarify t fmap =
    let
	val fmap' = map Library.swap fmap
	fun unthaw (f as (a,S)) =
	    (case assoc (fmap',a) of
		 None => TVar f
	       | Some b => TFree (b,S))
    in
	map_term_types (map_type_tvar unthaw) t
    end

(* The syntactic meddling needed to setup add_specification for work *)

fun process_spec cos alt_props int thy =
    let
	fun myfoldr f [] = error "SpecificationPackage.process_spec internal error"
	  | myfoldr f [x] = x
	  | myfoldr f (x::xs) = f (x,myfoldr f xs)

	val sg = sign_of thy
	fun typ_equiv t u =
	    let
		val tsig = Sign.tsig_of sg
	    in
		Type.typ_instance(tsig,t,u) andalso
		Type.typ_instance(tsig,u,t)
	    end

	val cprops = map (Thm.read_cterm sg o rpair Term.propT o snd) alt_props
	val ss = empty_ss setmksimps single addsimps [thm "HOL.atomize_imp",thm "HOL.atomize_all"]
	val rew_imps = map (Simplifier.full_rewrite ss) cprops
	val props' = map (HOLogic.dest_Trueprop o term_of o snd o dest_equals o cprop_of) rew_imps
	val prop  = myfoldr HOLogic.mk_conj props'
	val cprop = cterm_of sg (HOLogic.mk_Trueprop prop)

	val (prop_thawed,vmap) = Type.varify (prop,[])
	val thawed_prop_consts = collect_consts (prop_thawed,[])
	val (altcos,overloaded) = Library.split_list cos
	val (names,sconsts) = Library.split_list altcos
	val consts = map (term_of o Thm.read_cterm sg o rpair TypeInfer.logicT) sconsts
	val _ = assert (not (Library.exists (not o Term.is_Const) consts))
		       "Non-constant found as parameter"
	fun proc_const c =
	    let
		val c' = fst (Type.varify (c,[]))
		val (cname,ctyp) = dest_Const c'
	    in
		case filter (fn t => let val (name,typ) = dest_Const t
				     in name = cname andalso typ_equiv typ ctyp
				     end) thawed_prop_consts of
		    [] => error ("Constant \"" ^ (Sign.string_of_term sg c) ^ "\" not found in specification")
		  | [cf] => unvarify cf vmap
		  | _ => error ("Several variations of \"" ^ (Sign.string_of_term sg c) ^ "\" found in specification")
	    end
	val frees = Term.term_frees prop
	val tsig = Sign.tsig_of (sign_of thy)
	val _ = assert (forall (fn v => Type.of_sort tsig (type_of v,HOLogic.typeS)) frees)
		"Only free variables of sort 'type' allowed in specifications"
	val prop_closed = foldr (fn ((vname,T),prop) => HOLogic.mk_all (vname,T,prop)) (map dest_Free frees,prop)
	val proc_consts = map proc_const consts
	fun mk_exist (c,prop) =
	    let
		val T = type_of c
	    in
		HOLogic.exists_const T $ Abs("x",T,Term.abstract_over (c,prop))
	    end
	val ex_prop = foldr mk_exist (proc_consts,prop_closed)
	val cnames = map (fst o dest_Const) proc_consts
	fun zip3 [] [] [] = []
	  | zip3 (x::xs) (y::ys) (z::zs) = (x,y,z)::zip3 xs ys zs
	  | zip3 _ _ _ = error "Internal error: Bad specification syntax"
	fun post_process (arg as (thy,thm)) =
	    let
		fun inst_all sg (thm,v) =
		    let
			val cv = cterm_of sg v
			val cT = ctyp_of_term cv
			val spec' = instantiate' [Some cT] [None,Some cv] spec
		    in
			thm RS spec'
		    end
		fun remove_alls frees thm = foldl (inst_all (sign_of_thm thm)) (thm,frees)
		fun process_single (name,atts) rew_imp args =
		    let
			fun undo_imps thm =
			    equal_elim (symmetric rew_imp) thm

			fun apply_atts arg = Thm.apply_attributes (arg,map (Attrib.global_attribute thy) atts)
			fun add_final (arg as (thy,thm)) =
			    if name = ""
			    then arg
			    else (writeln ("  " ^ name ^ ": " ^ (string_of_thm thm));
				  PureThy.store_thm((name,thm),[]) thy)
		    in
			args |> apsnd (undo_imps)
			     |> apsnd standard
			     |> apply_atts
			     |> add_final
		    end

		fun process_all [alt_name] [rew_imp] args =
		    process_single alt_name rew_imp args
		  | process_all (alt_name::rest_alt) (rew_imp::rest_imp) (thy,thm) = 
		    let
			val single_th = thm RS conjunct1
			val rest_th   = thm RS conjunct2
			val (thy',_)  = process_single alt_name rew_imp (thy,single_th)
		    in
			process_all rest_alt rest_imp (thy',rest_th)
		    end
		  | process_all _ _ _ = error "SpecificationPackage.process_spec internal error"
		val alt_names = map fst alt_props
		val _ = if exists (fn(name,_) => not (name = "")) alt_names
			then writeln "specification"
			else ()
	    in
		arg |> apsnd freezeT
		    |> apsnd (remove_alls frees)
		    |> process_all alt_names rew_imps
	    end
    in
	IsarThy.theorem_i Drule.internalK
	    (("",[add_specification_i (zip3 (names:string list) (cnames:string list) (overloaded:bool list)),post_process]),
	     (HOLogic.mk_Trueprop ex_prop,([],[]))) int thy
    end

(* outer syntax *)

local structure P = OuterParse and K = OuterSyntax.Keyword in

(* taken from ~~/Pure/Isar/isar_syn.ML *)
val opt_overloaded =
  Scan.optional (P.$$$ "(" |-- P.!!! ((P.$$$ "overloaded" >> K true) --| P.$$$ ")")) false

val opt_name = Scan.optional (P.name --| P.$$$ ":") ""

val specification_decl =
    P.$$$ "(" |-- Scan.repeat1 (opt_name -- P.term -- opt_overloaded) --| P.$$$ ")" --
	  Scan.repeat1 (P.opt_thm_name ":" -- P.prop)

val specificationP =
  OuterSyntax.command "specification" "define constants by specification" K.thy_goal
    (specification_decl >> (fn (cos,alt_props) =>
			       Toplevel.print o (Toplevel.theory_to_proof (process_spec cos alt_props))))

val _ = OuterSyntax.add_parsers [specificationP]

end


end
