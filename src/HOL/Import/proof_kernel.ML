(*  Title:      HOL/Import/proof_kernel.ML
    ID:         $Id$
    Author:     Sebastian Skalberg (TU Muenchen)
*)

signature ProofKernel =
sig
    type hol_type
    type tag
    type term
    type thm
    type ('a,'b) subst
	 
    type proof_info
    datatype proof = Proof of proof_info * proof_content
	 and proof_content
	   = PRefl of term
	   | PInstT of proof * (hol_type,hol_type) subst
	   | PSubst of proof list * term * proof
	   | PAbs of proof * term
	   | PDisch of proof * term
	   | PMp of proof * proof
	   | PHyp of term
	   | PAxm of string * term
	   | PDef of string * string * term
	   | PTmSpec of string * string list * proof
	   | PTyDef of string * string * proof
	   | PTyIntro of string * string * string * string * term * term * proof
	   | POracle of tag * term list * term
	   | PDisk
	   | PSpec of proof * term
	   | PInst of proof * (term,term) subst
	   | PGen of proof * term
	   | PGenAbs of proof * term option * term list
	   | PImpAS of proof * proof
	   | PSym of proof
	   | PTrans of proof * proof
	   | PComb of proof * proof
	   | PEqMp of proof * proof
	   | PEqImp of proof
	   | PExists of proof * term * term
	   | PChoose of term * proof * proof
	   | PConj of proof * proof
	   | PConjunct1 of proof
	   | PConjunct2 of proof
	   | PDisj1 of proof * term
	   | PDisj2 of proof * term
	   | PDisjCases of proof * proof * proof
	   | PNotI of proof
	   | PNotE of proof
	   | PContr of proof * term

    exception PK of string * string

    val get_proof_dir: string -> theory -> string option
    val debug : bool ref
    val disk_info_of : proof -> (string * string) option
    val set_disk_info_of : proof -> string -> string -> unit
    val mk_proof : proof_content -> proof
    val content_of : proof -> proof_content
    val import_proof : string -> string -> theory -> (theory -> term) option * (theory -> proof)

    val rewrite_hol4_term: Term.term -> theory -> Thm.thm

    val type_of : term -> hol_type

    val get_thm  : string -> string         -> theory -> (theory * thm option)
    val get_def  : string -> string -> term -> theory -> (theory * thm option)
    val get_axiom: string -> string         -> theory -> (theory * thm option)

    val store_thm : string -> string -> thm -> theory -> theory * thm

    val to_isa_thm : thm -> (term * term) list * Thm.thm
    val to_isa_term: term -> Term.term

    val REFL : term -> theory -> theory * thm
    val ASSUME : term -> theory -> theory * thm
    val INST_TYPE : (hol_type,hol_type) subst -> thm -> theory -> theory * thm
    val INST : (term,term)subst -> thm -> theory -> theory * thm
    val EQ_MP : thm -> thm -> theory -> theory * thm
    val EQ_IMP_RULE : thm -> theory -> theory * thm
    val SUBST : thm list -> term -> thm -> theory -> theory * thm
    val DISJ_CASES : thm -> thm -> thm -> theory -> theory * thm
    val DISJ1: thm -> term -> theory -> theory * thm
    val DISJ2: term -> thm -> theory -> theory * thm
    val IMP_ANTISYM: thm -> thm -> theory -> theory * thm
    val SYM : thm -> theory -> theory * thm
    val MP : thm -> thm -> theory -> theory * thm
    val GEN : term -> thm -> theory -> theory * thm
    val CHOOSE : term -> thm -> thm -> theory -> theory * thm
    val EXISTS : term -> term -> thm -> theory -> theory * thm
    val ABS : term -> thm -> theory -> theory * thm
    val GEN_ABS : term option -> term list -> thm -> theory -> theory * thm
    val TRANS : thm -> thm -> theory -> theory * thm
    val CCONTR : term -> thm -> theory -> theory * thm
    val CONJ : thm -> thm -> theory -> theory * thm
    val CONJUNCT1: thm -> theory -> theory * thm
    val CONJUNCT2: thm -> theory -> theory * thm
    val NOT_INTRO: thm -> theory -> theory * thm
    val NOT_ELIM : thm -> theory -> theory * thm
    val SPEC : term -> thm -> theory -> theory * thm
    val COMB : thm -> thm -> theory -> theory * thm
    val DISCH: term -> thm -> theory -> theory * thm

    val type_introduction: string -> string -> string -> string -> string -> term * term -> thm -> theory -> theory * thm

    val new_definition : string -> string -> term -> theory -> theory * thm
    val new_specification : string -> string -> string list -> thm -> theory -> theory * thm
    val new_type_definition : string -> string -> string -> thm -> theory -> theory * thm
    val new_axiom : string -> term -> theory -> theory * thm

end

structure ProofKernel :> ProofKernel =
struct
type hol_type = Term.typ
type term = Term.term
datatype tag = Tag of string list
type ('a,'b) subst = ('a * 'b) list
datatype thm = HOLThm of (Term.term * Term.term) list * Thm.thm

datatype proof_info
  = Info of {disk_info: (string * string) option ref}
	    
datatype proof = Proof of proof_info * proof_content
     and proof_content
       = PRefl of term
       | PInstT of proof * (hol_type,hol_type) subst
       | PSubst of proof list * term * proof
       | PAbs of proof * term
       | PDisch of proof * term
       | PMp of proof * proof
       | PHyp of term
       | PAxm of string * term
       | PDef of string * string * term
       | PTmSpec of string * string list * proof
       | PTyDef of string * string * proof
       | PTyIntro of string * string * string * string * term * term * proof
       | POracle of tag * term list * term
       | PDisk
       | PSpec of proof * term
       | PInst of proof * (term,term) subst
       | PGen of proof * term
       | PGenAbs of proof * term option * term list
       | PImpAS of proof * proof
       | PSym of proof
       | PTrans of proof * proof
       | PComb of proof * proof
       | PEqMp of proof * proof
       | PEqImp of proof
       | PExists of proof * term * term
       | PChoose of term * proof * proof
       | PConj of proof * proof
       | PConjunct1 of proof
       | PConjunct2 of proof
       | PDisj1 of proof * term
       | PDisj2 of proof * term
       | PDisjCases of proof * proof * proof
       | PNotI of proof
       | PNotE of proof
       | PContr of proof * term

exception PK of string * string
fun ERR f mesg = PK (f,mesg)

fun print_exn e = 
    case e of
	PK (m,s) => (writeln ("PK (" ^ m ^ "): " ^ s); raise e)
      | _ => Goals.print_exn e

(* Compatibility. *)

fun mk_syn c = if Symbol.is_identifier c then NoSyn else Syntax.literal c

val keywords = ["open"]
fun quotename c = if Symbol.is_identifier c andalso not (c mem keywords) then c else quote c

fun smart_string_of_cterm ct =
    let
	val {sign,t,T,...} = rep_cterm ct
        (* Hack to avoid parse errors with Trueprop *)
	val ct  = (cterm_of sign (HOLogic.dest_Trueprop t)
		   handle TERM _ => ct)
	fun match cu = t aconv (term_of cu)
	fun G 0 = I
	  | G 1 = Library.setmp show_types true
	  | G 2 = Library.setmp show_all_types true
	  | G _ = error ("ProofKernel.smart_string_of_cterm internal error: " ^ (G 2 string_of_cterm ct))
	fun F sh_br n =
	    let
		val str = Library.setmp show_brackets sh_br (G n string_of_cterm) ct
		val cu  = transform_error (read_cterm sign) (str,T)
	    in
		if match cu
		then quote str
		else F false (n+1)
	    end
	    handle ERROR_MESSAGE mesg =>
		   if String.isPrefix "Ambiguous" mesg andalso
		      not sh_br
		   then F true n
		   else F false (n+1)
    in
	transform_error (Library.setmp Syntax.ambiguity_is_error true (F false)) 0
    end
    handle ERROR_MESSAGE mesg =>
	   (writeln "Exception in smart_string_of_cterm!";
	    writeln mesg;
	    quote (string_of_cterm ct))

val smart_string_of_thm = smart_string_of_cterm o cprop_of

fun prth th = writeln ((Library.setmp print_mode [] string_of_thm) th)
fun prc ct = writeln ((Library.setmp print_mode [] string_of_cterm) ct)
val prin = Library.setmp print_mode [] prin
fun pth (HOLThm(ren,thm)) =
    let
	val _ = writeln "Renaming:"
	val _ = app (fn(v,w) => (prin v; writeln " -->"; prin w)) ren
	val _ = prth thm
    in
	()
    end

fun disk_info_of (Proof(Info{disk_info,...},_)) = !disk_info
fun mk_proof p = Proof(Info{disk_info = ref None},p)
fun content_of (Proof(_,p)) = p

fun set_disk_info_of (Proof(Info{disk_info,...},_)) thyname thmname =
    disk_info := Some(thyname,thmname)

structure Lib =
struct
fun wrap b e s = String.concat[b,s,e]

fun assoc x =
    let
	fun F [] = raise PK("Lib.assoc","Not found")
	  | F ((x',y)::rest) = if x = x'
			       then y
			       else F rest
    in
	F
    end
fun i mem L = 
    let fun itr [] = false 
	  | itr (a::rst) = i=a orelse itr rst 
    in itr L end;
    
fun insert i L = if i mem L then L else i::L
					
fun mk_set [] = []
  | mk_set (a::rst) = insert a (mk_set rst)
		      
fun [] union S = S
  | S union [] = S
  | (a::rst) union S2 = rst union (insert a S2)
			
fun implode_subst [] = []
  | implode_subst (x::r::rest) = ((x,r)::(implode_subst rest))
  | implode_subst _ = raise ERR "implode_subst" "malformed substitution list"

fun apboth f (x,y) = (f x,f y)
end
open Lib

structure Tag =
struct
val empty_tag = Tag []
fun read name = Tag [name]
fun merge (Tag tag1) (Tag tag2) = Tag (Lib.union(tag1,tag2))
end

(* Acutal code. *)

fun get_segment thyname l = (Lib.assoc "s" l
			     handle PK _ => thyname)
val get_name : (string * string) list -> string = Lib.assoc "n"

local
    open LazyScan
    infix 7 |-- --|
    infix 5 :-- -- ^^
    infix 3 >>
    infix 0 ||
in
exception XML of string

datatype xml = Elem of string * (string * string) list * xml list
datatype XMLtype = XMLty of xml | FullType of hol_type
datatype XMLterm = XMLtm of xml | FullTerm of term

fun pair x y = (x,y)

fun scan_id toks =
    let
        val (x,toks2) = one Char.isAlpha toks
        val (xs,toks3) = any Char.isAlphaNum toks2
    in
        (String.implode (x::xs),toks3)
    end

fun scan_string str c =
    let
	fun F [] toks = (c,toks)
	  | F (c::cs) toks =
	    case LazySeq.getItem toks of
		Some(c',toks') =>
		if c = c'
		then F cs toks'
		else raise SyntaxError
	      | None => raise SyntaxError
    in
	F (String.explode str)
    end

local
    val scan_entity =
	(scan_string "amp;" #"&")
	    || scan_string "quot;" #"\""
	    || scan_string "gt;" #">"
	    || scan_string "lt;" #"<"
            || scan_string "apos;" #"'"
in
fun scan_nonquote toks =
    case LazySeq.getItem toks of
	Some (c,toks') =>
	(case c of
	     #"\"" => raise SyntaxError
	   | #"&" => scan_entity toks'
	   | c => (c,toks'))
      | None => raise SyntaxError
end

val scan_string = $$ #"\"" |-- repeat scan_nonquote --| $$ #"\"" >>
		     String.implode

val scan_attribute = scan_id -- $$ #"=" |-- scan_string

val scan_start_of_tag = $$ #"<" |-- scan_id --
			   repeat ($$ #" " |-- scan_attribute)

(* The evaluation delay introduced through the 'toks' argument is needed
for the sake of the SML/NJ (110.9.1) compiler.  Either that or an explicit
type :-( *)
fun scan_end_of_tag toks = ($$ #"/" |-- $$ #">" |-- succeed []) toks

val scan_end_tag = $$ #"<" |-- $$ #"/" |-- scan_id --| $$ #">"

fun scan_children id = $$ #">" |-- repeat scan_tag -- scan_end_tag >>
		       (fn (chldr,id') => if id = id'
					  then chldr
					  else raise XML "Tag mismatch")
and scan_tag toks =
    let
	val ((id,atts),toks2) = scan_start_of_tag toks
	val (chldr,toks3) = (scan_children id || scan_end_of_tag) toks2
    in
	(Elem (id,atts,chldr),toks3)
    end
end

val type_of = Term.type_of

val boolT = Type("bool",[])
val propT = Type("prop",[])

fun mk_defeq name rhs thy =
    let
	val ty = type_of rhs
    in
	Logic.mk_equals (Const(Sign.intern_const (sign_of thy) name,ty),rhs)
    end

fun mk_teq name rhs thy =
    let
	val ty = type_of rhs
    in
	HOLogic.mk_eq (Const(Sign.intern_const (sign_of thy) name,ty),rhs)
    end

fun intern_const_name thyname const thy =
    case get_hol4_const_mapping thyname const thy of
	Some (_,cname,_) => cname
      | None => (case get_hol4_const_renaming thyname const thy of
		     Some cname => Sign.intern_const (sign_of thy) (thyname ^ "." ^ cname)
		   | None => Sign.intern_const (sign_of thy) (thyname ^ "." ^ const))

fun intern_type_name thyname const thy =
    case get_hol4_type_mapping thyname const thy of
	Some (_,cname) => cname
      | None => Sign.intern_const (sign_of thy) (thyname ^ "." ^ const)

fun mk_vartype name = TFree(name,["HOL.type"])
fun mk_thy_type thy Thy Tyop Args = Type(intern_type_name Thy Tyop thy,Args)

val mk_var = Free

fun dom_rng (Type("fun",[dom,rng])) = (dom,rng)
  | dom_rng _ = raise ERR "dom_rng" "Not a functional type"

fun mk_thy_const thy Thy Name Ty = Const(intern_const_name Thy Name thy,Ty)

local
    fun get_type sg thyname name =
	case Sign.const_type sg name of
	    Some ty => ty
	  | None => raise ERR "get_type" (name ^ ": No such constant")
in
fun prim_mk_const thy Thy Name =
    let
	val name = intern_const_name Thy Name thy
	val cmaps = HOL4ConstMaps.get thy
    in
	case StringPair.lookup(cmaps,(Thy,Name)) of
	    Some(_,_,Some ty) => Const(name,ty)
	  | _ => Const(name,get_type (sign_of thy) Thy name)
    end
end

fun mk_comb(f,a) = f $ a
fun mk_abs(x,a) = Term.lambda x a

(* Needed for HOL Light *)
fun protect_tyvarname s =
    let
	fun no_quest s =
	    if Char.contains s #"?"
	    then String.translate (fn #"?" => "q_" | c => Char.toString c) s
	    else s
	fun beg_prime s =
	    if String.isPrefix "'" s
	    then s
	    else "'" ^ s
    in
	s |> no_quest |> beg_prime
    end
fun protect_varname s =
    let
	fun no_beg_underscore s =
	    if String.isPrefix "_" s
	    then "dummy" ^ s
	    else s
    in
	s |> no_beg_underscore
    end

structure TypeNet =
struct
fun get_type_from_index thy thyname types is =
    case Int.fromString is of
	SOME i => (case Array.sub(types,i) of
		       FullType ty => ty
		     | XMLty xty =>
		       let
			   val ty = get_type_from_xml thy thyname types xty
			   val _  = Array.update(types,i,FullType ty)
		       in
			   ty
		       end)
      | NONE => raise ERR "get_type_from_index" "Bad index"
and get_type_from_xml thy thyname types =
    let
	fun gtfx (Elem("tyi",[("i",iS)],[])) =
		 get_type_from_index thy thyname types iS
	  | gtfx (Elem("tyc",atts,[])) =
	    mk_thy_type thy
			(get_segment thyname atts)
			(get_name atts)
			[]
	  | gtfx (Elem("tyv",[("n",s)],[])) = mk_vartype (protect_tyvarname s)
	  | gtfx (Elem("tya",[],(Elem("tyc",atts,[]))::tys)) =
	    mk_thy_type thy
			(get_segment thyname atts)
			(get_name atts)
			(map gtfx tys)
	  | gtfx _ = raise ERR "get_type" "Bad type"
    in
	gtfx
    end

fun input_types thyname (Elem("tylist",[("i",i)],xtys)) =
    let
	val types = Array.array(valOf (Int.fromString i),XMLty (Elem("",[],[])))
	fun IT _ [] = ()
	  | IT n (xty::xtys) =
	    (Array.update(types,n,XMLty xty);
	     IT (n+1) xtys)
	val _ = IT 0 xtys
    in
	types
    end
  | input_types _ _ = raise ERR "input_types" "Bad type list"
end

structure TermNet =
struct
fun get_term_from_index thy thyname types terms is =
    case Int.fromString is of
	SOME i => (case Array.sub(terms,i) of
		       FullTerm tm => tm
		     | XMLtm xtm =>
		       let
			   val tm = get_term_from_xml thy thyname types terms xtm
			   val _  = Array.update(terms,i,FullTerm tm)
		       in
			   tm
		       end)
      | NONE => raise ERR "get_term_from_index" "Bad index"
and get_term_from_xml thy thyname types terms =
    let
	fun get_type [] = None
	  | get_type [ty] = Some (TypeNet.get_type_from_xml thy thyname types ty)
	  | get_type _ = raise ERR "get_term" "Bad type"

	fun gtfx (Elem("tmv",[("n",name),("t",tyi)],[])) =
	    mk_var(protect_varname name,TypeNet.get_type_from_index thy thyname types tyi)
	  | gtfx (Elem("tmc",atts,[])) =
	    let
		val segment = get_segment thyname atts
		val name = get_name atts
	    in
		mk_thy_const thy segment name (TypeNet.get_type_from_index thy thyname types (Lib.assoc "t" atts))
		handle PK _ => prim_mk_const thy segment name
	    end
	  | gtfx (Elem("tma",[("f",tmf),("a",tma)],[])) =
	    let
		val f = get_term_from_index thy thyname types terms tmf
		val a = get_term_from_index thy thyname types terms tma
	    in
		mk_comb(f,a)
	    end
	  | gtfx (Elem("tml",[("x",tmx),("a",tma)],[])) =
	    let
		val x = get_term_from_index thy thyname types terms tmx
		val a = get_term_from_index thy thyname types terms tma
	    in
		mk_abs(x,a)
	    end
	  | gtfx (Elem("tmi",[("i",iS)],[])) =
	    get_term_from_index thy thyname types terms iS
	  | gtfx (Elem(tag,_,_)) =
	    raise ERR "get_term" ("Not a term: "^tag)
    in
	gtfx
    end

fun input_terms thyname types (Elem("tmlist",[("i",i)],xtms)) =
    let
	val terms = Array.array(valOf(Int.fromString i),XMLtm (Elem("",[],[])))

	fun IT _ [] = ()
	  | IT n (xtm::xtms) =
	    (Array.update(terms,n,XMLtm xtm);
	     IT (n+1) xtms)
	val _ = IT 0 xtms
    in
	terms
    end
  | input_terms _ _ _ = raise ERR "input_terms" "Bad term list"
end

fun get_proof_dir (thyname:string) thy =
    let
	val import_segment =
	    case get_segment2 thyname thy of
		Some seg => seg
	      | None => get_import_segment thy
	val defpath = [OS.Path.joinDirFile {dir=getenv "ISABELLE_HOME_USER",file="proofs"}]
	val path = space_explode ":" (getenv "PROOF_DIRS") @ defpath
	fun find [] = None
	  | find (p::ps) =
	    (let
		 val dir = OS.Path.joinDirFile {dir = p,file=import_segment}
	     in
		 if OS.FileSys.isDir dir
		 then Some dir
		 else find ps
	     end) handle OS.SysErr _ => find ps
    in
	apsome (fn p => OS.Path.joinDirFile {dir = p, file = thyname}) (find path)
    end
			   
fun proof_file_name thyname thmname thy =
    let
	val path = case get_proof_dir thyname thy of
		       Some p => p
		     | None => error "Cannot find proof files"
	val _ = OS.FileSys.mkDir path handle OS.SysErr _ => ()
    in
	OS.Path.joinDirFile {dir = path, file = OS.Path.joinBaseExt {base = thmname, ext = SOME "prf"}}
    end
	
fun xml_to_proof thyname types terms prf thy =
    let
	val xml_to_hol_type = TypeNet.get_type_from_xml thy thyname types
	val xml_to_term = TermNet.get_term_from_xml thy thyname types terms

	fun index_to_term is =
	    TermNet.get_term_from_index thy thyname types terms is

	fun x2p (Elem("prefl",[("i",is)],[])) = mk_proof (PRefl (index_to_term is))
	  | x2p (Elem("pinstt",[],p::lambda)) =
	    let
		val p = x2p p
		val lambda = implode_subst (map xml_to_hol_type lambda)
	    in
		mk_proof (PInstT(p,lambda))
	    end
	  | x2p (Elem("psubst",[("i",is)],prf::prfs)) =
	    let
		val tm = index_to_term is
		val prf = x2p prf
		val prfs = map x2p prfs
	    in
		mk_proof (PSubst(prfs,tm,prf))
	    end
	  | x2p (Elem("pabs",[("i",is)],[prf])) =
	    let
		val p = x2p prf
		val t = index_to_term is
	    in
		mk_proof (PAbs (p,t))
	    end
	  | x2p (Elem("pdisch",[("i",is)],[prf])) =
	    let
		val p = x2p prf
		val t = index_to_term is
	    in
		mk_proof (PDisch (p,t))
	    end
	  | x2p (Elem("pmp",[],[prf1,prf2])) =
	    let
		val p1 = x2p prf1
		val p2 = x2p prf2
	    in
		mk_proof (PMp(p1,p2))
	    end
	  | x2p (Elem("phyp",[("i",is)],[])) = mk_proof (PHyp (index_to_term is))
	  | x2p (Elem("paxiom",[("n",n),("i",is)],[])) =
	    mk_proof (PAxm(n,index_to_term is))
	  | x2p (Elem("pfact",atts,[])) =
	    let
		val thyname = get_segment thyname atts
		val thmname = get_name atts
		val p = mk_proof PDisk
		val _  = set_disk_info_of p thyname thmname
	    in
		p
	    end
	  | x2p (Elem("pdef",[("s",seg),("n",name),("i",is)],[])) =
	    mk_proof (PDef(seg,name,index_to_term is))
	  | x2p (Elem("ptmspec",[("s",seg)],p::names)) =
	    let
		val names = map (fn Elem("name",[("n",name)],[]) => name
				  | _ => raise ERR "x2p" "Bad proof (ptmspec)") names
	    in
		mk_proof (PTmSpec(seg,names,x2p p))
	    end
	  | x2p (Elem("ptyintro",[("s",seg),("n",name),("a",abs_name),("r",rep_name)],[xP,xt,p])) =
	    let
		val P = xml_to_term xP
		val t = xml_to_term xt
	    in
		mk_proof (PTyIntro(seg,name,abs_name,rep_name,P,t,x2p p))
	    end
	  | x2p (Elem("ptydef",[("s",seg),("n",name)],[p])) =
	    mk_proof (PTyDef(seg,name,x2p p))
	  | x2p (xml as Elem("poracle",[],chldr)) =
	    let
		val (oracles,terms) = Library.partition (fn (Elem("oracle",_,_)) => true | _ => false) chldr
		val ors = map (fn (Elem("oracle",[("n",name)],[])) => name | xml => raise ERR "x2p" "bad oracle") oracles
		val (c,asl) = case terms of
				  [] => raise ERR "x2p" "Bad oracle description"
				| (hd::tl) => (hd,tl)
		val tg = foldr (fn (oracle,tg) => Tag.merge (Tag.read oracle) tg) (ors,Tag.empty_tag)
	    in
		mk_proof (POracle(tg,map xml_to_term asl,xml_to_term c))
	    end
	  | x2p (Elem("pspec",[("i",is)],[prf])) =
	    let
		val p = x2p prf
		val tm = index_to_term is
	    in
		mk_proof (PSpec(p,tm))
	    end
	  | x2p (Elem("pinst",[],p::theta)) =
	    let
		val p = x2p p
		val theta = implode_subst (map xml_to_term theta)
	    in
		mk_proof (PInst(p,theta))
	    end
	  | x2p (Elem("pgen",[("i",is)],[prf])) =
	    let
		val p = x2p prf
		val tm = index_to_term is
	    in
		mk_proof (PGen(p,tm))
	    end
	  | x2p (Elem("pgenabs",[],prf::tms)) =
	    let
		val p = x2p prf
		val tml = map xml_to_term tms
	    in
		mk_proof (PGenAbs(p,None,tml))
	    end
	  | x2p (Elem("pgenabs",[("i",is)],prf::tms)) =
	    let
		val p = x2p prf
		val tml = map xml_to_term tms
	    in
		mk_proof (PGenAbs(p,Some (index_to_term is),tml))
	    end
	  | x2p (Elem("pimpas",[],[prf1,prf2])) =
	    let
		val p1 = x2p prf1
		val p2 = x2p prf2
	    in
		mk_proof (PImpAS(p1,p2))
	    end
	  | x2p (Elem("psym",[],[prf])) =
	    let
		val p = x2p prf
	    in
		mk_proof (PSym p)
	    end
	  | x2p (Elem("ptrans",[],[prf1,prf2])) =
	    let
		val p1 = x2p prf1
		val p2 = x2p prf2
	    in
		mk_proof (PTrans(p1,p2))
	    end
	  | x2p (Elem("pcomb",[],[prf1,prf2])) =
	    let
		val p1 = x2p prf1
		val p2 = x2p prf2
	    in
		mk_proof (PComb(p1,p2))
	    end
	  | x2p (Elem("peqmp",[],[prf1,prf2])) =
	    let
		val p1 = x2p prf1
		val p2 = x2p prf2
	    in
		mk_proof (PEqMp(p1,p2))
	    end
	  | x2p (Elem("peqimp",[],[prf])) =
	    let
		val p = x2p prf
	    in
		mk_proof (PEqImp p)
	    end
	  | x2p (Elem("pexists",[("e",ise),("w",isw)],[prf])) =
	    let
		val p = x2p prf
		val ex = index_to_term ise
		val w = index_to_term isw
	    in
		mk_proof (PExists(p,ex,w))
	    end
	  | x2p (Elem("pchoose",[("i",is)],[prf1,prf2])) =
	    let
		val v  = index_to_term is
		val p1 = x2p prf1
		val p2 = x2p prf2
	    in
		mk_proof (PChoose(v,p1,p2))
	    end
	  | x2p (Elem("pconj",[],[prf1,prf2])) =
	    let
		val p1 = x2p prf1
		val p2 = x2p prf2
	    in
		mk_proof (PConj(p1,p2))
	    end
	  | x2p (Elem("pconjunct1",[],[prf])) =
	    let
		val p = x2p prf
	    in
		mk_proof (PConjunct1 p)
	    end
	  | x2p (Elem("pconjunct2",[],[prf])) =
	    let
		val p = x2p prf
	    in
		mk_proof (PConjunct2 p)
	    end
	  | x2p (Elem("pdisj1",[("i",is)],[prf])) =
	    let
		val p = x2p prf
		val t = index_to_term is
	    in
		mk_proof (PDisj1 (p,t))
	    end
	  | x2p (Elem("pdisj2",[("i",is)],[prf])) =
	    let
		val p = x2p prf
		val t = index_to_term is
	    in
		mk_proof (PDisj2 (p,t))
	    end
	  | x2p (Elem("pdisjcases",[],[prf1,prf2,prf3])) =
	    let
		val p1 = x2p prf1
		val p2 = x2p prf2
		val p3 = x2p prf3
	    in
		mk_proof (PDisjCases(p1,p2,p3))
	    end
	  | x2p (Elem("pnoti",[],[prf])) =
	    let
		val p = x2p prf
	    in
		mk_proof (PNotI p)
	    end
	  | x2p (Elem("pnote",[],[prf])) =
	    let
		val p = x2p prf
	    in
		mk_proof (PNotE p)
	    end
	  | x2p (Elem("pcontr",[("i",is)],[prf])) =
	    let
		val p = x2p prf
		val t = index_to_term is
	    in
		mk_proof (PContr (p,t))
	    end
	  | x2p xml = raise ERR "x2p" "Bad proof"
    in
	x2p prf
    end

fun import_proof thyname thmname thy =
    let
	val is = TextIO.openIn(proof_file_name thyname thmname thy)
	val (proof_xml,_) = scan_tag (LazySeq.of_instream is)
	val _ = TextIO.closeIn is
    in
	case proof_xml of
	    Elem("proof",[],xtypes::xterms::prf::rest) =>
	    let
		val types = TypeNet.input_types thyname xtypes
		val terms = TermNet.input_terms thyname types xterms
	    in
		(case rest of
		     [] => None
		   | [xtm] => Some (fn thy => TermNet.get_term_from_xml thy thyname types terms xtm)
		   | _ => raise ERR "import_proof" "Bad argument list",
		 xml_to_proof thyname types terms prf)
	    end
	  | _ => raise ERR "import_proof" "Bad proof"
    end

fun uniq_compose m th i st =
    let
	val res = bicompose false (false,th,m) i st
    in
	case Seq.pull res of
	    Some (th,rest) => (case Seq.pull rest of
				   Some _ => raise ERR "uniq_compose" "Not unique!"
				 | None => th)
	  | None => raise ERR "uniq_compose" "No result"
    end

val reflexivity_thm = thm "refl"
val substitution_thm = thm "subst"
val mp_thm = thm "mp"
val imp_antisym_thm = thm "light_imp_as"
val disch_thm = thm "impI"
val ccontr_thm = thm "ccontr"

val meta_eq_to_obj_eq_thm = thm "meta_eq_to_obj_eq"

val gen_thm = thm "HOLallI"
val choose_thm = thm "exE"
val exists_thm = thm "exI"
val conj_thm = thm "conjI"
val conjunct1_thm = thm "conjunct1"
val conjunct2_thm = thm "conjunct2"
val spec_thm = thm "spec"
val disj_cases_thm = thm "disjE"
val disj1_thm = thm "disjI1"
val disj2_thm = thm "disjI2"

local
    val th = thm "not_def"
    val sg = sign_of_thm th
    val pp = reflexive (cterm_of sg (Const("Trueprop",boolT-->propT)))
in
val not_elim_thm = combination pp th
end

val not_intro_thm = symmetric not_elim_thm
val abs_thm = thm "ext"
val trans_thm = thm "trans"
val symmetry_thm = thm "sym"
val transitivity_thm = thm "trans"
val eqmp_thm = thm "iffD1"
val eqimp_thm = thm "HOL4Setup.eq_imp"
val comb_thm = thm "cong"

(* Beta-eta normalizes a theorem (only the conclusion, not the *
hypotheses!)  *)

fun beta_eta_thm th =
    let
	val th1 = Thm.equal_elim (Thm.beta_conversion true (cprop_of th))  th
	val th2 = Thm.equal_elim (Thm.eta_conversion       (cprop_of th1)) th1
    in
	th2
    end

fun implies_elim_all th =
    foldl (fn (th,p) => implies_elim th (assume p)) (th,cprems_of th)

fun norm_hyps th =
    th |> beta_eta_thm
       |> implies_elim_all
       |> implies_intr_hyps

fun mk_GEN v th sg =
    let
	val c = HOLogic.dest_Trueprop (concl_of th)
	val cv = cterm_of sg v
	val lc = Term.lambda v c
	val clc = Thm.cterm_of sg lc
	val cvty = ctyp_of_term cv
	val th1 = implies_elim_all th
	val th2 = beta_eta_thm (forall_intr cv th1)
	val th3 = th2 COMP (beta_eta_thm (Drule.instantiate' [Some cvty] [Some clc] gen_thm))
	val c = prop_of th3
	val vname = fst(dest_Free v)
	val (cold,cnew) = case c of
			      tpc $ (Const("All",allT) $ Abs(oldname,ty,body)) =>
			      (Abs(oldname,dummyT,Bound 0),Abs(vname,dummyT,Bound 0))
			    | tpc $ (Const("All",allT) $ rest) => (tpc,tpc)
			    | _ => raise ERR "mk_GEN" "Unknown conclusion"
	val th4 = Thm.rename_boundvars cold cnew th3
	val res = implies_intr_hyps th4
    in
	res
    end

(* rotate left k places, leaving the first j and last l premises alone
*)

fun permute_prems j k 0 th = Thm.permute_prems j k th
  | permute_prems j k l th =
    th |> Thm.permute_prems 0 (~l)
       |> Thm.permute_prems (j+l) k
       |> Thm.permute_prems 0 l

fun rearrange sg tm th =
    let
	val tm' = Pattern.beta_eta_contract tm
	fun find []      n = permute_prems 0 1 0 (implies_intr (Thm.cterm_of sg tm) th)
	  | find (p::ps) n = if tm' aconv (Pattern.beta_eta_contract p)
			     then permute_prems n 1 0 th
			     else find ps (n+1)
    in
	find (prems_of th) 0
    end

fun zip (x::xs) (y::ys) = (x,y)::(zip xs ys)
  | zip [] [] = []
  | zip _ _ = raise ERR "zip" "arguments not of same length"

fun mk_INST dom rng th =
    th |> forall_intr_list dom
       |> forall_elim_list rng

fun apply_tyinst_typ tyinst =
    let
	fun G (ty as TFree _) =
	    (case try (Lib.assoc ty) tyinst of
		 Some ty' => ty'
	       | None => ty)
	  | G (Type(tyname,tys)) = Type(tyname,map G tys)
	  | G (TVar _) = raise ERR "apply_tyinst_typ" "Scematic variable found"
    in
	G
    end

fun apply_tyinst_term tyinst =
    let
	val G = apply_tyinst_typ tyinst
	fun F (tm as Bound _) = tm
	  | F (tm as Free(vname,ty)) = Free(vname,G ty)
	  | F (tm as Const(vname,ty)) = Const(vname,G ty)
	  | F (tm1 $ tm2) = (F tm1) $ (F tm2)
	  | F (Abs(vname,ty,body)) = Abs(vname,G ty,F body)
	  | F (Var _) = raise ERR "apply_tyinst_term" "Schematic variable found"
    in
	F
    end

fun apply_inst_term tminst =
    let
	fun F (tm as Bound _) = tm
	  | F (tm as Free _) =
	    (case try (Lib.assoc tm) tminst of
		 Some tm' => tm'
	       | None => tm)
	  | F (tm as Const _) = tm
	  | F (tm1 $ tm2) = (F tm1) $ (F tm2)
	  | F (Abs(vname,ty,body)) = Abs(vname,ty,F body)
	  | F (Var _) = raise ERR "apply_inst_term" "Schematic variable found"
    in
	F
    end

val collect_vars =
    let
	fun F vars (Bound _) = vars
	  | F vars (tm as Free _) =
	    if tm mem vars
	    then vars
	    else (tm::vars)
	  | F vars (Const _) = vars
	  | F vars (tm1 $ tm2) = F (F vars tm1) tm2
	  | F vars (Abs(_,_,body)) = F vars body
	  | F vars (Var _) = raise ERR "collect_vars" "Schematic variable found"
    in
	F []
    end

(* Code for disambiguating variablenames (wrt. types) *)

val disamb_info_empty = {vars=[],rens=[]}

fun rens_of {vars,rens} = rens

fun name_of_var (Free(vname,_)) = vname
  | name_of_var _ = raise ERR "name_of_var" "Not a variable"

fun disamb_helper {vars,rens} tm =
    let
	val varstm = collect_vars tm
	fun process (v as Free(vname,ty),(vars,rens,inst)) =
	    if v mem vars
	    then (vars,rens,inst)
	    else (case try (Lib.assoc v) rens of
		      Some vnew => (vars,rens,(v,vnew)::inst)
		    | None => if exists (fn Free(vname',_) => vname = vname' | _ => raise ERR "disamb_helper" "Bad varlist") vars
			      then
				  let
				      val tmnames = map name_of_var varstm
				      val varnames = map name_of_var vars
				      val (dom,rng) = ListPair.unzip rens
				      val rensnames = (map name_of_var dom) @ (map name_of_var rng)
				      val instnames = map name_of_var (snd (ListPair.unzip inst))
				      val allnames = tmnames @ varnames @ rensnames @ instnames
				      val vnewname = Term.variant allnames vname
				      val vnew = Free(vnewname,ty)
				  in
				      (vars,(v,vnew)::rens,(v,vnew)::inst)
				  end
			      else (v::vars,rens,inst))
	  | process _ = raise ERR "disamb_helper" "Internal error"

	val (vars',rens',inst) =
	    foldr process (varstm,(vars,rens,[]))
    in
	({vars=vars',rens=rens'},inst)
    end

fun disamb_term_from info tm =
    let
	val (info',inst) = disamb_helper info tm
    in
	(info',apply_inst_term inst tm)
    end

fun swap (x,y) = (y,x)

fun has_ren (HOLThm([],_)) = false
  | has_ren _ = true

fun prinfo {vars,rens} = (writeln "Vars:";
			  app prin vars;
			  writeln "Renaming:";
			  app (fn(x,y)=>(prin x; writeln " -->"; prin y)) rens)

fun disamb_thm_from info (hth as HOLThm(rens,thm)) =
    let
	val inv_rens = map swap rens
	val orig_thm = apply_inst_term inv_rens (prop_of thm)
	val (info',inst) = disamb_helper info orig_thm
	val rens' = map (apsnd (apply_inst_term inst)) inv_rens
	val (dom,rng) = ListPair.unzip (rens' @ inst)
	val sg = sign_of_thm thm
	val thm' = mk_INST (map (cterm_of sg) dom) (map (cterm_of sg) rng) thm
    in
	(info',thm')
    end

fun disamb_terms_from info tms =
    foldr (fn (tm,(info,tms)) =>
	      let
		  val (info',tm') = disamb_term_from info tm
	      in
		  (info',tm'::tms)
	      end)
	  (tms,(info,[]))

fun disamb_thms_from info hthms =
    foldr (fn (hthm,(info,thms)) =>
	      let
		  val (info',tm') = disamb_thm_from info hthm
	      in
		  (info',tm'::thms)
	      end)
	  (hthms,(info,[]))

fun disamb_term tm   = disamb_term_from disamb_info_empty tm
fun disamb_terms tms = disamb_terms_from disamb_info_empty tms
fun disamb_thm thm   = disamb_thm_from disamb_info_empty thm
fun disamb_thms thms = disamb_thms_from disamb_info_empty thms

fun norm_hthm sg (hth as HOLThm([],_)) = hth
  | norm_hthm sg (hth as HOLThm(rens,th)) =
    let
	val vars = collect_vars (prop_of th)
	val (rens',inst,_) =
	    foldr (fn((ren as (vold as Free(vname,_),vnew)),
		      (rens,inst,vars)) =>
		     (case Library.find_first (fn Free(v,_) => v = vname | _ => false) vars of
			  Some v' => if v' = vold
				     then (rens,(vnew,vold)::inst,vold::vars)
				     else (ren::rens,(vold,vnew)::inst,vnew::vars)
			| None => (rens,(vnew,vold)::inst,vold::vars))
		   | _ => raise ERR "norm_hthm" "Internal error")
		  (rens,([],[],vars))
	val (dom,rng) = ListPair.unzip inst
	val th' = mk_INST (map (cterm_of sg) dom) (map (cterm_of sg) rng) th
	val nvars = collect_vars (prop_of th')
	val rens' = filter (fn(_,v) => v mem nvars) rens
	val res = HOLThm(rens',th')
    in
	res
    end

(* End of disambiguating code *)

val debug = ref false

fun if_debug f x = if !debug then f x else ()
val message = if_debug writeln

val conjE_helper = Thm.permute_prems 0 1 conjE

fun get_hol4_thm thyname thmname thy =
    case get_hol4_theorem thyname thmname thy of
	Some hth => Some (HOLThm hth)
      | None => 
	let
	    val pending = HOL4Pending.get thy
	in
	    case StringPair.lookup (pending,(thyname,thmname)) of
		Some hth => Some (HOLThm hth)
	      | None => None
	end

fun non_trivial_term_consts tm =
    filter (fn c => not (c = "Trueprop" orelse
			 c = "All" orelse
			 c = "op -->" orelse
			 c = "op &" orelse
			 c = "op =")) (Term.term_consts tm) 

fun match_consts t (* th *) =
    let
	fun add_consts (Const (c, _), cs) =
	    (case c of
		 "op =" => "==" ins_string cs
	       | "op -->" => "==>" ins_string cs
	       | "All" => cs
	       | "all" => cs
	       | "op &" => cs
	       | "Trueprop" => cs
	       | _ => c ins_string cs)
	  | add_consts (t $ u, cs) = add_consts (t, add_consts (u, cs))
	  | add_consts (Abs (_, _, t), cs) = add_consts (t, cs)
	  | add_consts (_, cs) = cs
	val t_consts = add_consts(t,[])
    in
	fn th => eq_set(t_consts,add_consts(prop_of th,[]))
    end

fun split_name str =
    let
	val sub = Substring.all str
	val (f,idx) = apsnd Substring.string (Substring.splitr Char.isDigit sub)
	val (newstr,u) = apboth Substring.string (Substring.splitr (fn c => c = #"_") f)
    in
	if not (idx = "") andalso u = "_"
	then Some (newstr,valOf(Int.fromString idx))
	else None
    end
    handle _ => None

fun rewrite_hol4_term t thy =
    let
	val sg = sign_of thy

	val hol4rews1 = map (transfer_sg sg) (HOL4Rewrites.get thy)
	val hol4ss = empty_ss setmksimps single addsimps hol4rews1
    in
	transfer_sg sg (Simplifier.full_rewrite hol4ss (cterm_of sg t))
    end


fun get_isabelle_thm thyname thmname hol4conc thy =
    let
	val sg = sign_of thy

	val (info,hol4conc') = disamb_term hol4conc
	val i2h_conc = symmetric (rewrite_hol4_term (HOLogic.mk_Trueprop hol4conc') thy)
	val isaconc =
	    case concl_of i2h_conc of
		Const("==",_) $ lhs $ _ => lhs
	      | _ => error "get_isabelle_thm" "Bad rewrite rule"
	val _ = (message "Original conclusion:";
		 if_debug prin hol4conc';
		 message "Modified conclusion:";
		 if_debug prin isaconc)

	fun mk_res th = HOLThm(rens_of info,equal_elim i2h_conc th)
    in
	case get_hol4_mapping thyname thmname thy of
	    Some (Some thmname) =>
	    let
		val _ = message ("Looking for " ^ thmname)
		val th1 = (Some (transform_error (PureThy.get_thm thy) thmname)
			   handle ERROR_MESSAGE _ =>
				  (case split_name thmname of
				       Some (listname,idx) => (Some (nth_elem(idx-1,PureThy.get_thms thy listname))
							       handle _ => None)
				     | None => None))
	    in
		case th1 of
		    Some th2 =>
		    (case Shuffler.set_prop thy isaconc [(thmname,th2)] of
			 Some (_,th) => (message "YES";(thy, Some (mk_res th)))
		       | None => (message "NO2";error "get_isabelle_thm" "Bad mapping"))
		  | None => (message "NO1";error "get_isabelle_thm" "Bad mapping")
	    end
	  | Some None => error ("Trying to access ignored theorem " ^ thmname)
	  | None =>
	    let
		val _ = (message "Looking for conclusion:";
			 if_debug prin isaconc)
		val cs = non_trivial_term_consts isaconc
		val _ = (message "Looking for consts:";
			 message (String.concat cs))
		val pot_thms = Shuffler.find_potential thy isaconc
		val _ = message ((Int.toString (length pot_thms)) ^ " potential theorems")
	    in
		case Shuffler.set_prop thy isaconc pot_thms of
		    Some (isaname,th) =>
		    let
			val hth as HOLThm args = mk_res th
			val thy' =  thy |> add_hol4_theorem thyname thmname args
					|> add_hol4_mapping thyname thmname isaname
		    in
			(thy',Some hth)
		    end
		  | None => (thy,None)
	    end
    end
    handle _ => (thy,None)

fun get_thm thyname thmname thy =
    case get_hol4_thm thyname thmname thy of
	Some hth => (thy,Some hth)
      | None => ((case fst (import_proof thyname thmname thy) of
		      Some f => get_isabelle_thm thyname thmname (f thy) thy
		    | None => (thy,None))
		 handle e as IO.Io _ => (thy,None)
		      | e as PK _ => (thy,None))

fun rename_const thyname thy name =
    case get_hol4_const_renaming thyname name thy of
	Some cname => cname
      | None => name

fun get_def thyname constname rhs thy =
    let
	val constname = rename_const thyname thy constname
	val (thmname,thy') = get_defname thyname constname thy
	val _ = message ("Looking for definition " ^ thyname ^ "." ^ thmname)
    in
	get_isabelle_thm thyname thmname (mk_teq (thyname ^ "." ^ constname) rhs thy') thy'
    end

fun get_axiom thyname axname thy =
    case get_thm thyname axname thy of
	arg as (_,Some _) => arg
      | _ => raise ERR "get_axiom" ("Trying to retrieve axiom (" ^ axname ^ ")")

fun intern_store_thm gen_output thyname thmname hth thy =
    let
	val sg = sign_of thy
	val (hth' as HOLThm (args as (_,th))) = norm_hthm sg hth
	val _ = if has_ren hth' then warning ("Theorem " ^ thmname ^ " needs variable-disambiguating")
		else ()
	val rew = rewrite_hol4_term (concl_of th) thy
	val th  = equal_elim rew th
	val thy' = add_hol4_pending thyname thmname args thy
	val thy2 = if gen_output
		   then add_dump ("lemma " ^ thmname ^ ": " ^ (smart_string_of_thm th) ^ "\n  by (import " ^ thyname ^ " " ^ thmname ^ ")") thy'
		   else thy'
    in
	(thy2,hth')
    end

val store_thm = intern_store_thm true

fun mk_REFL ctm =
    let
	val cty = Thm.ctyp_of_term ctm
    in
	Drule.instantiate' [Some cty] [Some ctm] reflexivity_thm
    end

fun REFL tm thy =
    let
	val _ = message "REFL:"
	val (info,tm') = disamb_term tm
	val sg = sign_of thy
	val ctm = Thm.cterm_of sg tm'
	val res = HOLThm(rens_of info,mk_REFL ctm)
	val _ = if_debug pth res
    in
	(thy,res)
    end

fun ASSUME tm thy =
    let
	val _ = message "ASSUME:"
	val (info,tm') = disamb_term tm
	val sg = sign_of thy
	val ctm = Thm.cterm_of sg (HOLogic.mk_Trueprop tm')
	val th = Thm.trivial ctm
	val res = HOLThm(rens_of info,th)
	val _ = if_debug pth res
    in
	(thy,res)
    end

fun INST_TYPE lambda (hth as HOLThm(rens,th)) thy =
    let
	val _ = message "INST_TYPE:"
	val _ = if_debug pth hth
	val sg = sign_of thy
	val tys_before = add_term_tfrees (prop_of th,[])
	val th1 = varifyT th
	val tys_after = add_term_tvars (prop_of th1,[])
	val tyinst = map (fn (bef,(i,_)) =>
			     (case try (Lib.assoc (TFree bef)) lambda of
				  Some ty => (i,ctyp_of sg ty)
				| None => (i,ctyp_of sg (TFree bef))
			     ))
			 (zip tys_before tys_after)
	val res = Drule.instantiate (tyinst,[]) th1
	val appty = apboth (apply_tyinst_term lambda)
	val hth = HOLThm(map appty rens,res)
	val res = norm_hthm sg hth
	val _ = message "RESULT:"
	val _ = if_debug pth res
    in
	(thy,res)
    end

fun INST sigma hth thy =
    let
	val _ = message "INST:"
	val _ = if_debug (app (fn (x,y) => (prin x; prin y))) sigma
	val _ = if_debug pth hth
	val sg = sign_of thy
	val (sdom,srng) = ListPair.unzip sigma
	val (info,th) = disamb_thm hth
	val (info',srng') = disamb_terms_from info srng
	val rens = rens_of info'
	val sdom' = map (apply_inst_term rens) sdom
	val th1 = mk_INST (map (cterm_of sg) sdom') (map (cterm_of sg) srng') th
	val res = HOLThm(rens,th1)
	val _ = message "RESULT:"
	val _ = if_debug pth res
    in
	(thy,res)
    end

fun EQ_IMP_RULE (hth as HOLThm(rens,th)) thy =
    let
	val _ = message "EQ_IMP_RULE:"
	val _ = if_debug pth hth
	val res = HOLThm(rens,th RS eqimp_thm)
	val _ = message "RESULT:"
	val _ = if_debug pth res
    in
	(thy,res)
    end

fun mk_EQ_MP th1 th2 = [beta_eta_thm th1,beta_eta_thm th2] MRS eqmp_thm

fun EQ_MP hth1 hth2 thy =
    let
	val _ = message "EQ_MP:"
	val _ = if_debug pth hth1
	val _ = if_debug pth hth2
	val (info,[th1,th2]) = disamb_thms [hth1,hth2]
	val res = HOLThm(rens_of info,mk_EQ_MP th1 th2)
	val _ = message "RESULT:"
	val _ = if_debug pth res
    in
	(thy,res)
    end

fun mk_COMB th1 th2 sg =
    let
	val (f,g) = case concl_of th1 of
			_ $ (Const("op =",_) $ f $ g) => (f,g)
		      | _ => raise ERR "mk_COMB" "First theorem not an equality"
	val (x,y) = case concl_of th2 of
			_ $ (Const("op =",_) $ x $ y) => (x,y)
		      | _ => raise ERR "mk_COMB" "Second theorem not an equality"
	val fty = type_of f
	val (fd,fr) = dom_rng fty
	val comb_thm' = Drule.instantiate'
			    [Some (ctyp_of sg fd),Some (ctyp_of sg fr)]
			    [Some (cterm_of sg f),Some (cterm_of sg g),
			     Some (cterm_of sg x),Some (cterm_of sg y)] comb_thm
    in
	[th1,th2] MRS comb_thm'
    end

fun SUBST rews ctxt hth thy =
    let
	val _ = message "SUBST:"
	val _ = if_debug (app pth) rews
	val _ = if_debug prin ctxt
	val _ = if_debug pth hth
	val (info,th) = disamb_thm hth
	val (info1,ctxt') = disamb_term_from info ctxt
	val (info2,rews') = disamb_thms_from info1 rews

	val sg = sign_of thy
	val cctxt = cterm_of sg ctxt'
	fun subst th [] = th
	  | subst th (rew::rews) = subst (mk_COMB th rew sg) rews
	val res = HOLThm(rens_of info2,mk_EQ_MP (subst (mk_REFL cctxt) rews') th)
	val _ = message "RESULT:"
	val _ = if_debug pth res
    in
	(thy,res)
    end

fun DISJ_CASES hth hth1 hth2 thy =
    let
	val _ = message "DISJ_CASES:"
	val _ = if_debug (app pth) [hth,hth1,hth2]
	val (info,th) = disamb_thm hth
	val (info1,th1) = disamb_thm_from info hth1
	val (info2,th2) = disamb_thm_from info1 hth2
	val sg = sign_of thy
	val th1 = norm_hyps th1
	val th2 = norm_hyps th2
	val (l,r) = case concl_of th of
			_ $ (Const("op |",_) $ l $ r) => (l,r)
		      | _ => raise ERR "DISJ_CASES" "Conclusion not a disjunction"
	val th1' = rearrange sg (HOLogic.mk_Trueprop l) th1
	val th2' = rearrange sg (HOLogic.mk_Trueprop r) th2
	val res1 = th RS disj_cases_thm
	val res2 = uniq_compose ((nprems_of th1')-1) th1' ((nprems_of th)+1) res1
	val res3 = uniq_compose ((nprems_of th2')-1) th2' (nprems_of res2) res2
	val res  = HOLThm(rens_of info2,res3)
	val _ = message "RESULT:"
	val _ = if_debug pth res
    in
	(thy,res)
    end

fun DISJ1 hth tm thy =
    let
	val _ = message "DISJ1:"
	val _ = if_debug pth hth
	val _ = if_debug prin tm
	val (info,th) = disamb_thm hth
	val (info',tm') = disamb_term_from info tm
	val sg = sign_of thy
	val ct = Thm.cterm_of sg tm'
	val disj1_thm' = Drule.instantiate' [] [None,Some ct] disj1_thm
	val res = HOLThm(rens_of info',th RS disj1_thm')
	val _ = message "RESULT:"
	val _ = if_debug pth res
    in
	(thy,res)
    end

fun DISJ2 tm hth thy =
    let
	val _ = message "DISJ1:"
	val _ = if_debug prin tm
	val _ = if_debug pth hth
	val (info,th) = disamb_thm hth
	val (info',tm') = disamb_term_from info tm
	val sg = sign_of thy
	val ct = Thm.cterm_of sg tm'
	val disj2_thm' = Drule.instantiate' [] [None,Some ct] disj2_thm
	val res = HOLThm(rens_of info',th RS disj2_thm')
	val _ = message "RESULT:"
	val _ = if_debug pth res
    in
	(thy,res)
    end

fun IMP_ANTISYM hth1 hth2 thy =
    let
	val _ = message "IMP_ANTISYM:"
	val _ = if_debug pth hth1
	val _ = if_debug pth hth2
	val (info,[th1,th2]) = disamb_thms [hth1,hth2]
	val th = [beta_eta_thm th1,beta_eta_thm th2] MRS imp_antisym_thm
	val res = HOLThm(rens_of info,th)
	val _ = message "RESULT:"
	val _ = if_debug pth res
    in
	(thy,res)
    end

fun SYM (hth as HOLThm(rens,th)) thy =
    let
	val _ = message "SYM:"
	val _ = if_debug pth hth
	val th = th RS symmetry_thm
	val res = HOLThm(rens,th)
	val _ = message "RESULT:"
	val _ = if_debug pth res
    in
	(thy,res)
    end

fun MP hth1 hth2 thy =
    let
	val _ = message "MP:"
	val _ = if_debug pth hth1
	val _ = if_debug pth hth2
	val (info,[th1,th2]) = disamb_thms [hth1,hth2]
	val th = [beta_eta_thm th1,beta_eta_thm th2] MRS mp_thm
	val res = HOLThm(rens_of info,th)
	val _ = message "RESULT:"
	val _ = if_debug pth res
    in
	(thy,res)
    end

fun CONJ hth1 hth2 thy =
    let
	val _ = message "CONJ:"
	val _ = if_debug pth hth1
	val _ = if_debug pth hth2
	val (info,[th1,th2]) = disamb_thms [hth1,hth2]
	val th = [th1,th2] MRS conj_thm
	val res = HOLThm(rens_of info,th)
	val _ = message "RESULT:"
	val _ = if_debug pth res
    in
	(thy,res)
    end

fun CONJUNCT1 (hth as HOLThm(rens,th)) thy =
    let
	val _ = message "CONJUNCT1:"
	val _ = if_debug pth hth
	val res = HOLThm(rens,th RS conjunct1_thm)
	val _ = message "RESULT:"
	val _ = if_debug pth res
    in
	(thy,res)
    end

fun CONJUNCT2 (hth as HOLThm(rens,th)) thy =
    let
	val _ = message "CONJUNCT1:"
	val _ = if_debug pth hth
	val res = HOLThm(rens,th RS conjunct2_thm)
	val _ = message "RESULT:"
	val _ = if_debug pth res
    in
	(thy,res)
    end

fun EXISTS ex wit hth thy =
    let
	val _ = message "EXISTS:"
	val _ = if_debug prin ex
	val _ = if_debug prin wit
	val _ = if_debug pth hth
	val (info,th) = disamb_thm hth
	val (info',[ex',wit']) = disamb_terms_from info [ex,wit]
	val sg = sign_of thy
	val cwit = cterm_of sg wit'
	val cty = ctyp_of_term cwit
	val a = case ex' of
		    (Const("Ex",_) $ a) => a
		  | _ => raise ERR "EXISTS" "Argument not existential"
	val ca = cterm_of sg a
	val exists_thm' = beta_eta_thm (Drule.instantiate' [Some cty] [Some ca,Some cwit] exists_thm)
	val th1 = beta_eta_thm th
	val th2 = implies_elim_all th1
	val th3 = th2 COMP exists_thm'
	val th  = implies_intr_hyps th3
	val res = HOLThm(rens_of info',th)
	val _   = message "RESULT:"
	val _   = if_debug pth res
    in
	(thy,res)
    end

fun CHOOSE v hth1 hth2 thy =
    let
	val _ = message "CHOOSE:"
	val _ = if_debug prin v
	val _ = if_debug pth hth1
	val _ = if_debug pth hth2
	val (info,[th1,th2]) = disamb_thms [hth1,hth2]
	val (info',v') = disamb_term_from info v
	fun strip 0 _ th = th
	  | strip n (p::ps) th =
	    strip (n-1) ps (implies_elim th (assume p))
	  | strip _ _ _ = raise ERR "CHOOSE" "strip error"
	val sg = sign_of thy
	val cv = cterm_of sg v'
	val th2 = norm_hyps th2
	val cvty = ctyp_of_term cv
	val c = HOLogic.dest_Trueprop (concl_of th2)
	val cc = cterm_of sg c
	val a = case concl_of th1 of
		    _ $ (Const("Ex",_) $ a) => a
		  | _ => raise ERR "CHOOSE" "Conclusion not existential"
	val ca = cterm_of (sign_of_thm th1) a
	val choose_thm' = beta_eta_thm (Drule.instantiate' [Some cvty] [Some ca,Some cc] choose_thm)
	val th21 = rearrange sg (HOLogic.mk_Trueprop (a $ v')) th2
	val th22 = strip ((nprems_of th21)-1) (cprems_of th21) th21
	val th23 = beta_eta_thm (forall_intr cv th22)
	val th11 = implies_elim_all (beta_eta_thm th1)
	val th' = th23 COMP (th11 COMP choose_thm')
	val th = implies_intr_hyps th'
	val res = HOLThm(rens_of info',th)
	val _   = message "RESULT:"
	val _   = if_debug pth res
    in
	(thy,res)
    end

fun GEN v hth thy =
    let
	val _ = message "GEN:"
	val _ = if_debug prin v
	val _ = if_debug pth hth
	val (info,th) = disamb_thm hth
	val (info',v') = disamb_term_from info v
	val res = HOLThm(rens_of info',mk_GEN v' th (sign_of thy))
	val _ = message "RESULT:"
	val _ = if_debug pth res
    in
	(thy,res)
    end

fun SPEC tm hth thy =
    let
	val _ = message "SPEC:"
	val _ = if_debug prin tm
	val _ = if_debug pth hth
	val (info,th) = disamb_thm hth
	val (info',tm') = disamb_term_from info tm
	val sg = sign_of thy
	val ctm = Thm.cterm_of sg tm'
	val cty = Thm.ctyp_of_term ctm
	val spec' = Drule.instantiate' [Some cty] [None,Some ctm] spec_thm
	val th = th RS spec'
	val res = HOLThm(rens_of info',th)
	val _ = message "RESULT:"
	val _ = if_debug pth res
    in
	(thy,res)
    end

fun COMB hth1 hth2 thy =
    let
	val _ = message "COMB:"
	val _ = if_debug pth hth1
	val _ = if_debug pth hth2
	val (info,[th1,th2]) = disamb_thms [hth1,hth2]
	val sg = sign_of thy
	val res = HOLThm(rens_of info,mk_COMB th1 th2 sg)
	val _ = message "RESULT:"
	val _ = if_debug pth res
    in
	(thy,res)
    end

fun TRANS hth1 hth2 thy =
    let
	val _ = message "TRANS:"
	val _ = if_debug pth hth1
	val _ = if_debug pth hth2
	val (info,[th1,th2]) = disamb_thms [hth1,hth2]
	val th = [th1,th2] MRS trans_thm
	val res = HOLThm(rens_of info,th)
	val _ = message "RESULT:"
	val _ = if_debug pth res
    in
	(thy,res)
    end
	

fun CCONTR tm hth thy =
    let
	val _ = message "SPEC:"
	val _ = if_debug prin tm
	val _ = if_debug pth hth
	val (info,th) = disamb_thm hth
	val (info',tm') = disamb_term_from info tm
	val th = norm_hyps th
	val sg = sign_of thy
	val ct = cterm_of sg tm'
	val th1 = rearrange sg (HOLogic.mk_Trueprop (Const("Not",boolT-->boolT) $ tm')) th
	val ccontr_thm' = Drule.instantiate' [] [Some ct] ccontr_thm
	val res1 = uniq_compose ((nprems_of th1) - 1) th1 1 ccontr_thm'
	val res = HOLThm(rens_of info',res1)
	val _ = message "RESULT:"
	val _ = if_debug pth res
    in
	(thy,res)
    end

fun mk_ABS v th sg =
    let
	val cv = cterm_of sg v
	val th1 = implies_elim_all (beta_eta_thm th)
	val (f,g) = case concl_of th1 of
			_ $ (Const("op =",_) $ f $ g) => (Term.lambda v f,Term.lambda v g)
		      | _ => raise ERR "mk_ABS" "Bad conclusion"
	val (fd,fr) = dom_rng (type_of f)
	val abs_thm' = Drule.instantiate' [Some (ctyp_of sg fd), Some (ctyp_of sg fr)] [Some (cterm_of sg f), Some (cterm_of sg g)] abs_thm
	val th2 = forall_intr cv th1
	val th3 = th2 COMP abs_thm'
	val res = implies_intr_hyps th3
    in
	res
    end

fun ABS v hth thy =
    let
	val _ = message "ABS:"
	val _ = if_debug prin v
	val _ = if_debug pth hth
	val (info,th) = disamb_thm hth
	val (info',v') = disamb_term_from info v
	val sg = sign_of thy
	val res = HOLThm(rens_of info',mk_ABS v' th sg)
	val _ = message "RESULT:"
	val _ = if_debug pth res
    in
	(thy,res)
    end

fun GEN_ABS copt vlist hth thy =
    let
	val _ = message "GEN_ABS:"
	val _ = case copt of
		    Some c => if_debug prin c
		  | None => ()
	val _ = if_debug (app prin) vlist
	val _ = if_debug pth hth
	val (info,th) = disamb_thm hth
	val (info',vlist') = disamb_terms_from info vlist
	val sg = sign_of thy
	val th1 =
	    case copt of
		Some (c as Const(cname,cty)) =>
		let
		    fun inst_type ty1 ty2 (TVar _) = raise ERR "GEN_ABS" "Type variable found!"
		      | inst_type ty1 ty2 (ty as TFree _) = if ty1 = ty
							    then ty2
							    else ty
		      | inst_type ty1 ty2 (ty as Type(name,tys)) =
			Type(name,map (inst_type ty1 ty2) tys)
		in
		    foldr (fn (v,th) =>
			      let
				  val cdom = fst (dom_rng (fst (dom_rng cty)))
				  val vty  = type_of v
				  val newcty = inst_type cdom vty cty
				  val cc = cterm_of sg (Const(cname,newcty))
			      in
				  mk_COMB (mk_REFL cc) (mk_ABS v th sg) sg
			      end) (vlist',th)
		end
	      | Some _ => raise ERR "GEN_ABS" "Bad constant"
	      | None => 
		foldr (fn (v,th) => mk_ABS v th sg) (vlist',th)
	val res = HOLThm(rens_of info',th1)
	val _ = message "RESULT:"
	val _ = if_debug pth res
    in
	(thy,res)
    end

fun NOT_INTRO (hth as HOLThm(rens,th)) thy =
    let
	val _ = message "NOT_INTRO:"
	val _ = if_debug pth hth
	val sg = sign_of thy
	val th1 = implies_elim_all (beta_eta_thm th)
	val a = case concl_of th1 of
		    _ $ (Const("op -->",_) $ a $ Const("False",_)) => a
		  | _ => raise ERR "NOT_INTRO" "Conclusion of bad form"
	val ca = cterm_of sg a
	val th2 = equal_elim (Drule.instantiate' [] [Some ca] not_intro_thm) th1
	val res = HOLThm(rens,implies_intr_hyps th2)
	val _ = message "RESULT:"
	val _ = if_debug pth res
    in
	(thy,res)
    end

fun NOT_ELIM (hth as HOLThm(rens,th)) thy =
    let
	val _ = message "NOT_INTRO:"
	val _ = if_debug pth hth
	val sg = sign_of thy
	val th1 = implies_elim_all (beta_eta_thm th)
	val a = case concl_of th1 of
		    _ $ (Const("Not",_) $ a) => a
		  | _ => raise ERR "NOT_ELIM" "Conclusion of bad form"
	val ca = cterm_of sg a
	val th2 = equal_elim (Drule.instantiate' [] [Some ca] not_elim_thm) th1
	val res = HOLThm(rens,implies_intr_hyps th2)
	val _ = message "RESULT:"
	val _ = if_debug pth res
    in
	(thy,res)
    end

fun DISCH tm hth thy =
    let
	val _ = message "DISCH:"
	val _ = if_debug prin tm
	val _ = if_debug pth hth
	val (info,th) = disamb_thm hth
	val (info',tm') = disamb_term_from info tm
	val prems = prems_of th
	val sg = sign_of thy
	val th1 = beta_eta_thm th
	val th2 = implies_elim_all th1
	val th3 = implies_intr (cterm_of sg (HOLogic.mk_Trueprop tm')) th2
	val th4 = th3 COMP disch_thm
	val res = HOLThm(rens_of info',implies_intr_hyps th4)
	val _ = message "RESULT:"
	val _ = if_debug pth res
    in
	(thy,res)
    end

val spaces = String.concat o separate " "

fun new_definition thyname constname rhs thy =
    let
	val constname = rename_const thyname thy constname
	val _ = warning ("Introducing constant " ^ constname)
	val (thmname,thy) = get_defname thyname constname thy
	val (info,rhs') = disamb_term rhs
	val ctype = type_of rhs'
	val csyn = mk_syn constname
	val thy1 = case HOL4DefThy.get thy of
		       Replaying _ => thy
		     | _ => Theory.add_consts_i [(constname,ctype,csyn)] thy
	val eq = mk_defeq constname rhs' thy1
	val (thy2,thms) = PureThy.add_defs_i false [((thmname,eq),[])] thy1
	val def_thm = hd thms
	val thm' = def_thm RS meta_eq_to_obj_eq_thm
	val (thy',th) = (thy2, thm')
	val fullcname = Sign.intern_const (sign_of thy') constname
	val thy'' = add_hol4_const_mapping thyname constname true fullcname thy'
	val (linfo,tm24) = disamb_term (mk_teq constname rhs' thy'')
	val sg = sign_of thy''
	val rew = rewrite_hol4_term eq thy''
	val crhs = cterm_of sg (#2 (Logic.dest_equals (prop_of rew)))
	val thy22 = if (def_name constname) = thmname
		    then
			add_dump ("constdefs\n  " ^ (quotename constname) ^ " :: \"" ^ (string_of_ctyp (ctyp_of sg ctype)) ^ "\" " ^ (Syntax.string_of_mixfix csyn) ^ "\n  " ^ (smart_string_of_cterm crhs)) thy''
		    else
			add_dump ("consts\n  " ^ (quotename constname) ^ " :: \"" ^ (string_of_ctyp (ctyp_of sg ctype)) ^
				  "\" " ^ (Syntax.string_of_mixfix csyn) ^ "\n\ndefs\n  " ^ (quotename thmname) ^ ": " ^ (smart_string_of_cterm crhs))
				 thy''

	val hth = case Shuffler.set_prop thy22 (HOLogic.mk_Trueprop tm24) [("",th)] of
		     Some (_,res) => HOLThm(rens_of linfo,res)
		   | None => raise ERR "new_definition" "Bad conclusion"
	val fullname = Sign.full_name sg thmname
	val thy22' = case opt_get_output_thy thy22 of
			 "" => add_hol4_mapping thyname thmname fullname thy22
		       | output_thy =>
			 let
			     val moved_thmname = output_thy ^ "." ^ thyname ^ "." ^ thmname
			 in
			     thy22 |> add_hol4_move fullname moved_thmname
				   |> add_hol4_mapping thyname thmname moved_thmname
			 end
	val _ = message "new_definition:"
	val _ = if_debug pth hth
    in
	(thy22',hth)
    end
    handle e => (message "exception in new_definition"; print_exn e)

val commafy = String.concat o separate ", "

local
    val helper = thm "termspec_help"
in
fun new_specification thyname thmname names hth thy =
    case HOL4DefThy.get thy of
	Replaying _ => (thy,hth)
      | _ => 
	let
	    val _ = message "NEW_SPEC:"
	    val _ = if_debug pth hth
	    val names = map (rename_const thyname thy) names
	    val _ = warning ("Introducing constants " ^ (commafy names))
	    val (HOLThm(rens,th)) = norm_hthm (sign_of thy) hth
	    val thy1 = case HOL4DefThy.get thy of
			   Replaying _ => thy
			 | _ =>
			   let
			       fun dest_eta_abs (Abs(x,xT,body)) = (x,xT,body)
				 | dest_eta_abs body =
				   let
				       val (dT,rT) = dom_rng (type_of body)
				   in
				       ("x",dT,body $ Bound 0)
				   end
				   handle TYPE _ => raise ERR "new_specification" "not an abstraction type"
			       fun dest_exists (Const("Ex",_) $ abody) =
				   dest_eta_abs abody
				 | dest_exists tm =
				   raise ERR "new_specification" "Bad existential formula"
					 
			       val (consts,_) = foldl (fn ((cs,ex),cname) =>
							  let
							      val (_,cT,p) = dest_exists ex
							  in
							      ((cname,cT,mk_syn cname)::cs,p)
							  end) (([],HOLogic.dest_Trueprop (concl_of th)),names)
			       val sg = sign_of thy
			       val str = foldl (fn (acc,(c,T,csyn)) =>
						   acc ^ "\n  " ^ (quotename c) ^ " :: \"" ^ (string_of_ctyp (ctyp_of sg T)) ^ "\" " ^ (Syntax.string_of_mixfix csyn)) ("consts",consts)
			       val thy' = add_dump str thy
			   in
			       Theory.add_consts_i consts thy'
			   end

	    val thy1 = foldr (fn(name,thy)=>
				snd (get_defname thyname name thy)) (names,thy1)
	    fun new_name name = fst (get_defname thyname name thy1)
	    val (thy',res) = SpecificationPackage.add_specification_i None
				 (map (fn name => (new_name name,name,false)) names)
				 (thy1,th)
	    val res' = Drule.freeze_all res
	    val hth = HOLThm(rens,res')
	    val rew = rewrite_hol4_term (concl_of res') thy'
	    val th  = equal_elim rew res'
	    fun handle_const (name,thy) =
		let
		    val defname = def_name name
		    val (newname,thy') = get_defname thyname name thy
		in
		    (if defname = newname
		     then quotename name
		     else (quotename newname) ^ ": " ^ (quotename name),thy')
		end
	    val (new_names,thy') = foldr (fn(name,(names,thy)) =>
					    let
						val (name',thy') = handle_const (name,thy)
					    in
						(name'::names,thy')
					    end) (names,([],thy'))
	    val thy'' = add_dump ("specification (" ^ (spaces new_names) ^ ") " ^ thmname ^ ": " ^ (smart_string_of_thm th) ^
				  "\n  by (import " ^ thyname ^ " " ^ thmname ^ ")")
				 thy'
	    val _ = message "RESULT:"
	    val _ = if_debug pth hth
	in
	    intern_store_thm false thyname thmname hth thy''
	end
	handle e => (message "exception in new_specification"; print_exn e)
		    
end
			   
fun new_axiom name tm thy = raise ERR "new_axiom" ("Oh, no you don't! (" ^ name ^ ")")
				      
fun to_isa_thm (hth as HOLThm(_,th)) =
    let
	val (HOLThm args) = norm_hthm (sign_of_thm th) hth
    in
	apsnd strip_shyps args
    end

fun to_isa_term tm = tm

local
    val light_nonempty = thm "light_ex_imp_nonempty"
    val ex_imp_nonempty = thm "ex_imp_nonempty"
    val typedef_hol2hol4 = thm "typedef_hol2hol4"
    val typedef_hol2hollight = thm "typedef_hol2hollight"
in
fun new_type_definition thyname thmname tycname hth thy =
    case HOL4DefThy.get thy of
	Replaying _ => (thy,hth)
      | _ => 
	let
	    val _ = message "TYPE_DEF:"
	    val _ = if_debug pth hth
	    val _ = warning ("Introducing type " ^ tycname)
	    val (HOLThm(rens,td_th)) = norm_hthm (sign_of thy) hth
	    val th2 = beta_eta_thm (td_th RS ex_imp_nonempty)
	    val c = case concl_of th2 of
			_ $ (Const("Ex",_) $ Abs(_,_,Const("op :",_) $ _ $ c)) => c
		      | _ => raise ERR "new_type_definition" "Bad type definition theorem"
	    val tfrees = term_tfrees c
	    val tnames = map fst tfrees
	    val tsyn = mk_syn tycname
	    val typ = (tycname,tnames,tsyn)
	    val (thy',typedef_info) = TypedefPackage.add_typedef_i false (Some thmname) typ c None (rtac th2 1) thy
				      
	    val th3 = (#type_definition typedef_info) RS typedef_hol2hol4

	    val fulltyname = Sign.intern_tycon (sign_of thy') tycname
	    val thy'' = add_hol4_type_mapping thyname tycname true fulltyname thy'

	    val sg = sign_of thy''
	    val (hth' as HOLThm args) = norm_hthm sg (HOLThm(rens,th3))
	    val _ = if has_ren hth' then warning ("Theorem " ^ thmname ^ " needs variable-disambiguating")
		    else ()
	    val thy4 = add_hol4_pending thyname thmname args thy''

	    val sg = sign_of thy4
	    val rew = rewrite_hol4_term (concl_of td_th) thy4
	    val th  = equal_elim rew (transfer_sg sg td_th)
	    val c   = case HOLogic.dest_Trueprop (prop_of th) of
			  Const("Ex",exT) $ P =>
			  let
			      val PT = domain_type exT
			  in
			      Const("Collect",PT-->HOLogic.mk_setT (domain_type PT)) $ P
			  end
			| _ => error "Internal error in ProofKernel.new_typedefinition"
	    val tnames_string = if null tnames
				then ""
				else "(" ^ (commafy tnames) ^ ") "
	    val proc_prop = if null tnames
			    then smart_string_of_cterm
			    else Library.setmp show_all_types true smart_string_of_cterm
	    val thy5 = add_dump ("typedef (open) " ^ tnames_string ^ (quotename tycname) ^ " = " ^ (proc_prop (cterm_of sg c)) ^ " " ^ (Syntax.string_of_mixfix tsyn) ^ "\n  by (rule typedef_helper,import " ^ thyname ^ " " ^ thmname ^ ")") thy4
	    val thy6 = add_dump ("lemmas " ^ thmname ^ " = typedef_hol2hol4 [OF type_definition_" ^ tycname ^ "]")
		       thy5
	    val _ = message "RESULT:"
	    val _ = if_debug pth hth'
	in
	    (thy6,hth')
	end
	handle e => (message "exception in new_type_definition"; print_exn e)

fun type_introduction thyname thmname tycname abs_name rep_name (P,t) hth thy =
    case HOL4DefThy.get thy of
	Replaying _ => (thy,hth)
      | _ => 
	let
	    val _ = message "TYPE_INTRO:"
	    val _ = if_debug pth hth
	    val _ = warning ("Introducing type " ^ tycname ^ " (with morphisms " ^ abs_name ^ " and " ^ rep_name ^ ")")
	    val (HOLThm(rens,td_th)) = norm_hthm (sign_of thy) hth
	    val sg = sign_of thy
	    val tT = type_of t
	    val light_nonempty' =
		Drule.instantiate' [Some (ctyp_of sg tT)]
				   [Some (cterm_of sg P),
				    Some (cterm_of sg t)] light_nonempty
	    val th2 = beta_eta_thm (td_th RS (beta_eta_thm light_nonempty'))
	    val c = case concl_of th2 of
			_ $ (Const("Ex",_) $ Abs(_,_,Const("op :",_) $ _ $ c)) => c
		      | _ => raise ERR "type_introduction" "Bad type definition theorem"
	    val tfrees = term_tfrees c
	    val tnames = map fst tfrees
	    val tsyn = mk_syn tycname
	    val typ = (tycname,tnames,tsyn)
	    val (thy',typedef_info) = TypedefPackage.add_typedef_i false (Some thmname) typ c (Some(rep_name,abs_name)) (rtac th2 1) thy
				      
	    val th3 = (#type_definition typedef_info) RS typedef_hol2hollight

	    val th4 = Drule.freeze_all th3
	    val fulltyname = Sign.intern_tycon (sign_of thy') tycname
	    val thy'' = add_hol4_type_mapping thyname tycname true fulltyname thy'

	    val sg = sign_of thy''
	    val (hth' as HOLThm args) = norm_hthm sg (HOLThm(rens,th4))
	    val _ = if #maxidx (rep_thm th4) <> ~1
		    then (Library.setmp show_types true pth hth' ; error "SCHEME!")
		    else ()
	    val _ = if has_ren hth' then warning ("Theorem " ^ thmname ^ " needs variable-disambiguating")
		    else ()
	    val thy4 = add_hol4_pending thyname thmname args thy''

	    val sg = sign_of thy4
	    val P' = #2 (Logic.dest_equals (concl_of (rewrite_hol4_term P thy4)))
	    val c   =
		let
		    val PT = type_of P'
		in
		    Const("Collect",PT-->HOLogic.mk_setT (domain_type PT)) $ P'
		end

	    val tnames_string = if null tnames
				then ""
				else "(" ^ (commafy tnames) ^ ") "
	    val proc_prop = if null tnames
			    then smart_string_of_cterm
			    else Library.setmp show_all_types true smart_string_of_cterm
	    val thy5 = add_dump ("typedef (open) " ^ tnames_string ^ (quotename tycname) ^ " = " ^ (proc_prop (cterm_of sg c)) ^ " " ^ (Syntax.string_of_mixfix tsyn) ^ "\n  by (rule light_ex_imp_nonempty,import " ^ thyname ^ " " ^ thmname ^ ")") thy4
	    val thy6 = add_dump ("lemmas " ^ thmname ^ " = typedef_hol2hollight [OF type_definition_" ^ tycname ^ "]")
		       thy5
	    val _ = message "RESULT:"
	    val _ = if_debug pth hth'
	in
	    (thy6,hth')
	end
	handle e => (message "exception in type_introduction"; print_exn e)
end

end
