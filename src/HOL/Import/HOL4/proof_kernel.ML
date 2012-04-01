(*  Title:      HOL/Import/proof_kernel.ML
    Author:     Sebastian Skalberg and Steven Obua, TU Muenchen
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
    val disambiguate_frees : Thm.thm -> Thm.thm
    val debug : bool Unsynchronized.ref
    val disk_info_of : proof -> (string * string) option
    val set_disk_info_of : proof -> string -> string -> unit
    val mk_proof : proof_content -> proof
    val content_of : proof -> proof_content
    val import_proof : string -> string -> theory -> (theory -> term) option * (theory -> proof)

    val rewrite_importer_term: Term.term -> theory -> Thm.thm

    val type_of : term -> hol_type

    val get_thm  : string -> string         -> theory -> (theory * thm option)
    val get_def  : string -> string -> term -> theory -> (theory * thm option)
    val get_axiom: string -> string         -> theory -> (theory * thm option)

    val store_thm : string -> string -> thm -> theory -> theory * thm

    val to_isa_thm : thm -> (term * term) list * Thm.thm
    val to_isa_term: term -> Term.term
    val to_hol_thm : Thm.thm -> thm

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

    val prin : term -> unit
    val protect_factname : string -> string
    val replay_protect_varname : string -> string -> unit
    val replay_add_dump : string -> theory -> theory
end

structure ProofKernel : ProofKernel =
struct
type hol_type = Term.typ
type term = Term.term
datatype tag = Tag of string list
type ('a,'b) subst = ('a * 'b) list
datatype thm = HOLThm of (Term.term * Term.term) list * Thm.thm

fun hthm2thm (HOLThm (_, th)) = th

fun to_hol_thm th = HOLThm ([], th)

val replay_add_dump = add_dump
fun add_dump s thy = replay_add_dump s thy

datatype proof_info
  = Info of {disk_info: (string * string) option Unsynchronized.ref}

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


(* Compatibility. *)

val string_of_mixfix = Pretty.string_of o Mixfix.pretty_mixfix;

fun mk_syn thy c =
  if Lexicon.is_identifier c andalso not (Syntax.is_keyword (Sign.syn_of thy) c) then NoSyn
  else Delimfix (Syntax_Ext.escape c)

fun quotename c =
  if Lexicon.is_identifier c andalso not (Keyword.is_keyword c) then c else quote c

exception SMART_STRING

fun no_vars context tm =
  let
    val ctxt = Variable.set_body false context;
    val ([tm'], _) = Variable.import_terms true [tm] ctxt;
  in tm' end

fun smart_string_of_cterm ctxt0 ct =
    let
        val ctxt = ctxt0
          |> Config.put show_brackets false
          |> Config.put show_all_types false
          |> Config.put show_types false
          |> Config.put show_sorts false;
        val {t,T,...} = rep_cterm ct
        (* Hack to avoid parse errors with Trueprop *)
        val t' = HOLogic.dest_Trueprop t
                 handle TERM _ => t
        val tn = no_vars ctxt t'
        fun match u =
            let val _ = Thm.match (ct, cterm_of (Proof_Context.theory_of ctxt) u) in true end
            handle Pattern.MATCH => false
        fun G 0 f ctxt x = f ctxt x
          | G 1 f ctxt x = f (Config.put show_types true ctxt) x
          | G 2 f ctxt x = G 1 f (Config.put show_sorts true ctxt) x
          | G 3 f ctxt x = G 2 f (Config.put show_all_types true ctxt) x
          | G 4 f ctxt x = G 3 f (Config.put show_brackets true ctxt) x
          | G _ _ _ _ = raise SMART_STRING
        fun F n =
            let
                val str = G n Syntax.string_of_term ctxt tn
                val _ = warning (@{make_string} (n, str))
                val u = Syntax.parse_term ctxt str
                val u = if t = t' then u else HOLogic.mk_Trueprop u
                val u = Syntax.check_term ctxt (Type.constraint T u)
            in
                if match u
                then quote str
                else F (n+1)
            end
            handle ERROR _ => F (n + 1)
              | SMART_STRING =>
                  let val _ =
                    warning ("smart_string failed for: "^ G 0 Syntax.string_of_term ctxt (term_of ct))
                  in quote (G 2 Syntax.string_of_term ctxt tn) end
    in
      Print_Mode.setmp [] F 0
    end

fun smart_string_of_thm ctxt = smart_string_of_cterm ctxt o cprop_of

fun prth th = writeln (Print_Mode.setmp [] Display.string_of_thm_without_context th);
val topctxt = ML_Context.the_local_context ();
fun prin t = writeln (Print_Mode.setmp []
  (fn () => Syntax.string_of_term topctxt t) ());
fun pth (HOLThm(_,thm)) =
    let
        (*val _ = writeln "Renaming:"
        val _ = app (fn(v,w) => (prin v; writeln " -->"; prin w)) ren*)
        val _ = prth thm
    in
        ()
    end

fun disk_info_of (Proof(Info{disk_info,...},_)) = !disk_info
fun mk_proof p = Proof(Info{disk_info = Unsynchronized.ref NONE},p)
fun content_of (Proof(_,p)) = p

fun set_disk_info_of (Proof(Info{disk_info,...},_)) thyname thmname =
    disk_info := SOME(thyname,thmname)

structure Lib =
struct

fun assoc x =
    let
        fun F [] = raise PK("Lib.assoc","Not found")
          | F ((x',y)::rest) = if x = x'
                               then y
                               else F rest
    in
        F
    end
infix mem;
fun i mem L =
    let fun itr [] = false
          | itr (a::rst) = i=a orelse itr rst
    in itr L end;

infix union;
fun [] union S = S
  | S union [] = S
  | (a::rst) union S2 = rst union (insert (op =) a S2);

fun implode_subst [] = []
  | implode_subst (x::r::rest) = ((x,r)::(implode_subst rest))
  | implode_subst _ = raise ERR "implode_subst" "malformed substitution list"

end
open Lib

structure Tag =
struct
val empty_tag = Tag []
fun read name = Tag [name]
fun merge (Tag tag1) (Tag tag2) = Tag (Lib.union(tag1,tag2))
end

(* Actual code. *)

fun get_segment thyname l = (Lib.assoc "s" l
                             handle PK _ => thyname)
val get_name : (string * string) list -> string = Lib.assoc "n"

exception XML of string

datatype xml = Elem of string * (string * string) list * xml list
datatype XMLtype = XMLty of xml | FullType of hol_type
datatype XMLterm = XMLtm of xml | FullTerm of term

fun xml_to_import_xml (XML.Elem ((n, l), ts)) = Elem (n, l, map xml_to_import_xml ts)
  | xml_to_import_xml (XML.Text _) = raise XML "Incorrect proof file: text";

val type_of = Term.type_of

val propT = Type("prop",[])

fun mk_defeq name rhs thy =
    let
        val ty = type_of rhs
    in
        Logic.mk_equals (Const(Sign.intern_const thy name,ty),rhs)
    end

fun mk_teq name rhs thy =
    let
        val ty = type_of rhs
    in
        HOLogic.mk_eq (Const(Sign.intern_const thy name,ty),rhs)
    end

fun intern_const_name thyname const thy =
    case get_importer_const_mapping thyname const thy of
        SOME (_,cname,_) => cname
      | NONE => (case get_importer_const_renaming thyname const thy of
                     SOME cname => Sign.intern_const thy (thyname ^ "." ^ cname)
                   | NONE => Sign.intern_const thy (thyname ^ "." ^ const))

fun intern_type_name thyname const thy =
    case get_importer_type_mapping thyname const thy of
        SOME (_,cname) => cname
      | NONE => Sign.intern_const thy (thyname ^ "." ^ const)

fun mk_vartype name = TFree(name,["HOL.type"])
fun mk_thy_type thy Thy Tyop Args = Type(intern_type_name Thy Tyop thy,Args)

val mk_var = Free

fun mk_thy_const thy Thy Nam Ty = Const(intern_const_name Thy Nam thy,Ty)

local
  fun get_const sg _ name =
    (case Sign.const_type sg name of
      SOME ty => Const (name, ty)
    | NONE => raise ERR "get_type" (name ^ ": No such constant"))
in
fun prim_mk_const thy Thy Nam =
    let
      val name = intern_const_name Thy Nam thy
      val cmaps = Importer_ConstMaps.get thy
    in
      case StringPair.lookup cmaps (Thy,Nam) of
        SOME(_,_,SOME ty) => Const(name,ty)
      | _ => get_const thy Thy name
    end
end

fun mk_comb(f,a) = f $ a

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

val protected_varnames = Unsynchronized.ref (Symtab.empty:string Symtab.table)
val invented_isavar = Unsynchronized.ref 0

fun innocent_varname s = Lexicon.is_identifier s andalso not (String.isPrefix "u_" s)

fun valid_boundvarname s =
  can (fn () => Syntax.read_term_global @{theory Main} ("SOME "^s^". True")) ();

fun valid_varname s =
  can (fn () => Syntax.read_term_global @{theory Main} s) ();

fun protect_varname s =
    if innocent_varname s andalso valid_varname s then s else
    case Symtab.lookup (!protected_varnames) s of
      SOME t => t
    | NONE =>
      let
          val _ = Unsynchronized.inc invented_isavar
          val t = "u_" ^ string_of_int (!invented_isavar)
          val _ = protected_varnames := Symtab.update (s, t) (!protected_varnames)
      in
          t
      end

exception REPLAY_PROTECT_VARNAME of string*string*string

fun replay_protect_varname s t =
        case Symtab.lookup (!protected_varnames) s of
          SOME t' => raise REPLAY_PROTECT_VARNAME (s, t, t')
        | NONE =>
          let
              val _ = Unsynchronized.inc invented_isavar
              val t = "u_" ^ string_of_int (!invented_isavar)
              val _ = protected_varnames := Symtab.update (s, t) (!protected_varnames)
          in
              ()
          end

fun protect_boundvarname s = if innocent_varname s andalso valid_boundvarname s then s else "u"

fun mk_lambda (v as Free (x, T)) t = Abs (protect_boundvarname x, T, abstract_over (v, t))
  | mk_lambda (v as Var ((x, _), T)) t = Abs (protect_boundvarname x, T, abstract_over (v, t))
  | mk_lambda v t = raise TERM ("lambda", [v, t]);

fun replacestr x y s =
let
  val xl = raw_explode x
  val yl = raw_explode y
  fun isprefix [] _ = true
    | isprefix (x::xs) (y::ys) = if x = y then isprefix xs ys else false
    | isprefix _ _ = false
  fun isp s = isprefix xl s
  fun chg s = yl@(List.drop (s, List.length xl))
  fun r [] = []
    | r (S as (s::ss)) = if isp S then r (chg S) else s::(r ss)
in
  implode(r (raw_explode s))
end

fun protect_factname s = replacestr "." "_dot_" s
fun unprotect_factname s = replacestr "_dot_" "." s

val ty_num_prefix = "N_"

fun startsWithDigit s = Char.isDigit (hd (String.explode s))

fun protect_tyname tyn =
  let
    val tyn' =
      if String.isPrefix ty_num_prefix tyn then raise (ERR "protect_ty_name" ("type name '"^tyn^"' is reserved")) else
      (if startsWithDigit tyn then ty_num_prefix^tyn else tyn)
  in
    tyn'
  end

fun protect_constname tcn = tcn
 (* if tcn = ".." then "dotdot"
  else if tcn = "==" then "eqeq"
  else tcn*)

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
                        (protect_tyname (get_name atts))
                        []
          | gtfx (Elem("tyv",[("n",s)],[])) = mk_vartype (protect_tyvarname s)
          | gtfx (Elem("tya",[],(Elem("tyc",atts,[]))::tys)) =
            mk_thy_type thy
                        (get_segment thyname atts)
                        (protect_tyname (get_name atts))
                        (map gtfx tys)
          | gtfx _ = raise ERR "get_type" "Bad type"
    in
        gtfx
    end

fun input_types _ (Elem("tylist",[("i",i)],xtys)) =
    let
        val types = Array.array(the (Int.fromString i),XMLty (Elem("",[],[])))
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
        fun gtfx (Elem("tmv",[("n",name),("t",tyi)],[])) =
            mk_var(protect_varname name,TypeNet.get_type_from_index thy thyname types tyi)
          | gtfx (Elem("tmc",atts,[])) =
            let
                val segment = get_segment thyname atts
                val name = protect_constname(get_name atts)
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
                mk_lambda x a
            end
          | gtfx (Elem("tmi",[("i",iS)],[])) =
            get_term_from_index thy thyname types terms iS
          | gtfx (Elem(tag,_,_)) =
            raise ERR "get_term" ("Not a term: "^tag)
    in
        gtfx
    end

fun input_terms _ _ (Elem("tmlist",[("i",i)],xtms)) =
    let
        val terms = Array.array(the (Int.fromString i), XMLtm (Elem("",[],[])))

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
                SOME seg => seg
              | NONE => get_import_segment thy
        val path = space_explode ":" (getenv "IMPORTER_PROOFS")
        fun find [] = NONE
          | find (p::ps) =
            (let
                 val dir = OS.Path.joinDirFile {dir = p,file=import_segment}
             in
                 if OS.FileSys.isDir dir
                 then SOME dir
                 else find ps
             end) handle OS.SysErr _ => find ps
    in
        Option.map (fn p => OS.Path.joinDirFile {dir = p, file = thyname}) (find path)
    end

fun proof_file_name thyname thmname thy =
    let
        val path = case get_proof_dir thyname thy of
                       SOME p => p
                     | NONE => error "Cannot find proof files"
        val _ = OS.FileSys.mkDir path handle OS.SysErr _ => ()
    in
        OS.Path.joinDirFile {dir = path, file = OS.Path.joinBaseExt {base = (unprotect_factname thmname), ext = SOME "prf"}}
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
                val thmname = protect_factname (get_name atts)
                val p = mk_proof PDisk
                val _  = set_disk_info_of p thyname thmname
            in
                p
            end
          | x2p (Elem("pdef",[("s",seg),("n",name),("i",is)],[])) =
            mk_proof (PDef(seg,protect_constname name,index_to_term is))
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
                mk_proof (PTyIntro(seg,protect_tyname name,protect_constname abs_name,protect_constname rep_name,P,t,x2p p))
            end
          | x2p (Elem("ptydef",[("s",seg),("n",name)],[p])) =
            mk_proof (PTyDef(seg,protect_tyname name,x2p p))
          | x2p (Elem("poracle",[],chldr)) =
            let
                val (oracles,terms) = List.partition (fn (Elem("oracle",_,_)) => true | _ => false) chldr
                val ors = map (fn (Elem("oracle",[("n",name)],[])) => name | _ => raise ERR "x2p" "bad oracle") oracles
                val (c,asl) = case terms of
                                  [] => raise ERR "x2p" "Bad oracle description"
                                | (hd::tl) => (hd,tl)
                val tg = fold_rev (Tag.merge o Tag.read) ors Tag.empty_tag
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
                mk_proof (PGenAbs(p,NONE,tml))
            end
          | x2p (Elem("pgenabs",[("i",is)],prf::tms)) =
            let
                val p = x2p prf
                val tml = map xml_to_term tms
            in
                mk_proof (PGenAbs(p,SOME (index_to_term is),tml))
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
          | x2p _ = raise ERR "x2p" "Bad proof"
    in
        x2p prf
    end

fun import_proof_concl thyname thmname thy =
    let
        val is = TextIO.openIn(proof_file_name thyname thmname thy)
        val proof_xml = xml_to_import_xml (XML.parse (TextIO.inputAll is))
        val _ = TextIO.closeIn is
    in
        case proof_xml of
            Elem("proof",[],xtypes::xterms::_::rest) =>
            let
                val types = TypeNet.input_types thyname xtypes
                val terms = TermNet.input_terms thyname types xterms
                fun f xtm thy = TermNet.get_term_from_xml thy thyname types terms xtm
            in
                case rest of
                    [] => NONE
                  | [xtm] => SOME (f xtm)
                  | _ => raise ERR "import_proof" "Bad argument list"
            end
          | _ => raise ERR "import_proof" "Bad proof"
    end

fun import_proof thyname thmname thy =
    let
        val is = TextIO.openIn(proof_file_name thyname thmname thy)
        val proof_xml = xml_to_import_xml (XML.parse (TextIO.inputAll is))
        val _ = TextIO.closeIn is
    in
        case proof_xml of
            Elem("proof",[],xtypes::xterms::prf::rest) =>
            let
                val types = TypeNet.input_types thyname xtypes
                val terms = TermNet.input_terms thyname types xterms
            in
                (case rest of
                     [] => NONE
                   | [xtm] => SOME (fn thy => TermNet.get_term_from_xml thy thyname types terms xtm)
                   | _ => raise ERR "import_proof" "Bad argument list",
                 xml_to_proof thyname types terms prf)
            end
          | _ => raise ERR "import_proof" "Bad proof"
    end

fun uniq_compose m th i st =
    let
        val res = Thm.bicompose false (false,th,m) i st
    in
        case Seq.pull res of
            SOME (th,rest) => (case Seq.pull rest of
                                   SOME _ => raise ERR "uniq_compose" "Not unique!"
                                 | NONE => th)
          | NONE => raise ERR "uniq_compose" "No result"
    end

val reflexivity_thm = @{thm refl}
val mp_thm = @{thm mp}
val imp_antisym_thm = @{thm light_imp_as}
val disch_thm = @{thm impI}
val ccontr_thm = @{thm ccontr}

val meta_eq_to_obj_eq_thm = @{thm meta_eq_to_obj_eq}

val gen_thm = @{thm HOLallI}
val choose_thm = @{thm exE}
val exists_thm = @{thm exI}
val conj_thm = @{thm conjI}
val conjunct1_thm = @{thm conjunct1}
val conjunct2_thm = @{thm conjunct2}
val spec_thm = @{thm spec}
val disj_cases_thm = @{thm disjE}
val disj1_thm = @{thm disjI1}
val disj2_thm = @{thm disjI2}

local
    val th = @{thm not_def}
    val thy = theory_of_thm th
    val pp = Thm.reflexive (cterm_of thy (Const(@{const_name Trueprop},HOLogic.boolT-->propT)))
in
val not_elim_thm = Thm.combination pp th
end

val not_intro_thm = Thm.symmetric not_elim_thm
val abs_thm = @{thm ext}
val trans_thm = @{thm trans}
val symmetry_thm = @{thm sym}
val eqmp_thm = @{thm iffD1}
val eqimp_thm = @{thm Importer.eq_imp}
val comb_thm = @{thm cong}

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
    Library.foldl (fn (th,p) => Thm.implies_elim th (Thm.assume p)) (th,cprems_of th)

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
        val th2 = beta_eta_thm (Thm.forall_intr cv th1)
        val th3 = th2 COMP (beta_eta_thm (Drule.instantiate' [SOME cvty] [SOME clc] gen_thm))
        val c = prop_of th3
        val vname = fst(dest_Free v)
        val (cold,cnew) = case c of
                              tpc $ (Const(@{const_name All},_) $ Abs(oldname,_,_)) =>
                              (Abs(oldname,dummyT,Bound 0),Abs(vname,dummyT,Bound 0))
                            | tpc $ (Const(@{const_name All},_) $ _) => (tpc,tpc)
                            | _ => raise ERR "mk_GEN" "Unknown conclusion"
        val th4 = Thm.rename_boundvars cold cnew th3
        val res = implies_intr_hyps th4
    in
        res
    end

fun rearrange sg tm th =
    let
        val tm' = Envir.beta_eta_contract tm
        fun find []      n = Thm.permute_prems 0 1 (Thm.implies_intr (Thm.cterm_of sg tm) th)
          | find (p::ps) n = if tm' aconv (Envir.beta_eta_contract p)
                             then Thm.permute_prems n 1 th
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

(* Code for disambiguating variablenames (wrt. types) *)

val disamb_info_empty = {vars=[],rens=[]}

fun rens_of { vars = _, rens = rens } = rens

fun disamb_term_from info tm = (info, tm)

fun has_ren (HOLThm _) = false

fun disamb_thm_from info (HOLThm (_,thm)) = (info, thm)

fun disamb_terms_from info tms = (info, tms)

fun disamb_thms_from info hthms = (info, map hthm2thm hthms)

fun disamb_term tm   = disamb_term_from disamb_info_empty tm
fun disamb_thm thm   = disamb_thm_from disamb_info_empty thm
fun disamb_thms thms = disamb_thms_from disamb_info_empty thms

fun norm_hthm _ (hth as HOLThm _) = hth

(* End of disambiguating code *)

fun disambiguate_frees thm =
    let
      fun ERR s = error ("Drule.disambiguate_frees: "^s)
      val ct = cprop_of thm
      val t = term_of ct
      val thy = theory_of_cterm ct
      val frees = Misc_Legacy.term_frees t
      val freenames = Term.add_free_names t []
      val is_old_name = member (op =) freenames
      fun name_of (Free (n, _)) = n
        | name_of _ = ERR "name_of"
      fun new_name' bump map n =
          let val n' = n^bump in
            if is_old_name n' orelse Symtab.lookup map n' <> NONE then
              new_name' (Symbol.bump_string bump) map n
            else
              n'
          end
      val new_name = new_name' "a"
      fun replace_name n' (Free (_, t)) = Free (n', t)
        | replace_name _ _ = ERR "replace_name"
      (* map: old or fresh name -> old free,
         invmap: old free which has fresh name assigned to it -> fresh name *)
      fun dis v (mapping as (map,invmap)) =
          let val n = name_of v in
            case Symtab.lookup map n of
              NONE => (Symtab.update (n, v) map, invmap)
            | SOME v' =>
              if v=v' then
                mapping
              else
                let val n' = new_name map n in
                  (Symtab.update (n', v) map,
                   Termtab.update (v, n') invmap)
                end
          end
    in
      if (length freenames = length frees) then
        thm
      else
        let
          val (_, invmap) =
              fold dis frees (Symtab.empty, Termtab.empty)
          fun make_subst (oldfree, newname) (intros, elims) =
              (cterm_of thy oldfree :: intros,
               cterm_of thy (replace_name newname oldfree) :: elims)
          val (intros, elims) = fold make_subst (Termtab.dest invmap) ([], [])
        in
          forall_elim_list elims (forall_intr_list intros thm)
        end
    end

val debug = Unsynchronized.ref false

fun if_debug f x = if !debug then f x else ()
val message = if_debug writeln

fun get_importer_thm thyname thmname thy =
    case get_importer_theorem thyname thmname thy of
        SOME hth => SOME (HOLThm hth)
      | NONE =>
        let
            val pending = Importer_Pending.get thy
        in
            case StringPair.lookup pending (thyname,thmname) of
                SOME hth => SOME (HOLThm hth)
              | NONE => NONE
        end

fun non_trivial_term_consts t = fold_aterms
  (fn Const (c, _) =>
      if c = @{const_name Trueprop} orelse c = @{const_name All}
        orelse c = @{const_name HOL.implies} orelse c = @{const_name HOL.conj} orelse c = @{const_name HOL.eq}
      then I else insert (op =) c
    | _ => I) t [];

fun split_name str =
    let
        val sub = Substring.full str
        val (f,idx) = apsnd Substring.string (Substring.splitr Char.isDigit sub)
        val (newstr,u) = pairself Substring.string (Substring.splitr (fn c => c = #"_") f)
    in
        if not (idx = "") andalso u = "_"
        then SOME (newstr, the (Int.fromString idx))
        else NONE
    end
    handle _ => NONE  (* FIXME avoid handle _ *)

fun rewrite_importer_term t thy =
    let
        val import_rews1 = map (Thm.transfer thy) (Importer_Rewrites.get thy)
        val importerss = Simplifier.global_context thy empty_ss addsimps import_rews1
    in
        Thm.transfer thy (Simplifier.full_rewrite importerss (cterm_of thy t))
    end

fun get_isabelle_thm thyname thmname importerconc thy =
    let
        val (info,importerconc') = disamb_term importerconc
        val i2h_conc = Thm.symmetric (rewrite_importer_term (HOLogic.mk_Trueprop importerconc') thy)
        val isaconc =
            case concl_of i2h_conc of
                Const("==",_) $ lhs $ _ => lhs
              | _ => error "get_isabelle_thm" "Bad rewrite rule"
        val _ = (message "Original conclusion:";
                 if_debug prin importerconc';
                 message "Modified conclusion:";
                 if_debug prin isaconc)

        fun mk_res th = HOLThm (rens_of info, Thm.equal_elim i2h_conc th)
    in
        case get_importer_mapping thyname thmname thy of
            SOME (SOME thmname) =>
            let
                val th1 = (SOME (Global_Theory.get_thm thy thmname)
                           handle ERROR _ =>
                                  (case split_name thmname of
                                       SOME (listname,idx) => (SOME (nth (Global_Theory.get_thms thy listname) (idx - 1))
                                                               handle _ => NONE)  (* FIXME avoid handle _ *)
                                     | NONE => NONE))
            in
                case th1 of
                    SOME th2 =>
                    (case Shuffler.set_prop thy isaconc [(thmname,th2)] of
                         SOME (_,th) => (message "YES";(thy, SOME (mk_res th)))
                       | NONE => (message "NO2";error "get_isabelle_thm" "Bad mapping"))
                  | NONE => (message "NO1";error "get_isabelle_thm" "Bad mapping")
            end
          | SOME NONE => error ("Trying to access ignored theorem " ^ thmname)
          | NONE =>
            let
                val _ = (message "Looking for conclusion:";
                         if_debug prin isaconc)
                val cs = non_trivial_term_consts isaconc;
                val _ = (message "Looking for consts:";
                         message (commas cs))
                val pot_thms = Shuffler.find_potential thy isaconc
                val _ = message (string_of_int (length pot_thms) ^ " potential theorems")
            in
                case Shuffler.set_prop thy isaconc pot_thms of
                    SOME (isaname,th) =>
                    let
                        val hth as HOLThm args = mk_res th
                        val thy' =  thy |> add_importer_theorem thyname thmname args
                                        |> add_importer_mapping thyname thmname isaname
                    in
                        (thy',SOME hth)
                    end
                  | NONE => (thy,NONE)
            end
    end
    handle e =>
      if Exn.is_interrupt e then reraise e
      else
        (if_debug (fn () =>
            writeln ("Exception in get_isabelle_thm:\n" ^ ML_Compiler.exn_message e)) ();
          (thy,NONE))

fun get_isabelle_thm_and_warn thyname thmname importerconc thy =
  let
    val (a, b) = get_isabelle_thm thyname thmname importerconc thy
    fun warn () =
        let
            val (_,importerconc') = disamb_term importerconc
            val i2h_conc = Thm.symmetric (rewrite_importer_term (HOLogic.mk_Trueprop importerconc') thy)
        in
            case concl_of i2h_conc of
                Const("==",_) $ lhs $ _ =>
                (warning ("Failed lookup of theorem '"^thmname^"':");
                 writeln "Original conclusion:";
                 prin importerconc';
                 writeln "Modified conclusion:";
                 prin lhs)
              | _ => ()
        end
  in
      case b of
          NONE => (warn () handle _ => (); (a,b)) (* FIXME avoid handle _ *)
        | _ => (a, b)
  end

fun get_thm thyname thmname thy =
    case get_importer_thm thyname thmname thy of
        SOME hth => (thy,SOME hth)
      | NONE => ((case import_proof_concl thyname thmname thy of
                      SOME f => get_isabelle_thm_and_warn thyname thmname (f thy) thy
                    | NONE => (message "No conclusion"; (thy,NONE)))
                 handle IO.Io _ => (message "IO exception"; (thy,NONE))
                      | PK _ => (message "PK exception"; (thy,NONE)))

fun rename_const thyname thy name =
    case get_importer_const_renaming thyname name thy of
        SOME cname => cname
      | NONE => name

fun get_def thyname constname rhs thy =
    let
        val constname = rename_const thyname thy constname
        val (thmname,thy') = get_defname thyname constname thy
        val _ = message ("Looking for definition " ^ thyname ^ "." ^ thmname)
    in
        get_isabelle_thm_and_warn thyname thmname (mk_teq (thyname ^ "." ^ constname) rhs thy') thy'
    end

fun get_axiom thyname axname thy =
    case get_thm thyname axname thy of
        arg as (_,SOME _) => arg
      | _ => raise ERR "get_axiom" ("Trying to retrieve axiom (" ^ axname ^ ")")

fun intern_store_thm gen_output thyname thmname hth thy =
    let
        val (hth' as HOLThm (args as (_,th))) = norm_hthm thy hth
        val rew = rewrite_importer_term (concl_of th) thy
        val th  = Thm.equal_elim rew th
        val thy' = add_importer_pending thyname thmname args thy
        val th = disambiguate_frees th
        val th = Object_Logic.rulify th
        val thy2 =
          if gen_output
          then
            add_dump ("lemma " ^ (quotename thmname) ^ ": " ^
                (smart_string_of_thm (Syntax.init_pretty_global thy') th) ^ "\n  by (import " ^
                thyname ^ " " ^ (quotename thmname) ^ ")") thy'
          else thy'
    in
        (thy2,hth')
    end

val store_thm = intern_store_thm true

fun mk_REFL ctm =
    let
        val cty = Thm.ctyp_of_term ctm
    in
        Drule.instantiate' [SOME cty] [SOME ctm] reflexivity_thm
    end

fun REFL tm thy =
    let
        val _ = message "REFL:"
        val (info,tm') = disamb_term tm
        val ctm = Thm.cterm_of thy tm'
        val res = HOLThm(rens_of info,mk_REFL ctm)
        val _ = if_debug pth res
    in
        (thy,res)
    end

fun ASSUME tm thy =
    let
        val _ = message "ASSUME:"
        val (info,tm') = disamb_term tm
        val ctm = Thm.cterm_of thy (HOLogic.mk_Trueprop tm')
        val th = Thm.trivial ctm
        val res = HOLThm(rens_of info,th)
        val _ = if_debug pth res
    in
        (thy,res)
    end

fun INST_TYPE lambda (hth as HOLThm(_,th)) thy =
    let
        val _ = message "INST_TYPE:"
        val _ = if_debug pth hth
        val tys_before = Misc_Legacy.add_term_tfrees (prop_of th,[])
        val th1 = Thm.varifyT_global th
        val tys_after = Misc_Legacy.add_term_tvars (prop_of th1,[])
        val tyinst = map (fn (bef, iS) =>
                             (case try (Lib.assoc (TFree bef)) lambda of
                                  SOME ty => (ctyp_of thy (TVar iS), ctyp_of thy ty)
                                | NONE => (ctyp_of thy (TVar iS), ctyp_of thy (TFree bef))
                             ))
                         (zip tys_before tys_after)
        val res = Drule.instantiate_normalize (tyinst,[]) th1
        val hth = HOLThm([],res)
        val res = norm_hthm thy hth
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
        val (sdom,srng) = ListPair.unzip (rev sigma)
        val th = hthm2thm hth
        val th1 = mk_INST (map (cterm_of thy) sdom) (map (cterm_of thy) srng) th
        val res = HOLThm([],th1)
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

fun mk_EQ_MP th1 th2 = [beta_eta_thm th1, beta_eta_thm th2] MRS eqmp_thm

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

fun mk_COMB th1 th2 thy =
    let
        val (f,g) = case concl_of th1 of
                        _ $ (Const(@{const_name HOL.eq},_) $ f $ g) => (f,g)
                      | _ => raise ERR "mk_COMB" "First theorem not an equality"
        val (x,y) = case concl_of th2 of
                        _ $ (Const(@{const_name HOL.eq},_) $ x $ y) => (x,y)
                      | _ => raise ERR "mk_COMB" "Second theorem not an equality"
        val fty = type_of f
        val (fd,fr) = Term.dest_funT fty
        val comb_thm' = Drule.instantiate'
                            [SOME (ctyp_of thy fd),SOME (ctyp_of thy fr)]
                            [SOME (cterm_of thy f),SOME (cterm_of thy g),
                             SOME (cterm_of thy x),SOME (cterm_of thy y)] comb_thm
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

        val cctxt = cterm_of thy ctxt'
        fun subst th [] = th
          | subst th (rew::rews) = subst (mk_COMB th rew thy) rews
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
        val th1 = norm_hyps th1
        val th2 = norm_hyps th2
        val (l,r) = case concl_of th of
                        _ $ (Const(@{const_name HOL.disj},_) $ l $ r) => (l,r)
                      | _ => raise ERR "DISJ_CASES" "Conclusion not a disjunction"
        val th1' = rearrange thy (HOLogic.mk_Trueprop l) th1
        val th2' = rearrange thy (HOLogic.mk_Trueprop r) th2
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
        val ct = Thm.cterm_of thy tm'
        val disj1_thm' = Drule.instantiate' [] [NONE,SOME ct] disj1_thm
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
        val ct = Thm.cterm_of thy tm'
        val disj2_thm' = Drule.instantiate' [] [NONE,SOME ct] disj2_thm
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
        val cwit = cterm_of thy wit'
        val cty = ctyp_of_term cwit
        val a = case ex' of
                    (Const(@{const_name Ex},_) $ a) => a
                  | _ => raise ERR "EXISTS" "Argument not existential"
        val ca = cterm_of thy a
        val exists_thm' = beta_eta_thm (Drule.instantiate' [SOME cty] [SOME ca,SOME cwit] exists_thm)
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
            strip (n-1) ps (Thm.implies_elim th (Thm.assume p))
          | strip _ _ _ = raise ERR "CHOOSE" "strip error"
        val cv = cterm_of thy v'
        val th2 = norm_hyps th2
        val cvty = ctyp_of_term cv
        val c = HOLogic.dest_Trueprop (concl_of th2)
        val cc = cterm_of thy c
        val a = case concl_of th1 of
                    _ $ (Const(@{const_name Ex},_) $ a) => a
                  | _ => raise ERR "CHOOSE" "Conclusion not existential"
        val ca = cterm_of (theory_of_thm th1) a
        val choose_thm' = beta_eta_thm (Drule.instantiate' [SOME cvty] [SOME ca,SOME cc] choose_thm)
        val th21 = rearrange thy (HOLogic.mk_Trueprop (a $ v')) th2
        val th22 = strip ((nprems_of th21)-1) (cprems_of th21) th21
        val th23 = beta_eta_thm (Thm.forall_intr cv th22)
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
        val res = HOLThm(rens_of info',mk_GEN v' th thy)
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
        val ctm = Thm.cterm_of thy tm'
        val cty = Thm.ctyp_of_term ctm
        val spec' = Drule.instantiate' [SOME cty] [NONE,SOME ctm] spec_thm
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
        val res = HOLThm(rens_of info,mk_COMB th1 th2 thy)
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
        val ct = cterm_of thy tm'
        val th1 = rearrange thy (HOLogic.mk_Trueprop (Const(@{const_name Not},HOLogic.boolT-->HOLogic.boolT) $ tm')) th
        val ccontr_thm' = Drule.instantiate' [] [SOME ct] ccontr_thm
        val res1 = uniq_compose ((nprems_of th1) - 1) th1 1 ccontr_thm'
        val res = HOLThm(rens_of info',res1)
        val _ = message "RESULT:"
        val _ = if_debug pth res
    in
        (thy,res)
    end

fun mk_ABS v th thy =
    let
        val cv = cterm_of thy v
        val th1 = implies_elim_all (beta_eta_thm th)
        val (f,g) = case concl_of th1 of
                        _ $ (Const(@{const_name HOL.eq},_) $ f $ g) => (Term.lambda v f,Term.lambda v g)
                      | _ => raise ERR "mk_ABS" "Bad conclusion"
        val (fd,fr) = Term.dest_funT (type_of f)
        val abs_thm' = Drule.instantiate' [SOME (ctyp_of thy fd), SOME (ctyp_of thy fr)] [SOME (cterm_of thy f), SOME (cterm_of thy g)] abs_thm
        val th2 = Thm.forall_intr cv th1
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
        val res = HOLThm(rens_of info',mk_ABS v' th thy)
        val _ = message "RESULT:"
        val _ = if_debug pth res
    in
        (thy,res)
    end

fun GEN_ABS copt vlist hth thy =
    let
        val _ = message "GEN_ABS:"
        val _ = case copt of
                    SOME c => if_debug prin c
                  | NONE => ()
        val _ = if_debug (app prin) vlist
        val _ = if_debug pth hth
        val (info,th) = disamb_thm hth
        val (info',vlist') = disamb_terms_from info vlist
        val th1 =
            case copt of
                SOME (Const(cname,cty)) =>
                let
                    fun inst_type ty1 ty2 (TVar _) = raise ERR "GEN_ABS" "Type variable found!"
                      | inst_type ty1 ty2 (ty as TFree _) = if ty1 = ty
                                                            then ty2
                                                            else ty
                      | inst_type ty1 ty2 (Type(name,tys)) =
                        Type(name,map (inst_type ty1 ty2) tys)
                in
                    fold_rev (fn v => fn th =>
                              let
                                  val cdom = fst (Term.dest_funT (fst (Term.dest_funT cty)))
                                  val vty  = type_of v
                                  val newcty = inst_type cdom vty cty
                                  val cc = cterm_of thy (Const(cname,newcty))
                              in
                                  mk_COMB (mk_REFL cc) (mk_ABS v th thy) thy
                              end) vlist' th
                end
              | SOME _ => raise ERR "GEN_ABS" "Bad constant"
              | NONE =>
                fold_rev (fn v => fn th => mk_ABS v th thy) vlist' th
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
        val th1 = implies_elim_all (beta_eta_thm th)
        val a = case concl_of th1 of
                    _ $ (Const(@{const_name HOL.implies},_) $ a $ Const(@{const_name False},_)) => a
                  | _ => raise ERR "NOT_INTRO" "Conclusion of bad form"
        val ca = cterm_of thy a
        val th2 = Thm.equal_elim (Drule.instantiate' [] [SOME ca] not_intro_thm) th1
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
        val th1 = implies_elim_all (beta_eta_thm th)
        val a = case concl_of th1 of
                    _ $ (Const(@{const_name Not},_) $ a) => a
                  | _ => raise ERR "NOT_ELIM" "Conclusion of bad form"
        val ca = cterm_of thy a
        val th2 = Thm.equal_elim (Drule.instantiate' [] [SOME ca] not_elim_thm) th1
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
        val th1 = beta_eta_thm th
        val th2 = implies_elim_all th1
        val th3 = Thm.implies_intr (cterm_of thy (HOLogic.mk_Trueprop tm')) th2
        val th4 = th3 COMP disch_thm
        val res = HOLThm (rens_of info', implies_intr_hyps th4)
        val _ = message "RESULT:"
        val _ = if_debug pth res
    in
        (thy,res)
    end

val spaces = space_implode " "

fun new_definition thyname constname rhs thy =
    let
        val constname = rename_const thyname thy constname
        val redeclared = is_some (Sign.const_type thy (Sign.intern_const thy constname));
        val _ = warning ("Introducing constant " ^ constname)
        val (thmname,thy) = get_defname thyname constname thy
        val (_,rhs') = disamb_term rhs
        val ctype = type_of rhs'
        val csyn = mk_syn thy constname
        val thy1 = case Importer_DefThy.get thy of
                       Replaying _ => thy
                     | _ => Sign.add_consts_i [(Binding.name constname,ctype,csyn)] thy
        val eq = mk_defeq constname rhs' thy1
        val (thms, thy2) = Global_Theory.add_defs false [((Binding.name thmname,eq),[])] thy1
        val def_thm = hd thms
        val thm' = def_thm RS meta_eq_to_obj_eq_thm
        val (thy',th) = (thy2, thm')
        val fullcname = Sign.intern_const thy' constname
        val thy'' = add_importer_const_mapping thyname constname true fullcname thy'
        val (linfo,tm24) = disamb_term (mk_teq constname rhs' thy'')
        val rew = rewrite_importer_term eq thy''
        val crhs = cterm_of thy'' (#2 (Logic.dest_equals (prop_of rew)))
        val thy22 =
          if Thm.def_name constname = thmname andalso not redeclared andalso csyn = NoSyn
          then
              let
                  val ctxt = Syntax.init_pretty_global thy''
                  val p1 = quotename constname
                  val p2 = Syntax.string_of_typ ctxt ctype
                  val p3 = string_of_mixfix csyn
                  val p4 = smart_string_of_cterm ctxt crhs
              in
                add_dump ("definition\n  " ^ p1 ^ " :: \"" ^ p2 ^ "\" "^ p3 ^ " where\n  " ^ p4) thy''
              end
          else
              let val ctxt = Syntax.init_pretty_global thy'' in
                add_dump ("consts\n  " ^ quotename constname ^ " :: \"" ^
                  Syntax.string_of_typ ctxt ctype ^
                  "\" " ^ string_of_mixfix csyn ^ "\n\ndefs\n  " ^
                  quotename thmname ^ ": " ^ smart_string_of_cterm ctxt crhs) thy''
              end
        val hth = case Shuffler.set_prop thy22 (HOLogic.mk_Trueprop tm24) [("",th)] of
                      SOME (_,res) => HOLThm(rens_of linfo,res)
                    | NONE => raise ERR "new_definition" "Bad conclusion"
        val fullname = Sign.full_bname thy22 thmname
        val thy22' = case opt_get_output_thy thy22 of
                         "" => add_importer_mapping thyname thmname fullname thy22
                       | output_thy =>
                         let
                             val moved_thmname = output_thy ^ "." ^ thyname ^ "." ^ thmname
                         in
                             thy22 |> add_importer_move fullname moved_thmname
                                   |> add_importer_mapping thyname thmname moved_thmname
                         end
        val _ = message "new_definition:"
        val _ = if_debug pth hth
    in
        (thy22',hth)
    end

fun new_specification thyname thmname names hth thy =
    case Importer_DefThy.get thy of
        Replaying _ => (thy,hth)
      | _ =>
        let
            val _ = message "NEW_SPEC:"
            val _ = if_debug pth hth
            val names = map (rename_const thyname thy) names
            val _ = warning ("Introducing constants " ^ commas names)
            val (HOLThm(rens,th)) = norm_hthm thy hth
            val thy1 = case Importer_DefThy.get thy of
                           Replaying _ => thy
                         | _ =>
                           let
                               fun dest_eta_abs (Abs(x,xT,body)) = (x,xT,body)
                                 | dest_eta_abs body =
                                   let
                                       val (dT,_) = Term.dest_funT (type_of body)
                                   in
                                       ("x",dT,body $ Bound 0)
                                   end
                                   handle TYPE _ => raise ERR "new_specification" "not an abstraction type"
                               fun dest_exists (Const(@{const_name Ex},_) $ abody) =
                                   dest_eta_abs abody
                                 | dest_exists _ =
                                   raise ERR "new_specification" "Bad existential formula"

                               val (consts,_) = Library.foldl (fn ((cs,ex),cname) =>
                                                          let
                                                              val (_,cT,p) = dest_exists ex
                                                          in
                                                              ((cname,cT,mk_syn thy cname)::cs,p)
                                                          end) (([],HOLogic.dest_Trueprop (concl_of th)),names)
                               val str = Library.foldl (fn (acc, (c, T, csyn)) =>
                                   acc ^ "\n  " ^ quotename c ^ " :: \"" ^
                                   Syntax.string_of_typ_global thy T ^ "\" " ^ string_of_mixfix csyn) ("consts", consts)
                               val thy' = add_dump str thy
                           in
                               Sign.add_consts_i (map (fn (c, T, mx) => (Binding.name c, T, mx)) consts) thy'
                           end

            val thy1 = fold_rev (fn name => fn thy =>
                                snd (get_defname thyname name thy)) names thy1
            fun new_name name = fst (get_defname thyname name thy1)
            val names' = map (fn name => (new_name name,name,false)) names
            val (thy',res) = Choice_Specification.add_specification NONE
                                 names'
                                 (thy1,th)
            val res' = Thm.unvarify_global res
            val hth = HOLThm(rens,res')
            val rew = rewrite_importer_term (concl_of res') thy'
            val th  = Thm.equal_elim rew res'
            fun handle_const (name,thy) =
                let
                    val defname = Thm.def_name name
                    val (newname,thy') = get_defname thyname name thy
                in
                    (if defname = newname
                     then quotename name
                     else (quotename newname) ^ ": " ^ (quotename name),thy')
                end
            val (new_names,thy') = fold_rev (fn name => fn (names, thy) =>
                                            let
                                                val (name',thy') = handle_const (name,thy)
                                            in
                                                (name'::names,thy')
                                            end) names ([], thy')
            val thy'' =
              add_dump ("specification (" ^ (spaces new_names) ^ ") " ^ thmname ^ ": " ^
                (smart_string_of_thm (Syntax.init_pretty_global thy') th) ^
                "\n  by (import " ^ thyname ^ " " ^ thmname ^ ")")
                thy'
            val _ = message "RESULT:"
            val _ = if_debug pth hth
        in
            intern_store_thm false thyname thmname hth thy''
        end

fun new_axiom name _ _ = raise ERR "new_axiom" ("Oh, no you don't! (" ^ name ^ ")")

fun to_isa_thm (hth as HOLThm(_,th)) =
    let
        val (HOLThm args) = norm_hthm (theory_of_thm th) hth
    in
        apsnd Thm.strip_shyps args
    end

fun to_isa_term tm = tm

local
    val light_nonempty = @{thm light_ex_imp_nonempty}
    val ex_imp_nonempty = @{thm ex_imp_nonempty}
    val typedef_hol2hol4 = @{thm typedef_hol2hol4}
    val typedef_hol2hollight = @{thm typedef_hol2hollight}
in
fun new_type_definition thyname thmname tycname hth thy =
    case Importer_DefThy.get thy of
        Replaying _ => (thy,hth)
      | _ =>
        let
            val _ = message "TYPE_DEF:"
            val _ = if_debug pth hth
            val _ = warning ("Introducing type " ^ tycname)
            val (HOLThm(rens,td_th)) = norm_hthm thy hth
            val th2 = beta_eta_thm (td_th RS ex_imp_nonempty)
            val c = case concl_of th2 of
                        _ $ (Const(@{const_name Ex},_) $ Abs(_,_,Const(@{const_name Set.member},_) $ _ $ c)) => c
                      | _ => raise ERR "new_type_definition" "Bad type definition theorem"
            val tfrees = Misc_Legacy.term_tfrees c
            val tnames = map fst tfrees
            val tsyn = mk_syn thy tycname
            val ((_, typedef_info), thy') =
              Typedef.add_typedef_global false (SOME (Binding.name thmname))
                (Binding.name tycname, map (rpair dummyS) tnames, tsyn) c NONE (rtac th2 1) thy

            val th3 = (#type_definition (#2 typedef_info)) RS typedef_hol2hol4

            val fulltyname = Sign.intern_type thy' tycname
            val thy'' = add_importer_type_mapping thyname tycname true fulltyname thy'

            val (hth' as HOLThm args) = norm_hthm thy'' (HOLThm(rens,th3))
            val _ = if has_ren hth' then warning ("Theorem " ^ thmname ^ " needs variable-disambiguating")
                    else ()
            val thy4 = add_importer_pending thyname thmname args thy''

            val rew = rewrite_importer_term (concl_of td_th) thy4
            val th  = Thm.equal_elim rew (Thm.transfer thy4 td_th)
            val c   = case HOLogic.dest_Trueprop (prop_of th) of
                          Const(@{const_name Ex},exT) $ P =>
                          let
                              val PT = domain_type exT
                          in
                              Const (@{const_name Collect},PT-->HOLogic.mk_setT (domain_type PT)) $ P
                          end
                        | _ => error "Internal error in ProofKernel.new_typedefinition"
            val tnames_string = if null tnames
                                then ""
                                else "(" ^ commas tnames ^ ") "
            val proc_prop =
              smart_string_of_cterm
                (Syntax.init_pretty_global thy4
                  |> not (null tnames) ? Config.put show_all_types true)
            val thy5 = add_dump ("typedef (open) " ^ tnames_string ^ (quotename tycname) ^ " = " ^ (proc_prop (cterm_of thy4 c)) ^ " "
                                 ^ (string_of_mixfix tsyn) ^ "\n  by (rule typedef_helper,import " ^ thyname ^ " " ^ thmname ^ ")") thy4

            val thy6 = add_dump ("lemmas " ^ thmname ^ " = typedef_hol2importer [OF type_definition_" ^ tycname ^ "]") thy5

            val _ = message "RESULT:"
            val _ = if_debug pth hth'
        in
            (thy6,hth')
        end

fun add_dump_syntax thy name =
    let
      val n = quotename name
      val syn = string_of_mixfix (mk_syn thy name)
    in
      add_dump ("syntax\n  "^n^" :: _ "^syn) thy
    end

fun type_introduction thyname thmname tycname abs_name rep_name (P,t) hth thy =
    case Importer_DefThy.get thy of
        Replaying _ => (thy,
          HOLThm([], Global_Theory.get_thm thy (thmname^"_@intern")) handle ERROR _ => hth)
      | _ =>
        let
            val _ = message "TYPE_INTRO:"
            val _ = if_debug pth hth
            val _ = warning ("Introducing type " ^ tycname ^ " (with morphisms " ^ abs_name ^ " and " ^ rep_name ^ ")")
            val (HOLThm(rens,td_th)) = norm_hthm thy hth
            val tT = type_of t
            val light_nonempty' =
                Drule.instantiate' [SOME (ctyp_of thy tT)]
                                   [SOME (cterm_of thy P),
                                    SOME (cterm_of thy t)] light_nonempty
            val th2 = beta_eta_thm (td_th RS (beta_eta_thm light_nonempty'))
            val c = case concl_of th2 of
                        _ $ (Const(@{const_name Ex},_) $ Abs(_,_,Const(@{const_name Set.member},_) $ _ $ c)) => c
                      | _ => raise ERR "type_introduction" "Bad type definition theorem"
            val tfrees = Misc_Legacy.term_tfrees c
            val tnames = sort_strings (map fst tfrees)
            val tsyn = mk_syn thy tycname
            val ((_, typedef_info), thy') =
              Typedef.add_typedef_global false NONE
                (Binding.name tycname, map (rpair dummyS) tnames, tsyn) c
                (SOME(Binding.name rep_name,Binding.name abs_name)) (rtac th2 1) thy
            val fulltyname = Sign.intern_type thy' tycname
            val aty = Type (fulltyname, map mk_vartype tnames)
            val typedef_hol2hollight' =
                Drule.instantiate'
                    [SOME (ctyp_of thy' aty), SOME (ctyp_of thy' tT)]
                    [NONE, NONE, NONE, SOME (cterm_of thy' (Free ("a", aty))), SOME (cterm_of thy' (Free ("r", tT)))]
                    typedef_hol2hollight
            val th4 = (#type_definition (#2 typedef_info)) RS typedef_hol2hollight'
            val _ = null (Thm.fold_terms Term.add_tvars th4 []) orelse
              raise ERR "type_introduction" "no type variables expected any more"
            val _ = null (Thm.fold_terms Term.add_vars th4 []) orelse
              raise ERR "type_introduction" "no term variables expected any more"
            val _ = message ("step 3: thyname="^thyname^", tycname="^tycname^", fulltyname="^fulltyname)
            val thy'' = add_importer_type_mapping thyname tycname true fulltyname thy'
            val _ = message "step 4"
            val (hth' as HOLThm args) = norm_hthm thy'' (HOLThm(rens,th4))
            val thy4 = add_importer_pending thyname thmname args thy''

            val P' = P (* why !? #2 (Logic.dest_equals (concl_of (rewrite_importer_term P thy4))) *)
            val c   =
                let
                    val PT = type_of P'
                in
                    Const (@{const_name Collect},PT-->HOLogic.mk_setT (domain_type PT)) $ P'
                end

            val tnames_string = if null tnames
                                then ""
                                else "(" ^ commas tnames ^ ") "
            val proc_prop =
              smart_string_of_cterm
                (Syntax.init_pretty_global thy4
                  |> not (null tnames) ? Config.put show_all_types true)
            val thy = add_dump ("typedef (open) " ^ tnames_string ^ (quotename tycname) ^
              " = " ^ (proc_prop (cterm_of thy4 c)) ^ " " ^
              (string_of_mixfix tsyn) ^ " morphisms "^
              (quote rep_name)^" "^(quote abs_name)^"\n"^
              ("  apply (rule light_ex_imp_nonempty[where t="^
              (proc_prop (cterm_of thy4 t))^"])\n"^
              ("  by (import " ^ thyname ^ " " ^ (quotename thmname) ^ ")"))) thy4
            val str_aty = Syntax.string_of_typ_global thy aty
            val thy = add_dump_syntax thy rep_name
            val thy = add_dump_syntax thy abs_name
            val thy = add_dump ("lemmas " ^ (quote (thmname^"_@intern")) ^
              " = typedef_hol2hollight \n"^
              "  [where a=\"a :: "^str_aty^"\" and r=r" ^
              " ,\n   OF "^(quotename ("type_definition_" ^ tycname)) ^ "]") thy
            val _ = message "RESULT:"
            val _ = if_debug pth hth'
        in
            (thy,hth')
        end
end

val prin = prin

end
