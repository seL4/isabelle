(*  Title:      HOL/MicroJava/J/TypeRel.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen

The relations between Java types
*)

TypeRel = Prog +

consts
  subcls1	:: "'c prog \\<Rightarrow> (cname \\<times> cname) set" (*        subclass *)
  widen,				 	    (*        widening *)
  cast		:: "'c prog \\<Rightarrow> (ty \\<times> ty) set"	    (*        casting *)

syntax
  subcls1	:: "'c prog \\<Rightarrow> [cname, cname] \\<Rightarrow> bool" ("_\\<turnstile>_\\<prec>C1_"	 [71,71,71] 70)
  subcls	:: "'c prog \\<Rightarrow> [cname, cname] \\<Rightarrow> bool" ("_\\<turnstile>_\\<prec>C _"	 [71,71,71] 70)
  widen		:: "'c prog \\<Rightarrow> [ty, ty] \\<Rightarrow> bool"       ("_\\<turnstile>_\\<preceq>_"  [71,71,71] 70)
  cast		:: "'c prog \\<Rightarrow> [ty, ty] \\<Rightarrow> bool"       ("_\\<turnstile>_\\<Rightarrow>? _"[71,71,71] 70)

translations
  	"G\\<turnstile>C \\<prec>C1 D" == "(C,D) \\<in> subcls1 G"
	"G\\<turnstile>C \\<prec>C  D" == "(C,D) \\<in> (subcls1 G)^+"
	"G\\<turnstile>S \\<preceq>   T" == "(S,T) \\<in> widen   G"
	"G\\<turnstile>S \\<Rightarrow>?  T" == "(S,T) \\<in> cast    G"

defs

  (* direct subclass, cf. 8.1.3 *)
  subcls1_def	"subcls1 G \\<equiv> {(C,D). \\<exists>c. class G C = Some c \\<and> fst c = Some D}"
  
consts

  cmethd	:: "'c prog \\<times> cname \\<Rightarrow> ( sig   \\<leadsto> cname \\<times> ty \\<times> 'c)"
  cfield	:: "'c prog \\<times> cname \\<Rightarrow> ( vname \\<leadsto> cname \\<times> ty)"
  fields	:: "'c prog \\<times> cname \\<Rightarrow> ((vname \\<times> cname) \\<times>  ty) list"

constdefs       (* auxiliary relations for recursive definitions below *)

  subcls1_rel	:: "(('c prog \\<times> cname) \\<times> ('c prog \\<times> cname)) set"
 "subcls1_rel \\<equiv> {((G,C),(G',C')). G = G' \\<and>  wf ((subcls1 G)^-1) \\<and>  G\\<turnstile>C'\\<prec>C1C}"

(* methods of a class, with inheritance, overriding and hiding, cf. 8.4.6 *)
recdef cmethd "subcls1_rel"
 "cmethd (G,C) = (if wf((subcls1 G)^-1) then (case class G C of None \\<Rightarrow> empty
                   | Some (sc,fs,ms) \\<Rightarrow> (case sc of None \\<Rightarrow> empty | Some D \\<Rightarrow> 
                                           if is_class G D then cmethd (G,D) 
                                                           else arbitrary) \\<oplus>
                                           map_of (map (\\<lambda>(s,  m ). 
                                                        (s,(C,m))) ms))
                  else arbitrary)"

(* list of fields of a class, including inherited and hidden ones *)
recdef fields  "subcls1_rel"
 "fields (G,C) = (if wf((subcls1 G)^-1) then (case class G C of None \\<Rightarrow> arbitrary
                   | Some (sc,fs,ms) \\<Rightarrow> map (\\<lambda>(fn,ft). ((fn,C),ft)) fs@
                                           (case sc of None \\<Rightarrow> [] | Some D \\<Rightarrow> 
                                           if is_class G D then fields (G,D) 
                                                           else arbitrary))
                  else arbitrary)"
defs

  cfield_def "cfield \\<equiv> map_of o (map (\\<lambda>((fn,fd),ft). (fn,(fd,ft)))) o fields"

inductive "widen G" intrs (*widening, viz. method invocation conversion, cf. 5.3
			     i.e. sort of syntactic subtyping *)
  refl	              "G\\<turnstile>      T \\<preceq> T" 	 (* identity conv., cf. 5.1.1 *)
  subcls "G\\<turnstile>C\\<prec>C D \\<Longrightarrow> G\\<turnstile>Class C \\<preceq> Class D"
  null	              "G\\<turnstile>     NT \\<preceq> RefT R"

inductive "cast G" intrs (* casting / narr.ref. conversion, cf. 5.5 / 5.1.5 *)
  widen	 "G\\<turnstile>S\\<preceq>T  \\<Longrightarrow> G\\<turnstile>      S \\<Rightarrow>? T"
  subcls "G\\<turnstile>C\\<prec>C D \\<Longrightarrow> G\\<turnstile>Class D \\<Rightarrow>? Class C"

end
