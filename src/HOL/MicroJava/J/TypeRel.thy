(*  Title:      HOL/MicroJava/J/TypeRel.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen

The relations between Java types
*)

TypeRel = Decl +

consts
  subcls1	:: "'c prog => (cname \\<times> cname) set"  (* subclass *)
  widen 	:: "'c prog => (ty    \\<times> ty   ) set"  (* widening *)
  cast		:: "'c prog => (cname \\<times> cname) set"  (* casting *)

syntax
  subcls1	:: "'c prog => [cname, cname] => bool" ("_\\<turnstile>_\\<prec>C1_"	 [71,71,71] 70)
  subcls	:: "'c prog => [cname, cname] => bool" ("_\\<turnstile>_\\<preceq>C _"	 [71,71,71] 70)
  widen		:: "'c prog => [ty   , ty   ] => bool" ("_\\<turnstile>_\\<preceq>_"  [71,71,71] 70)
  cast		:: "'c prog => [cname, cname] => bool" ("_\\<turnstile>_\\<preceq>? _"[71,71,71] 70)

translations
  	"G\\<turnstile>C \\<prec>C1 D" == "(C,D) \\<in> subcls1 G"
	"G\\<turnstile>C \\<preceq>C  D" == "(C,D) \\<in> (subcls1 G)^*"
	"G\\<turnstile>S \\<preceq>   T" == "(S,T) \\<in> widen   G"
	"G\\<turnstile>C \\<preceq>?  D" == "(C,D) \\<in> cast    G"

defs

  (* direct subclass, cf. 8.1.3 *)
  subcls1_def	"subcls1 G == {(C,D). \\<exists>c. class G C = Some c \\<and> fst c = Some D}"
  
consts

  method	:: "'c prog \\<times> cname => ( sig   \\<leadsto> cname \\<times> ty \\<times> 'c)"
  field	:: "'c prog \\<times> cname => ( vname \\<leadsto> cname \\<times> ty)"
  fields	:: "'c prog \\<times> cname => ((vname \\<times> cname) \\<times>  ty) list"

constdefs       (* auxiliary relations for recursive definitions below *)

  subcls1_rel	:: "(('c prog \\<times> cname) \\<times> ('c prog \\<times> cname)) set"
 "subcls1_rel == {((G,C),(G',C')). G = G' \\<and>  wf ((subcls1 G)^-1) \\<and>  G\\<turnstile>C'\\<prec>C1C}"

(* methods of a class, with inheritance, overriding and hiding, cf. 8.4.6 *)
recdef method "subcls1_rel"
 "method (G,C) = (if wf((subcls1 G)^-1) then (case class G C of None => empty
                   | Some (sc,fs,ms) => (case sc of None => empty | Some D => 
                                           if is_class G D then method (G,D) 
                                                           else arbitrary) \\<oplus>
                                           map_of (map (\\<lambda>(s,  m ). 
                                                        (s,(C,m))) ms))
                  else arbitrary)"

(* list of fields of a class, including inherited and hidden ones *)
recdef fields  "subcls1_rel"
 "fields (G,C) = (if wf((subcls1 G)^-1) then (case class G C of None => arbitrary
                   | Some (sc,fs,ms) => map (\\<lambda>(fn,ft). ((fn,C),ft)) fs@
                                           (case sc of None => [] | Some D => 
                                           if is_class G D then fields (G,D) 
                                                           else arbitrary))
                  else arbitrary)"
defs

  field_def "field == map_of o (map (\\<lambda>((fn,fd),ft). (fn,(fd,ft)))) o fields"

inductive "widen G" intrs (*widening, viz. method invocation conversion, cf. 5.3
			     i.e. sort of syntactic subtyping *)
  refl	             "G\\<turnstile>      T \\<preceq> T" 	 (* identity conv., cf. 5.1.1 *)
  subcls "G\\<turnstile>C\\<preceq>C D ==> G\\<turnstile>Class C \\<preceq> Class D"
  null	             "G\\<turnstile>     NT \\<preceq> RefT R"

inductive "cast G" intrs (* casting conversion, cf. 5.5 / 5.1.5 *)
                         (* left out casts on primitve types    *)
  widen	 "G\\<turnstile>C\\<preceq>C D ==> G\\<turnstile>C \\<preceq>? D"
  subcls "G\\<turnstile>D\\<preceq>C C ==> G\\<turnstile>C \\<preceq>? D"

end
