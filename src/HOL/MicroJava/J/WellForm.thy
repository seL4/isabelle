(*  Title:      HOL/MicroJava/J/WellForm.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen

Well-formedness of Java programs
for static checks on expressions and statements, see WellType.thy

improvements over Java Specification 1.0 (cf. 8.4.6.3, 8.4.6.4, 9.4.1):
* a method implementing or overwriting another method may have a result type 
  that widens to the result type of the other method (instead of identical type)

simplifications:
* for uniformity, Object is assumed to be declared like any other class
*)

WellForm = TypeRel +

types 'c wf_mb = 'c prog => cname => 'c mdecl => bool

constdefs
 wf_fdecl :: "'c prog => fdecl => bool"
"wf_fdecl G == \\<lambda>(fn,ft). is_type G ft"

 wf_mhead :: "'c prog => sig => ty => bool"
"wf_mhead G == \\<lambda>(mn,pTs) rT. (\\<forall>T\\<in>set pTs. is_type G T) \\<and> is_type G rT"

 wf_mdecl :: "'c wf_mb => 'c wf_mb"
"wf_mdecl wf_mb G C == \\<lambda>(sig,rT,mb). wf_mhead G sig rT \\<and> wf_mb G C (sig,rT,mb)"

 wf_cdecl :: "'c wf_mb => 'c prog => 'c cdecl => bool"
"wf_cdecl wf_mb G ==
   \\<lambda>(C,(sc,fs,ms)).
  (\\<forall>f\\<in>set fs. wf_fdecl G   f    ) \\<and>  unique fs \\<and>
  (\\<forall>m\\<in>set ms. wf_mdecl wf_mb G C m) \\<and>  unique ms \\<and>
  (case sc of None => C = Object
         | Some D =>
             is_class G D \\<and>  \\<not>  G\\<turnstile>D\\<preceq>C C \\<and>
             (\\<forall>(sig,rT,b)\\<in>set ms. \\<forall>D' rT' b'.
                 method(G,D) sig = Some(D',rT',b') --> G\\<turnstile>rT\\<preceq>rT'))"

 wf_prog :: "'c wf_mb => 'c prog => bool"
"wf_prog wf_mb G ==
   let cs = set G in ObjectC \\<in> cs \\<and> (\\<forall>c\\<in>cs. wf_cdecl wf_mb G c) \\<and> unique G"

end
