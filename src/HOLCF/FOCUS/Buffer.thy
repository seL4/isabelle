(*  Title: 	HOLCF/FOCUS/Buffer.thy
    ID:         $Id$
    Author: 	David von Oheimb, TU Muenchen

Formalization of section 4 of

@inproceedings{Broy95-SRBLO,
        author = {Manfred Broy},
        title = {Specification and ReFinement of a Buffer of Length One},
        booktitle = {Working Material of Marktoberdorf Summer School},
        year = {1994},
        publisher = {},
        editor = {},
        note = {\url{http://www4.in.tum.de/papers/broy_mod94.html}}
}

Slides available from http://isabelle.in.tum.de/HOLCF/1-Buffer.ps.gz
*)

Buffer = FOCUS + 

types   D
arities D :: type

datatype

  M	= Md D | Mreq ("\\<bullet>")

datatype

  State	= Sd D | Snil ("\\<currency>")

types

  SPF11		= "M fstream \\<rightarrow> D fstream"
  SPEC11	= "SPF11 set"
  SPSF11	= "State \\<Rightarrow> SPF11"
  SPECS11	= "SPSF11 set"

consts

  BufEq_F	:: "SPEC11 \\<Rightarrow> SPEC11"
  BufEq		:: "SPEC11"
  BufEq_alt	:: "SPEC11"

  BufAC_Asm_F	:: " (M fstream set) \\<Rightarrow> (M fstream set)"
  BufAC_Asm	:: " (M fstream set)"
  BufAC_Cmt_F	:: "((M fstream * D fstream) set) \\<Rightarrow> \
\		    ((M fstream * D fstream) set)"
  BufAC_Cmt	:: "((M fstream * D fstream) set)"
  BufAC		:: "SPEC11"

  BufSt_F	:: "SPECS11 \\<Rightarrow> SPECS11"
  BufSt_P	:: "SPECS11"
  BufSt		:: "SPEC11"

defs

  BufEq_F_def	"BufEq_F B \\<equiv> {f. \\<forall>d. f\\<cdot>(Md d\\<leadsto><>) = <> \\<and>  
			         (\\<forall>x. \\<exists>ff\\<in>B. f\\<cdot>(Md d\\<leadsto>\\<bullet>\\<leadsto>x) = d\\<leadsto>ff\\<cdot>x)}"
  BufEq_def	"BufEq     \\<equiv> gfp BufEq_F"
  BufEq_alt_def	"BufEq_alt \\<equiv> gfp (\\<lambda>B. {f. \\<forall>d. f\\<cdot>(Md d\\<leadsto><> ) = <> \\<and>
			         (\\<exists>ff\\<in>B. (\\<forall>x. f\\<cdot>(Md d\\<leadsto>\\<bullet>\\<leadsto>x) = d\\<leadsto>ff\\<cdot>x))})"
  BufAC_Asm_F_def "BufAC_Asm_F A \\<equiv> {s. s = <> \\<or>  
		  (\\<exists>d x. s = Md d\\<leadsto>x \\<and> (x = <> \\<or> (ft\\<cdot>x = Def \\<bullet> \\<and> (rt\\<cdot>x)\\<in>A)))}"
  BufAC_Asm_def	"BufAC_Asm \\<equiv> gfp BufAC_Asm_F"

  BufAC_Cmt_F_def "BufAC_Cmt_F C \\<equiv> {(s,t). \\<forall>d x. 
			   (s = <>         \\<longrightarrow>     t = <>                 ) \\<and>
			   (s = Md d\\<leadsto><>   \\<longrightarrow>     t = <>                 ) \\<and>
			   (s = Md d\\<leadsto>\\<bullet>\\<leadsto>x \\<longrightarrow> (ft\\<cdot>t = Def d \\<and> (x,rt\\<cdot>t)\\<in>C))}"
  BufAC_Cmt_def	"BufAC_Cmt \\<equiv> gfp BufAC_Cmt_F"
  BufAC_def	"BufAC \\<equiv> {f. \\<forall>x. x\\<in>BufAC_Asm \\<longrightarrow> (x,f\\<cdot>x)\\<in>BufAC_Cmt}"

  BufSt_F_def	"BufSt_F H \\<equiv> {h. \\<forall>s  . h s      \\<cdot><>        = <>         \\<and>
				 (\\<forall>d x. h \\<currency>     \\<cdot>(Md d\\<leadsto>x) = h (Sd d)\\<cdot>x \\<and>
			        (\\<exists>hh\\<in>H. h (Sd d)\\<cdot>(\\<bullet>   \\<leadsto>x) = d\\<leadsto>(hh \\<currency>\\<cdot>x)))}"
  BufSt_P_def	"BufSt_P \\<equiv> gfp BufSt_F"
  BufSt_def	"BufSt \\<equiv> {f. \\<exists>h\\<in>BufSt_P. f = h \\<currency>}"

end
