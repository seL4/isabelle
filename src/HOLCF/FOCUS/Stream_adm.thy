(*  Title: 	HOLCF/ex/Stream_adm.thy
    ID:         $Id$
    Author: 	David von Oheimb, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Admissibility for streams
*)

Stream_adm = Stream + Continuity +

consts

  stream_monoP,
  stream_antiP	:: "(('a stream) set \\<Rightarrow> ('a stream) set) \\<Rightarrow> bool"

defs

  stream_monoP_def "stream_monoP F \\<equiv> \\<exists>Q i. \\<forall>P s. Fin i \\<le> #s \\<longrightarrow> 
			s \\<in> F P = (stream_take i\\<cdot>s \\<in> Q \\<and> iterate i rt s \\<in> P)"
  stream_antiP_def "stream_antiP F \\<equiv> \\<forall>P x. \\<exists>Q i. 
		(#x  < Fin i \\<longrightarrow> (\\<forall>y. x \\<sqsubseteq> y \\<longrightarrow> y \\<in> F P \\<longrightarrow> x \\<in> F P)) \\<and>
		(Fin i <= #x \\<longrightarrow> (\\<forall>y. x \\<sqsubseteq> y \\<longrightarrow> 
		y \\<in> F P = (stream_take i\\<cdot>y \\<in> Q \\<and> iterate i rt y \\<in> P)))"

constdefs
  antitonP :: "'a set => bool"
 "antitonP P \\<equiv> \\<forall>x y. x \\<sqsubseteq> y \\<longrightarrow> y\\<in>P \\<longrightarrow> x\\<in>P"
  
end
