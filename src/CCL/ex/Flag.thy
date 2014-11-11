(*  Title:      CCL/ex/Flag.thy
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge
*)

section {* Dutch national flag program -- except that the point of Dijkstra's example was to use
  arrays and this uses lists. *}

theory Flag
imports List
begin

definition Colour :: "i set"
  where "Colour == Unit + Unit + Unit"

definition red :: "i"
  where "red == inl(one)"

definition white :: "i"
  where "white == inr(inl(one))"

definition blue :: "i"
  where "blue == inr(inr(one))"

definition ccase :: "[i,i,i,i]\<Rightarrow>i"
  where "ccase(c,r,w,b) == when(c, \<lambda>x. r, \<lambda>wb. when(wb, \<lambda>x. w, \<lambda>x. b))"

definition flag :: "i"
  where
    "flag == lam l. letrec
      flagx l be lcase(l,<[],<[],[]>>,
                       \<lambda>h t. split(flagx(t), \<lambda>lr p. split(p, \<lambda>lw lb.
                            ccase(h, <red$lr,<lw,lb>>,
                                     <lr,<white$lw,lb>>,
                                     <lr,<lw,blue$lb>>))))
      in flagx(l)"

axiomatization Perm :: "i \<Rightarrow> i \<Rightarrow> o"
definition Flag :: "i \<Rightarrow> i \<Rightarrow> o" where
  "Flag(l,x) == ALL lr:List(Colour).ALL lw:List(Colour).ALL lb:List(Colour).
                x = <lr,<lw,lb>> \<longrightarrow>
              (ALL c:Colour.(c mem lr = true \<longrightarrow> c=red) \<and>
                            (c mem lw = true \<longrightarrow> c=white) \<and>
                            (c mem lb = true \<longrightarrow> c=blue)) \<and>
              Perm(l,lr @ lw @ lb)"


lemmas flag_defs = Colour_def red_def white_def blue_def ccase_def

lemma ColourXH: "a : Colour \<longleftrightarrow> (a=red | a=white | a=blue)"
  unfolding simp_type_defs flag_defs by blast

lemma redT: "red : Colour"
  and whiteT: "white : Colour"
  and blueT: "blue : Colour"
  unfolding ColourXH by blast+

lemma ccaseT:
  "\<lbrakk>c:Colour; c=red \<Longrightarrow> r : C(red); c=white \<Longrightarrow> w : C(white); c=blue \<Longrightarrow> b : C(blue)\<rbrakk>
    \<Longrightarrow> ccase(c,r,w,b) : C(c)"
  unfolding flag_defs by ncanT

lemma "flag : List(Colour)->List(Colour)*List(Colour)*List(Colour)"
  apply (unfold flag_def)
  apply (typechk redT whiteT blueT ccaseT)
  apply clean_ccs
  apply (erule ListPRI [THEN ListPR_wf [THEN wfI]])
  apply assumption
  done

lemma "flag : PROD l:List(Colour).{x:List(Colour)*List(Colour)*List(Colour).Flag(x,l)}"
  apply (unfold flag_def)
  apply (gen_ccs redT whiteT blueT ccaseT)
  oops

end
