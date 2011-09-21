(*  Title:      HOL/Nitpick_Examples/Hotel_Nits.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2010-2011

Nitpick example based on Tobias Nipkow's hotel key card formalization.
*)

header {* Nitpick Example Based on Tobias Nipkow's Hotel Key Card
          Formalization *}

theory Hotel_Nits
imports Main
begin

nitpick_params [verbose, max_potential = 0, sat_solver = MiniSat_JNI,
                max_threads = 1, timeout = 240]

typedecl guest
typedecl key
typedecl room

type_synonym keycard = "key \<times> key"

record state =
  owns :: "room \<Rightarrow> guest option"
  currk :: "room \<Rightarrow> key"
  issued :: "key set"
  cards :: "guest \<Rightarrow> keycard set"
  roomk :: "room \<Rightarrow> key"
  isin :: "room \<Rightarrow> guest set"
  safe :: "room \<Rightarrow> bool"

inductive_set reach :: "state set" where
init:
"inj initk \<Longrightarrow>
 \<lparr>owns = (\<lambda>r. None), currk = initk, issued = range initk, cards = (\<lambda>g. {}),
  roomk = initk, isin = (\<lambda>r. {}), safe = (\<lambda>r. True)\<rparr> \<in> reach" |
check_in:
"\<lbrakk>s \<in> reach; k \<notin> issued s\<rbrakk> \<Longrightarrow>
 s\<lparr>currk := (currk s)(r := k), issued := issued s \<union> {k},
   cards := (cards s)(g := cards s g \<union> {(currk s r, k)}),
   owns :=  (owns s)(r := Some g), safe := (safe s)(r := False)\<rparr> \<in> reach" |
enter_room:
"\<lbrakk>s \<in> reach; (k,k') \<in> cards s g; roomk s r \<in> {k,k'}\<rbrakk> \<Longrightarrow>
 s\<lparr>isin := (isin s)(r := isin s r \<union> {g}),
   roomk := (roomk s)(r := k'),
   safe := (safe s)(r := owns s r = Some g \<and> isin s r = {} (* \<and> k' = currk s r *)
                         \<or> safe s r)\<rparr> \<in> reach" |
exit_room:
"\<lbrakk>s \<in> reach; g \<in> isin s r\<rbrakk> \<Longrightarrow> s\<lparr>isin := (isin s)(r := isin s r - {g})\<rparr> \<in> reach"

theorem safe: "s \<in> reach \<Longrightarrow> safe s r \<Longrightarrow> g \<in> isin s r \<Longrightarrow> owns s r = Some g"
nitpick [card room = 1, card guest = 2, card "guest option" = 3,
         card key = 4, card state = 6, show_consts, format = 2,
         expect = genuine]
(* nitpick [card room = 1, card guest = 2, expect = genuine] *)
oops

end
