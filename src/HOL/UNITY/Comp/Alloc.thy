(*  Title:      HOL/UNITY/Comp/Alloc.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Specification of Chandy and Charpentier's Allocator
*)

theory Alloc
imports AllocBase "../PPROD"
begin

subsection{*State definitions.  OUTPUT variables are locals*}

record clientState =
  giv :: "nat list"   --{*client's INPUT history:  tokens GRANTED*}
  ask :: "nat list"   --{*client's OUTPUT history: tokens REQUESTED*}
  rel :: "nat list"   --{*client's OUTPUT history: tokens RELEASED*}

record 'a clientState_d =
  clientState +
  dummy :: 'a       --{*dummy field for new variables*}

definition
  --{*DUPLICATED FROM Client.thy, but with "tok" removed*}
  --{*Maybe want a special theory section to declare such maps*}
  non_dummy :: "'a clientState_d => clientState"
  where "non_dummy s = (|giv = giv s, ask = ask s, rel = rel s|)"

definition
  --{*Renaming map to put a Client into the standard form*}
  client_map :: "'a clientState_d => clientState*'a"
  where "client_map = funPair non_dummy dummy"


record allocState =
  allocGiv :: "nat => nat list"   --{*OUTPUT history: source of "giv" for i*}
  allocAsk :: "nat => nat list"   --{*INPUT: allocator's copy of "ask" for i*}
  allocRel :: "nat => nat list"   --{*INPUT: allocator's copy of "rel" for i*}

record 'a allocState_d =
  allocState +
  dummy    :: 'a                --{*dummy field for new variables*}

record 'a systemState =
  allocState +
  client :: "nat => clientState"  --{*states of all clients*}
  dummy  :: 'a                    --{*dummy field for new variables*}


--{** Resource allocation system specification **}

definition
  --{*spec (1)*}
  system_safety :: "'a systemState program set"
  where "system_safety =
     Always {s. (SUM i: lessThan Nclients. (tokens o giv o sub i o client)s)
     \<le> NbT + (SUM i: lessThan Nclients. (tokens o rel o sub i o client)s)}"

definition
  --{*spec (2)*}
  system_progress :: "'a systemState program set"
  where "system_progress = (INT i : lessThan Nclients.
                        INT h.
                          {s. h \<le> (ask o sub i o client)s} LeadsTo
                          {s. h pfixLe (giv o sub i o client) s})"

definition
  system_spec :: "'a systemState program set"
  where "system_spec = system_safety Int system_progress"

--{** Client specification (required) ***}

definition
  --{*spec (3)*}
  client_increasing :: "'a clientState_d program set"
  where "client_increasing = UNIV guarantees  Increasing ask Int Increasing rel"

definition
  --{*spec (4)*}
  client_bounded :: "'a clientState_d program set"
  where "client_bounded = UNIV guarantees  Always {s. ALL elt : set (ask s). elt \<le> NbT}"

definition
  --{*spec (5)*}
  client_progress :: "'a clientState_d program set"
  where "client_progress =
         Increasing giv  guarantees
         (INT h. {s. h \<le> giv s & h pfixGe ask s}
                 LeadsTo {s. tokens h \<le> (tokens o rel) s})"

definition
  --{*spec: preserves part*}
  client_preserves :: "'a clientState_d program set"
  where "client_preserves = preserves giv Int preserves clientState_d.dummy"

definition
  --{*environmental constraints*}
  client_allowed_acts :: "'a clientState_d program set"
  where "client_allowed_acts =
       {F. AllowedActs F =
            insert Id (UNION (preserves (funPair rel ask)) Acts)}"

definition
  client_spec :: "'a clientState_d program set"
  where "client_spec = client_increasing Int client_bounded Int client_progress
                    Int client_allowed_acts Int client_preserves"

--{** Allocator specification (required) **}

definition
  --{*spec (6)*}
  alloc_increasing :: "'a allocState_d program set"
  where "alloc_increasing =
         UNIV  guarantees
         (INT i : lessThan Nclients. Increasing (sub i o allocGiv))"

definition
  --{*spec (7)*}
  alloc_safety :: "'a allocState_d program set"
  where "alloc_safety =
         (INT i : lessThan Nclients. Increasing (sub i o allocRel))
         guarantees
         Always {s. (SUM i: lessThan Nclients. (tokens o sub i o allocGiv)s)
         \<le> NbT + (SUM i: lessThan Nclients. (tokens o sub i o allocRel)s)}"

definition
  --{*spec (8)*}
  alloc_progress :: "'a allocState_d program set"
  where "alloc_progress =
         (INT i : lessThan Nclients. Increasing (sub i o allocAsk) Int
                                     Increasing (sub i o allocRel))
         Int
         Always {s. ALL i<Nclients.
                     ALL elt : set ((sub i o allocAsk) s). elt \<le> NbT}
         Int
         (INT i : lessThan Nclients.
          INT h. {s. h \<le> (sub i o allocGiv)s & h pfixGe (sub i o allocAsk)s}
                 LeadsTo
                 {s. tokens h \<le> (tokens o sub i o allocRel)s})
         guarantees
             (INT i : lessThan Nclients.
              INT h. {s. h \<le> (sub i o allocAsk) s}
                     LeadsTo
                     {s. h pfixLe (sub i o allocGiv) s})"

  (*NOTE: to follow the original paper, the formula above should have had
        INT h. {s. h i \<le> (sub i o allocGiv)s & h i pfixGe (sub i o allocAsk)s}
               LeadsTo
               {s. tokens h i \<le> (tokens o sub i o allocRel)s})
    thus h should have been a function variable.  However, only h i is ever
    looked at.*)

definition
  --{*spec: preserves part*}
  alloc_preserves :: "'a allocState_d program set"
  where "alloc_preserves = preserves allocRel Int preserves allocAsk Int
                        preserves allocState_d.dummy"

definition
  --{*environmental constraints*}
  alloc_allowed_acts :: "'a allocState_d program set"
  where "alloc_allowed_acts =
       {F. AllowedActs F =
            insert Id (UNION (preserves allocGiv) Acts)}"

definition
  alloc_spec :: "'a allocState_d program set"
  where "alloc_spec = alloc_increasing Int alloc_safety Int alloc_progress Int
                   alloc_allowed_acts Int alloc_preserves"

--{** Network specification **}

definition
  --{*spec (9.1)*}
  network_ask :: "'a systemState program set"
  where "network_ask = (INT i : lessThan Nclients.
                        Increasing (ask o sub i o client)  guarantees
                        ((sub i o allocAsk) Fols (ask o sub i o client)))"

definition
  --{*spec (9.2)*}
  network_giv :: "'a systemState program set"
  where "network_giv = (INT i : lessThan Nclients.
                        Increasing (sub i o allocGiv)
                        guarantees
                        ((giv o sub i o client) Fols (sub i o allocGiv)))"

definition
  --{*spec (9.3)*}
  network_rel :: "'a systemState program set"
  where "network_rel = (INT i : lessThan Nclients.
                        Increasing (rel o sub i o client)
                        guarantees
                        ((sub i o allocRel) Fols (rel o sub i o client)))"

definition
  --{*spec: preserves part*}
  network_preserves :: "'a systemState program set"
  where "network_preserves =
       preserves allocGiv  Int
       (INT i : lessThan Nclients. preserves (rel o sub i o client)  Int
                                   preserves (ask o sub i o client))"

definition
  --{*environmental constraints*}
  network_allowed_acts :: "'a systemState program set"
  where "network_allowed_acts =
       {F. AllowedActs F =
           insert Id
            (UNION (preserves allocRel Int
                    (INT i: lessThan Nclients. preserves(giv o sub i o client)))
                  Acts)}"

definition
  network_spec :: "'a systemState program set"
  where "network_spec = network_ask Int network_giv Int
                     network_rel Int network_allowed_acts Int
                     network_preserves"


--{** State mappings **}
definition
  sysOfAlloc :: "((nat => clientState) * 'a) allocState_d => 'a systemState"
  where "sysOfAlloc = (%s. let (cl,xtr) = allocState_d.dummy s
                       in (| allocGiv = allocGiv s,
                             allocAsk = allocAsk s,
                             allocRel = allocRel s,
                             client   = cl,
                             dummy    = xtr|))"


definition
  sysOfClient :: "(nat => clientState) * 'a allocState_d => 'a systemState"
  where "sysOfClient = (%(cl,al). (| allocGiv = allocGiv al,
                                 allocAsk = allocAsk al,
                                 allocRel = allocRel al,
                                 client   = cl,
                                 systemState.dummy = allocState_d.dummy al|))"

axiomatization Alloc :: "'a allocState_d program"
  where Alloc: "Alloc : alloc_spec"

axiomatization Client :: "'a clientState_d program"
  where Client: "Client : client_spec"

axiomatization Network :: "'a systemState program"
  where Network: "Network : network_spec"

definition System  :: "'a systemState program"
  where "System = rename sysOfAlloc Alloc Join Network Join
                 (rename sysOfClient
                  (plam x: lessThan Nclients. rename client_map Client))"


(**
locale System =
  fixes
    Alloc   :: 'a allocState_d program
    Client  :: 'a clientState_d program
    Network :: 'a systemState program
    System  :: 'a systemState program

  assumes
    Alloc   "Alloc   : alloc_spec"
    Client  "Client  : client_spec"
    Network "Network : network_spec"

  defines
    System_def
      "System == rename sysOfAlloc Alloc
                 Join
                 Network
                 Join
                 (rename sysOfClient
                  (plam x: lessThan Nclients. rename client_map Client))"
**)

declare subset_preserves_o [THEN [2] rev_subsetD, intro]
declare subset_preserves_o [THEN [2] rev_subsetD, simp]
declare funPair_o_distrib [simp]
declare Always_INT_distrib [simp]
declare o_apply [simp del]

(*For rewriting of specifications related by "guarantees"*)
lemmas [simp] =
  rename_image_constrains
  rename_image_stable
  rename_image_increasing
  rename_image_invariant
  rename_image_Constrains
  rename_image_Stable
  rename_image_Increasing
  rename_image_Always
  rename_image_leadsTo
  rename_image_LeadsTo
  rename_preserves
  rename_image_preserves
  lift_image_preserves
  bij_image_INT
  bij_is_inj [THEN image_Int]
  bij_image_Collect_eq

ML {*
(*Splits up conjunctions & intersections: like CONJUNCTS in the HOL system*)
fun list_of_Int th =
    (list_of_Int (th RS conjunct1) @ list_of_Int (th RS conjunct2))
    handle THM _ => (list_of_Int (th RS IntD1) @ list_of_Int (th RS IntD2))
    handle THM _ => (list_of_Int (th RS @{thm INT_D}))
    handle THM _ => (list_of_Int (th RS bspec))
    handle THM _ => [th];
*}

lemmas lessThanBspec = lessThan_iff [THEN iffD2, THEN [2] bspec]

attribute_setup normalized = {*
let
  fun normalized th =
    normalized (th RS spec
      handle THM _ => th RS @{thm lessThanBspec}
      handle THM _ => th RS bspec
      handle THM _ => th RS (@{thm guarantees_INT_right_iff} RS iffD1))
    handle THM _ => th;
in
  Scan.succeed (Thm.rule_attribute (K normalized))
end
*}

(*** bijectivity of sysOfAlloc [MUST BE AUTOMATED] ***)
ML {*
fun record_auto_tac ctxt =
  let val ctxt' =
    ctxt
    |> map_claset (fn cs => cs addSWrapper Record.split_wrapper)
    |> map_simpset (fn ss => ss addsimps
       [@{thm sysOfAlloc_def}, @{thm sysOfClient_def},
        @{thm client_map_def}, @{thm non_dummy_def}, @{thm funPair_def},
        @{thm o_apply}, @{thm Let_def}])
  in auto_tac ctxt' end;

*}

method_setup record_auto = {* Scan.succeed (SIMPLE_METHOD o record_auto_tac) *}

lemma inj_sysOfAlloc [iff]: "inj sysOfAlloc"
  apply (unfold sysOfAlloc_def Let_def)
  apply (rule inj_onI)
  apply record_auto
  done

text{*We need the inverse; also having it simplifies the proof of surjectivity*}
lemma inv_sysOfAlloc_eq [simp]: "!!s. inv sysOfAlloc s =
             (| allocGiv = allocGiv s,
                allocAsk = allocAsk s,
                allocRel = allocRel s,
                allocState_d.dummy = (client s, dummy s) |)"
  apply (rule inj_sysOfAlloc [THEN inv_f_eq])
  apply record_auto
  done

lemma surj_sysOfAlloc [iff]: "surj sysOfAlloc"
  apply (simp add: surj_iff_all)
  apply record_auto
  done

lemma bij_sysOfAlloc [iff]: "bij sysOfAlloc"
  apply (blast intro: bijI)
  done


subsubsection{*bijectivity of @{term sysOfClient}*}

lemma inj_sysOfClient [iff]: "inj sysOfClient"
  apply (unfold sysOfClient_def)
  apply (rule inj_onI)
  apply record_auto
  done

lemma inv_sysOfClient_eq [simp]: "!!s. inv sysOfClient s =
             (client s,
              (| allocGiv = allocGiv s,
                 allocAsk = allocAsk s,
                 allocRel = allocRel s,
                 allocState_d.dummy = systemState.dummy s|) )"
  apply (rule inj_sysOfClient [THEN inv_f_eq])
  apply record_auto
  done

lemma surj_sysOfClient [iff]: "surj sysOfClient"
  apply (simp add: surj_iff_all)
  apply record_auto
  done

lemma bij_sysOfClient [iff]: "bij sysOfClient"
  apply (blast intro: bijI)
  done


subsubsection{*bijectivity of @{term client_map}*}

lemma inj_client_map [iff]: "inj client_map"
  apply (unfold inj_on_def)
  apply record_auto
  done

lemma inv_client_map_eq [simp]: "!!s. inv client_map s =
             (%(x,y).(|giv = giv x, ask = ask x, rel = rel x,
                       clientState_d.dummy = y|)) s"
  apply (rule inj_client_map [THEN inv_f_eq])
  apply record_auto
  done

lemma surj_client_map [iff]: "surj client_map"
  apply (simp add: surj_iff_all)
  apply record_auto
  done

lemma bij_client_map [iff]: "bij client_map"
  apply (blast intro: bijI)
  done


text{*o-simprules for @{term client_map}*}

lemma fst_o_client_map: "fst o client_map = non_dummy"
  apply (unfold client_map_def)
  apply (rule fst_o_funPair)
  done

ML {* bind_thms ("fst_o_client_map'", make_o_equivs @{thm fst_o_client_map}) *}
declare fst_o_client_map' [simp]

lemma snd_o_client_map: "snd o client_map = clientState_d.dummy"
  apply (unfold client_map_def)
  apply (rule snd_o_funPair)
  done

ML {* bind_thms ("snd_o_client_map'", make_o_equivs @{thm snd_o_client_map}) *}
declare snd_o_client_map' [simp]


subsection{*o-simprules for @{term sysOfAlloc} [MUST BE AUTOMATED]*}

lemma client_o_sysOfAlloc: "client o sysOfAlloc = fst o allocState_d.dummy "
  apply record_auto
  done

ML {* bind_thms ("client_o_sysOfAlloc'", make_o_equivs @{thm client_o_sysOfAlloc}) *}
declare client_o_sysOfAlloc' [simp]

lemma allocGiv_o_sysOfAlloc_eq: "allocGiv o sysOfAlloc = allocGiv"
  apply record_auto
  done

ML {* bind_thms ("allocGiv_o_sysOfAlloc_eq'", make_o_equivs @{thm allocGiv_o_sysOfAlloc_eq}) *}
declare allocGiv_o_sysOfAlloc_eq' [simp]

lemma allocAsk_o_sysOfAlloc_eq: "allocAsk o sysOfAlloc = allocAsk"
  apply record_auto
  done

ML {* bind_thms ("allocAsk_o_sysOfAlloc_eq'", make_o_equivs @{thm allocAsk_o_sysOfAlloc_eq}) *}
declare allocAsk_o_sysOfAlloc_eq' [simp]

lemma allocRel_o_sysOfAlloc_eq: "allocRel o sysOfAlloc = allocRel"
  apply record_auto
  done

ML {* bind_thms ("allocRel_o_sysOfAlloc_eq'", make_o_equivs @{thm allocRel_o_sysOfAlloc_eq}) *}
declare allocRel_o_sysOfAlloc_eq' [simp]


subsection{* o-simprules for @{term sysOfClient} [MUST BE AUTOMATED]*}

lemma client_o_sysOfClient: "client o sysOfClient = fst"
  apply record_auto
  done

ML {* bind_thms ("client_o_sysOfClient'", make_o_equivs @{thm client_o_sysOfClient}) *}
declare client_o_sysOfClient' [simp]

lemma allocGiv_o_sysOfClient_eq: "allocGiv o sysOfClient = allocGiv o snd "
  apply record_auto
  done

ML {* bind_thms ("allocGiv_o_sysOfClient_eq'", make_o_equivs @{thm allocGiv_o_sysOfClient_eq}) *}
declare allocGiv_o_sysOfClient_eq' [simp]

lemma allocAsk_o_sysOfClient_eq: "allocAsk o sysOfClient = allocAsk o snd "
  apply record_auto
  done

ML {* bind_thms ("allocAsk_o_sysOfClient_eq'", make_o_equivs @{thm allocAsk_o_sysOfClient_eq}) *}
declare allocAsk_o_sysOfClient_eq' [simp]

lemma allocRel_o_sysOfClient_eq: "allocRel o sysOfClient = allocRel o snd "
  apply record_auto
  done

ML {* bind_thms ("allocRel_o_sysOfClient_eq'", make_o_equivs @{thm allocRel_o_sysOfClient_eq}) *}
declare allocRel_o_sysOfClient_eq' [simp]

lemma allocGiv_o_inv_sysOfAlloc_eq: "allocGiv o inv sysOfAlloc = allocGiv"
  apply (simp add: o_def)
  done

ML {* bind_thms ("allocGiv_o_inv_sysOfAlloc_eq'", make_o_equivs @{thm allocGiv_o_inv_sysOfAlloc_eq}) *}
declare allocGiv_o_inv_sysOfAlloc_eq' [simp]

lemma allocAsk_o_inv_sysOfAlloc_eq: "allocAsk o inv sysOfAlloc = allocAsk"
  apply (simp add: o_def)
  done

ML {* bind_thms ("allocAsk_o_inv_sysOfAlloc_eq'", make_o_equivs @{thm allocAsk_o_inv_sysOfAlloc_eq}) *}
declare allocAsk_o_inv_sysOfAlloc_eq' [simp]

lemma allocRel_o_inv_sysOfAlloc_eq: "allocRel o inv sysOfAlloc = allocRel"
  apply (simp add: o_def)
  done

ML {* bind_thms ("allocRel_o_inv_sysOfAlloc_eq'", make_o_equivs @{thm allocRel_o_inv_sysOfAlloc_eq}) *}
declare allocRel_o_inv_sysOfAlloc_eq' [simp]

lemma rel_inv_client_map_drop_map: "(rel o inv client_map o drop_map i o inv sysOfClient) =
      rel o sub i o client"
  apply (simp add: o_def drop_map_def)
  done

ML {* bind_thms ("rel_inv_client_map_drop_map'", make_o_equivs @{thm rel_inv_client_map_drop_map}) *}
declare rel_inv_client_map_drop_map [simp]

lemma ask_inv_client_map_drop_map: "(ask o inv client_map o drop_map i o inv sysOfClient) =
      ask o sub i o client"
  apply (simp add: o_def drop_map_def)
  done

ML {* bind_thms ("ask_inv_client_map_drop_map'", make_o_equivs @{thm ask_inv_client_map_drop_map}) *}
declare ask_inv_client_map_drop_map [simp]


declare finite_lessThan [iff]

text{*Client : <unfolded specification> *}
lemmas client_spec_simps =
  client_spec_def client_increasing_def client_bounded_def
  client_progress_def client_allowed_acts_def client_preserves_def
  guarantees_Int_right

ML {*
val [Client_Increasing_ask, Client_Increasing_rel,
     Client_Bounded, Client_Progress, Client_AllowedActs,
     Client_preserves_giv, Client_preserves_dummy] =
        @{thm Client} |> simplify (@{simpset} addsimps @{thms client_spec_simps})
               |> list_of_Int;

bind_thm ("Client_Increasing_ask", Client_Increasing_ask);
bind_thm ("Client_Increasing_rel", Client_Increasing_rel);
bind_thm ("Client_Bounded", Client_Bounded);
bind_thm ("Client_Progress", Client_Progress);
bind_thm ("Client_AllowedActs", Client_AllowedActs);
bind_thm ("Client_preserves_giv", Client_preserves_giv);
bind_thm ("Client_preserves_dummy", Client_preserves_dummy);
*}

declare
  Client_Increasing_ask [iff]
  Client_Increasing_rel [iff]
  Client_Bounded [iff]
  Client_preserves_giv [iff]
  Client_preserves_dummy [iff]


text{*Network : <unfolded specification> *}
lemmas network_spec_simps =
  network_spec_def network_ask_def network_giv_def
  network_rel_def network_allowed_acts_def network_preserves_def
  ball_conj_distrib

ML {*
val [Network_Ask, Network_Giv, Network_Rel, Network_AllowedActs,
     Network_preserves_allocGiv, Network_preserves_rel,
     Network_preserves_ask]  =
        @{thm Network} |> simplify (@{simpset} addsimps @{thms network_spec_simps})
                |> list_of_Int;

bind_thm ("Network_Ask", Network_Ask);
bind_thm ("Network_Giv", Network_Giv);
bind_thm ("Network_Rel", Network_Rel);
bind_thm ("Network_AllowedActs", Network_AllowedActs);
bind_thm ("Network_preserves_allocGiv", Network_preserves_allocGiv);
bind_thm ("Network_preserves_rel", Network_preserves_rel);
bind_thm ("Network_preserves_ask", Network_preserves_ask);
*}

declare Network_preserves_allocGiv [iff]

declare
  Network_preserves_rel [simp]
  Network_preserves_ask [simp]

declare
  Network_preserves_rel [simplified o_def, simp]
  Network_preserves_ask [simplified o_def, simp]

text{*Alloc : <unfolded specification> *}
lemmas alloc_spec_simps =
  alloc_spec_def alloc_increasing_def alloc_safety_def
  alloc_progress_def alloc_allowed_acts_def alloc_preserves_def

ML {*
val [Alloc_Increasing_0, Alloc_Safety, Alloc_Progress, Alloc_AllowedActs,
     Alloc_preserves_allocRel, Alloc_preserves_allocAsk,
     Alloc_preserves_dummy] =
        @{thm Alloc} |> simplify (@{simpset} addsimps @{thms alloc_spec_simps})
              |> list_of_Int;

bind_thm ("Alloc_Increasing_0", Alloc_Increasing_0);
bind_thm ("Alloc_Safety", Alloc_Safety);
bind_thm ("Alloc_Progress", Alloc_Progress);
bind_thm ("Alloc_AllowedActs", Alloc_AllowedActs);
bind_thm ("Alloc_preserves_allocRel", Alloc_preserves_allocRel);
bind_thm ("Alloc_preserves_allocAsk", Alloc_preserves_allocAsk);
bind_thm ("Alloc_preserves_dummy", Alloc_preserves_dummy);
*}

text{*Strip off the INT in the guarantees postcondition*}

lemmas Alloc_Increasing = Alloc_Increasing_0 [normalized]

declare
  Alloc_preserves_allocRel [iff]
  Alloc_preserves_allocAsk [iff]
  Alloc_preserves_dummy [iff]


subsection{*Components Lemmas [MUST BE AUTOMATED]*}

lemma Network_component_System: "Network Join
      ((rename sysOfClient
        (plam x: (lessThan Nclients). rename client_map Client)) Join
       rename sysOfAlloc Alloc)
      = System"
  by (simp add: System_def Join_ac)

lemma Client_component_System: "(rename sysOfClient
       (plam x: (lessThan Nclients). rename client_map Client)) Join
      (Network Join rename sysOfAlloc Alloc)  =  System"
  by (simp add: System_def Join_ac)

lemma Alloc_component_System: "rename sysOfAlloc Alloc Join
       ((rename sysOfClient (plam x: (lessThan Nclients). rename client_map Client)) Join
        Network)  =  System"
  by (simp add: System_def Join_ac)

declare
  Client_component_System [iff]
  Network_component_System [iff]
  Alloc_component_System [iff]


text{** These preservation laws should be generated automatically **}

lemma Client_Allowed [simp]: "Allowed Client = preserves rel Int preserves ask"
  by (auto simp add: Allowed_def Client_AllowedActs safety_prop_Acts_iff)

lemma Network_Allowed [simp]: "Allowed Network =
        preserves allocRel Int
        (INT i: lessThan Nclients. preserves(giv o sub i o client))"
  by (auto simp add: Allowed_def Network_AllowedActs safety_prop_Acts_iff)

lemma Alloc_Allowed [simp]: "Allowed Alloc = preserves allocGiv"
  by (auto simp add: Allowed_def Alloc_AllowedActs safety_prop_Acts_iff)

text{*needed in @{text rename_client_map_tac}*}
lemma OK_lift_rename_Client [simp]: "OK I (%i. lift i (rename client_map Client))"
  apply (rule OK_lift_I)
  apply auto
  apply (drule_tac w1 = rel in subset_preserves_o [THEN [2] rev_subsetD])
  apply (drule_tac [2] w1 = ask in subset_preserves_o [THEN [2] rev_subsetD])
  apply (auto simp add: o_def split_def)
  done

lemma fst_lift_map_eq_fst [simp]: "fst (lift_map i x) i = fst x"
apply (insert fst_o_lift_map [of i])
apply (drule fun_cong [where x=x])
apply (simp add: o_def)
done

lemma fst_o_lift_map' [simp]:
     "(f \<circ> sub i \<circ> fst \<circ> lift_map i \<circ> g) = f o fst o g"
apply (subst fst_o_lift_map [symmetric])
apply (simp only: o_assoc)
done


(*The proofs of rename_Client_Increasing, rename_Client_Bounded and
  rename_Client_Progress are similar.  All require copying out the original
  Client property.  A forward proof can be constructed as follows:

  Client_Increasing_ask RS
      (bij_client_map RS rename_rename_guarantees_eq RS iffD2)
  RS (lift_lift_guarantees_eq RS iffD2)
  RS guarantees_PLam_I
  RS (bij_sysOfClient RS rename_rename_guarantees_eq RS iffD2)
  |> simplify (simpset() addsimps [lift_image_eq_rename, o_def, split_def,
                                   surj_rename])

However, the "preserves" property remains to be discharged, and the unfolding
of "o" and "sub" complicates subsequent reasoning.

The following tactic works for all three proofs, though it certainly looks
ad-hoc!
*)
ML
{*
fun rename_client_map_tac ss =
  EVERY [
    simp_tac (ss addsimps [@{thm rename_guarantees_eq_rename_inv}]) 1,
    rtac @{thm guarantees_PLam_I} 1,
    assume_tac 2,
         (*preserves: routine reasoning*)
    asm_simp_tac (ss addsimps [@{thm lift_preserves_sub}]) 2,
         (*the guarantee for  "lift i (rename client_map Client)" *)
    asm_simp_tac
        (ss addsimps [@{thm lift_guarantees_eq_lift_inv},
                      @{thm rename_guarantees_eq_rename_inv},
                      @{thm bij_imp_bij_inv}, @{thm surj_rename},
                      @{thm inv_inv_eq}]) 1,
    asm_simp_tac
        (@{simpset} addsimps [@{thm o_def}, @{thm non_dummy_def}, @{thm guarantees_Int_right}]) 1]
*}

method_setup rename_client_map = {*
  Scan.succeed (fn ctxt =>
    SIMPLE_METHOD (rename_client_map_tac (simpset_of ctxt)))
*}

text{*Lifting @{text Client_Increasing} to @{term systemState}*}
lemma rename_Client_Increasing: "i : I
      ==> rename sysOfClient (plam x: I. rename client_map Client) :
            UNIV  guarantees
            Increasing (ask o sub i o client) Int
            Increasing (rel o sub i o client)"
  by rename_client_map

lemma preserves_sub_fst_lift_map: "[| F : preserves w; i ~= j |]
      ==> F : preserves (sub i o fst o lift_map j o funPair v w)"
  apply (auto simp add: lift_map_def split_def linorder_neq_iff o_def)
  apply (drule_tac [!] subset_preserves_o [THEN [2] rev_subsetD])
  apply (auto simp add: o_def)
  done

lemma client_preserves_giv_oo_client_map: "[| i < Nclients; j < Nclients |]
      ==> Client : preserves (giv o sub i o fst o lift_map j o client_map)"
  apply (case_tac "i=j")
  apply (simp, simp add: o_def non_dummy_def)
  apply (drule Client_preserves_dummy [THEN preserves_sub_fst_lift_map])
  apply (drule_tac [!] subset_preserves_o [THEN [2] rev_subsetD])
  apply (simp add: o_def client_map_def)
  done

lemma rename_sysOfClient_ok_Network:
  "rename sysOfClient (plam x: lessThan Nclients. rename client_map Client)
    ok Network"
  by (auto simp add: ok_iff_Allowed client_preserves_giv_oo_client_map)

lemma rename_sysOfClient_ok_Alloc:
  "rename sysOfClient (plam x: lessThan Nclients. rename client_map Client)
    ok rename sysOfAlloc Alloc"
  by (simp add: ok_iff_Allowed)

lemma rename_sysOfAlloc_ok_Network: "rename sysOfAlloc Alloc ok Network"
  by (simp add: ok_iff_Allowed)

declare
  rename_sysOfClient_ok_Network [iff]
  rename_sysOfClient_ok_Alloc [iff]
  rename_sysOfAlloc_ok_Network [iff]

text{*The "ok" laws, re-oriented.
  But not sure this works: theorem @{text ok_commute} is needed below*}
declare
  rename_sysOfClient_ok_Network [THEN ok_sym, iff]
  rename_sysOfClient_ok_Alloc [THEN ok_sym, iff]
  rename_sysOfAlloc_ok_Network [THEN ok_sym]

lemma System_Increasing: "i < Nclients
      ==> System : Increasing (ask o sub i o client) Int
                   Increasing (rel o sub i o client)"
  apply (rule component_guaranteesD [OF rename_Client_Increasing Client_component_System])
  apply auto
  done

lemmas rename_guarantees_sysOfAlloc_I =
  bij_sysOfAlloc [THEN rename_rename_guarantees_eq, THEN iffD2]


(*Lifting Alloc_Increasing up to the level of systemState*)
lemmas rename_Alloc_Increasing =
  Alloc_Increasing
    [THEN rename_guarantees_sysOfAlloc_I,
     simplified surj_rename o_def sub_apply
                rename_image_Increasing bij_sysOfAlloc
                allocGiv_o_inv_sysOfAlloc_eq']

lemma System_Increasing_allocGiv:
     "i < Nclients ==> System : Increasing (sub i o allocGiv)"
  apply (unfold System_def)
  apply (simp add: o_def)
  apply (rule rename_Alloc_Increasing [THEN guarantees_Join_I1, THEN guaranteesD])
  apply auto
  done


ML {*
bind_thms ("System_Increasing'", list_of_Int @{thm System_Increasing})
*}

declare System_Increasing' [intro!]

text{* Follows consequences.
    The "Always (INT ...) formulation expresses the general safety property
    and allows it to be combined using @{text Always_Int_rule} below. *}

lemma System_Follows_rel:
  "i < Nclients ==> System : ((sub i o allocRel) Fols (rel o sub i o client))"
  apply (auto intro!: Network_Rel [THEN component_guaranteesD])
  apply (simp add: ok_commute [of Network])
  done

lemma System_Follows_ask:
  "i < Nclients ==> System : ((sub i o allocAsk) Fols (ask o sub i o client))"
  apply (auto intro!: Network_Ask [THEN component_guaranteesD])
  apply (simp add: ok_commute [of Network])
  done

lemma System_Follows_allocGiv:
  "i < Nclients ==> System : (giv o sub i o client) Fols (sub i o allocGiv)"
  apply (auto intro!: Network_Giv [THEN component_guaranteesD]
    rename_Alloc_Increasing [THEN component_guaranteesD])
  apply (simp_all add: o_def non_dummy_def ok_commute [of Network])
  apply (auto intro!: rename_Alloc_Increasing [THEN component_guaranteesD])
  done


lemma Always_giv_le_allocGiv: "System : Always (INT i: lessThan Nclients.
                       {s. (giv o sub i o client) s \<le> (sub i o allocGiv) s})"
  apply auto
  apply (erule System_Follows_allocGiv [THEN Follows_Bounded])
  done


lemma Always_allocAsk_le_ask: "System : Always (INT i: lessThan Nclients.
                       {s. (sub i o allocAsk) s \<le> (ask o sub i o client) s})"
  apply auto
  apply (erule System_Follows_ask [THEN Follows_Bounded])
  done


lemma Always_allocRel_le_rel: "System : Always (INT i: lessThan Nclients.
                       {s. (sub i o allocRel) s \<le> (rel o sub i o client) s})"
  by (auto intro!: Follows_Bounded System_Follows_rel)


subsection{*Proof of the safety property (1)*}

text{*safety (1), step 1 is @{text System_Follows_rel}*}

text{*safety (1), step 2*}
(* i < Nclients ==> System : Increasing (sub i o allocRel) *)
lemmas System_Increasing_allocRel = System_Follows_rel [THEN Follows_Increasing1]

(*Lifting Alloc_safety up to the level of systemState.
  Simplifying with o_def gets rid of the translations but it unfortunately
  gets rid of the other "o"s too.*)

text{*safety (1), step 3*}
lemma System_sum_bounded:
    "System : Always {s. (\<Sum>i \<in> lessThan Nclients. (tokens o sub i o allocGiv) s)
            \<le> NbT + (\<Sum>i \<in> lessThan Nclients. (tokens o sub i o allocRel) s)}"
  apply (simp add: o_apply)
  apply (insert Alloc_Safety [THEN rename_guarantees_sysOfAlloc_I])
  apply (simp add: o_def)
  apply (erule component_guaranteesD)
  apply (auto simp add: System_Increasing_allocRel [simplified sub_apply o_def])
  done

text{* Follows reasoning*}

lemma Always_tokens_giv_le_allocGiv: "System : Always (INT i: lessThan Nclients.
                          {s. (tokens o giv o sub i o client) s
                           \<le> (tokens o sub i o allocGiv) s})"
  apply (rule Always_giv_le_allocGiv [THEN Always_weaken])
  apply (auto intro: tokens_mono_prefix simp add: o_apply)
  done

lemma Always_tokens_allocRel_le_rel: "System : Always (INT i: lessThan Nclients.
                          {s. (tokens o sub i o allocRel) s
                           \<le> (tokens o rel o sub i o client) s})"
  apply (rule Always_allocRel_le_rel [THEN Always_weaken])
  apply (auto intro: tokens_mono_prefix simp add: o_apply)
  done

text{*safety (1), step 4 (final result!) *}
theorem System_safety: "System : system_safety"
  apply (unfold system_safety_def)
  apply (tactic {* rtac (Always_Int_rule [@{thm System_sum_bounded},
    @{thm Always_tokens_giv_le_allocGiv}, @{thm Always_tokens_allocRel_le_rel}] RS
    @{thm Always_weaken}) 1 *})
  apply auto
  apply (rule setsum_fun_mono [THEN order_trans])
  apply (drule_tac [2] order_trans)
  apply (rule_tac [2] add_le_mono [OF order_refl setsum_fun_mono])
  prefer 3 apply assumption
  apply auto
  done

subsection {* Proof of the progress property (2) *}

text{*progress (2), step 1 is @{text System_Follows_ask} and
      @{text System_Follows_rel}*}

text{*progress (2), step 2; see also @{text System_Increasing_allocRel}*}
(* i < Nclients ==> System : Increasing (sub i o allocAsk) *)
lemmas System_Increasing_allocAsk =  System_Follows_ask [THEN Follows_Increasing1]

text{*progress (2), step 3: lifting @{text Client_Bounded} to systemState*}
lemma rename_Client_Bounded: "i : I
    ==> rename sysOfClient (plam x: I. rename client_map Client) :
          UNIV  guarantees
          Always {s. ALL elt : set ((ask o sub i o client) s). elt \<le> NbT}"
  by rename_client_map


lemma System_Bounded_ask: "i < Nclients
      ==> System : Always
                    {s. ALL elt : set ((ask o sub i o client) s). elt \<le> NbT}"
  apply (rule component_guaranteesD [OF rename_Client_Bounded Client_component_System])
  apply auto
  done

lemma Collect_all_imp_eq: "{x. ALL y. P y --> Q x y} = (INT y: {y. P y}. {x. Q x y})"
  apply blast
  done

text{*progress (2), step 4*}
lemma System_Bounded_allocAsk: "System : Always {s. ALL i<Nclients.
                          ALL elt : set ((sub i o allocAsk) s). elt \<le> NbT}"
  apply (auto simp add: Collect_all_imp_eq)
  apply (tactic {* rtac (Always_Int_rule [@{thm Always_allocAsk_le_ask},
    @{thm System_Bounded_ask}] RS @{thm Always_weaken}) 1 *})
  apply (auto dest: set_mono)
  done

text{*progress (2), step 5 is @{text System_Increasing_allocGiv}*}

text{*progress (2), step 6*}
(* i < Nclients ==> System : Increasing (giv o sub i o client) *)
lemmas System_Increasing_giv =  System_Follows_allocGiv [THEN Follows_Increasing1]


lemma rename_Client_Progress: "i: I
   ==> rename sysOfClient (plam x: I. rename client_map Client)
        : Increasing (giv o sub i o client)
          guarantees
          (INT h. {s. h \<le> (giv o sub i o client) s &
                            h pfixGe (ask o sub i o client) s}
                  LeadsTo {s. tokens h \<le> (tokens o rel o sub i o client) s})"
  apply rename_client_map
  apply (simp add: Client_Progress [simplified o_def])
  done


text{*progress (2), step 7*}
lemma System_Client_Progress:
  "System : (INT i : (lessThan Nclients).
            INT h. {s. h \<le> (giv o sub i o client) s &
                       h pfixGe (ask o sub i o client) s}
                LeadsTo {s. tokens h \<le> (tokens o rel o sub i o client) s})"
  apply (rule INT_I)
(*Couldn't have just used Auto_tac since the "INT h" must be kept*)
  apply (rule component_guaranteesD [OF rename_Client_Progress Client_component_System])
  apply (auto simp add: System_Increasing_giv)
  done

(*Concludes
 System : {s. k \<le> (sub i o allocGiv) s}
          LeadsTo
          {s. (sub i o allocAsk) s \<le> (ask o sub i o client) s} Int
          {s. k \<le> (giv o sub i o client) s} *)

lemmas System_lemma1 =
  Always_LeadsToD [OF System_Follows_ask [THEN Follows_Bounded]
                      System_Follows_allocGiv [THEN Follows_LeadsTo]]

lemmas System_lemma2 =
  PSP_Stable [OF System_lemma1
              System_Follows_ask [THEN Follows_Increasing1, THEN IncreasingD]]


lemma System_lemma3: "i < Nclients
      ==> System : {s. h \<le> (sub i o allocGiv) s &
                       h pfixGe (sub i o allocAsk) s}
                   LeadsTo
                   {s. h \<le> (giv o sub i o client) s &
                       h pfixGe (ask o sub i o client) s}"
  apply (rule single_LeadsTo_I)
  apply (rule_tac k1 = h and x1 = "(sub i o allocAsk) s"
         in System_lemma2 [THEN LeadsTo_weaken])
  apply auto
  apply (blast intro: trans_Ge [THEN trans_genPrefix, THEN transD] prefix_imp_pfixGe)
  done


text{*progress (2), step 8: Client i's "release" action is visible system-wide*}
lemma System_Alloc_Client_Progress: "i < Nclients
      ==> System : {s. h \<le> (sub i o allocGiv) s &
                       h pfixGe (sub i o allocAsk) s}
                   LeadsTo {s. tokens h \<le> (tokens o sub i o allocRel) s}"
  apply (rule LeadsTo_Trans)
   prefer 2
   apply (drule System_Follows_rel [THEN
     mono_tokens [THEN mono_Follows_o, THEN [2] rev_subsetD],
     THEN Follows_LeadsTo])
   apply (simp add: o_assoc)
  apply (rule LeadsTo_Trans)
   apply (cut_tac [2] System_Client_Progress)
   prefer 2
   apply (blast intro: LeadsTo_Basis)
  apply (erule System_lemma3)
  done

text{*Lifting @{text Alloc_Progress} up to the level of systemState*}

text{*progress (2), step 9*}
lemma System_Alloc_Progress:
 "System : (INT i : (lessThan Nclients).
            INT h. {s. h \<le> (sub i o allocAsk) s}
                   LeadsTo {s. h pfixLe (sub i o allocGiv) s})"
  apply (simp only: o_apply sub_def)
  apply (insert Alloc_Progress [THEN rename_guarantees_sysOfAlloc_I])
  apply (simp add: o_def del: INT_iff)
  apply (erule component_guaranteesD)
  apply (auto simp add:
    System_Increasing_allocRel [simplified sub_apply o_def]
    System_Increasing_allocAsk [simplified sub_apply o_def]
    System_Bounded_allocAsk [simplified sub_apply o_def]
    System_Alloc_Client_Progress [simplified sub_apply o_def])
  done

text{*progress (2), step 10 (final result!) *}
lemma System_Progress: "System : system_progress"
  apply (unfold system_progress_def)
  apply (cut_tac System_Alloc_Progress)
  apply (blast intro: LeadsTo_Trans
    System_Follows_allocGiv [THEN Follows_LeadsTo_pfixLe]
    System_Follows_ask [THEN Follows_LeadsTo])
  done


theorem System_correct: "System : system_spec"
  apply (unfold system_spec_def)
  apply (blast intro: System_safety System_Progress)
  done


text{* Some obsolete lemmas *}

lemma non_dummy_eq_o_funPair: "non_dummy = (% (g,a,r). (| giv = g, ask = a, rel = r |)) o
                              (funPair giv (funPair ask rel))"
  apply (rule ext)
  apply (auto simp add: o_def non_dummy_def)
  done

lemma preserves_non_dummy_eq: "(preserves non_dummy) =
      (preserves rel Int preserves ask Int preserves giv)"
  apply (simp add: non_dummy_eq_o_funPair)
  apply auto
    apply (drule_tac w1 = rel in subset_preserves_o [THEN [2] rev_subsetD])
    apply (drule_tac [2] w1 = ask in subset_preserves_o [THEN [2] rev_subsetD])
    apply (drule_tac [3] w1 = giv in subset_preserves_o [THEN [2] rev_subsetD])
    apply (auto simp add: o_def)
  done

text{*Could go to Extend.ML*}
lemma bij_fst_inv_inv_eq: "bij f ==> fst (inv (%(x, u). inv f x) z) = f z"
  apply (rule fst_inv_equalityI)
   apply (rule_tac f = "%z. (f z, ?h z) " in surjI)
   apply (simp add: bij_is_inj inv_f_f)
  apply (simp add: bij_is_surj surj_f_inv_f)
  done

end
