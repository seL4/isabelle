chapter \<open>Isabelle Verification of a protocol using IOA\<close>

theory Overview
  imports IOA.IOA
begin

section \<open>The System\<close>

text \<open>
The system being proved correct is a parallel composition of 4 processes:

    Sender || Schannel || Receiver || Rchannel

Accordingly, the system state is a 4-tuple:

    (Sender_state, Schannel_state, Receiver_state, Rchannel_state)
\<close>


section \<open>Packets\<close>

text \<open>
The objects going over the medium from Sender to Receiver are modelled
with the type

    'm packet = bool \<times> 'm

This expresses that messages (modelled by polymorphic type \<open>'m\<close>) are
sent with a single header bit. Packet fields are accessed by

    hdr<b,m> = b
    mesg<b,m> = m
\<close>


section \<open>The Sender\<close>

text \<open>
The state of the process "Sender" is a 5-tuple:

     1. messages : 'm list        (* sq *)
     2. sent     : bool multiset  (* ssent *)
     3. received : bool multiset  (* srcvd *)
     4. header   : bool           (* sbit *)
     5. mode     : bool           (* ssending *)
\<close>


section \<open>The Receiver\<close>

text \<open>
The state of the process "Receiver" is a 5-tuple:

     1. messages    : 'm list              (* rq *)
     2. replies     : bool multiset        (* rsent *)
     3. received    : 'm packet multiset   (* rrcvd *)
     4. header      : bool                 (* rbit *)
     5. mode        : bool                 (* rsending *)
\<close>


section \<open>The Channels\<close>

text \<open>
The Sender and Receiver each have a proprietary channel, named
"Schannel" and "Rchannel" respectively. The messages sent by the Sender
and Receiver are never lost, but the channels may mix them
up. Accordingly, multisets are used in modelling the state of the
channels. The state of "Schannel" is modelled with the following type:

    'm packet multiset

The state of "Rchannel" is modelled with the following type:

    bool multiset

This expresses that replies from the Receiver are just one bit.

Both Channels are instances of an abstract channel, that is modelled with
the type

    'a multiset.
\<close>


section \<open>The events\<close>

text \<open>
An `execution' of the system is modelled by a sequence of

    <system_state, action, system_state>

transitions. The actions, or events, of the system are described by the
following ML-style datatype declaration:

    'm action = S_msg ('m)           (* Rqt for Sender to send mesg      *)
              | R_msg ('m)           (* Mesg taken from Receiver's queue *)
              | S_pkt_sr ('m packet) (* Packet arrives in Schannel       *)
              | R_pkt_sr ('m packet) (* Packet leaves Schannel           *)
              | S_pkt_rs (bool)      (* Packet arrives in Rchannel       *)
              | R_pkt_rs (bool)      (* Packet leaves Rchannel           *)
              | C_m_s                (* Change mode in Sender            *)
              | C_m_r                (* Change mode in Receiver          *)
              | C_r_s                (* Change round in Sender           *)
              | C_r_r ('m)           (* Change round in Receiver         *)
\<close>


section \<open>The Specification\<close>

text \<open>
The abstract description of system behaviour is given by defining an
IO/automaton named "Spec". The state of Spec is a message queue,
modelled as an "'m list". The only actions performed in the abstract
system are: "S_msg(m)" (putting message "m" at the end of the queue);
and "R_msg(m)" (taking message "m" from the head of the queue).
\<close>


section \<open>The Verification\<close>

text \<open>
The verification proceeds by showing that a certain mapping ("hom") from
the concrete system state to the abstract system state is a `weak
possibilities map` from "Impl" to "Spec".

    hom : (S_state * Sch_state * R_state * Rch_state) -> queue

The verification depends on several system invariants that relate the
states of the 4 processes. These invariants must hold in all reachable
states of the system. These invariants are difficult to make sense of;
however, we attempt to give loose English paraphrases of them.
\<close>


subsection \<open>Invariant 1\<close>

text \<open>
This expresses that no packets from the Receiver to the Sender are
dropped by Rchannel. The analogous statement for Schannel is also true.

    \<forall>b. R.replies b = S.received b + Rch b
    \<and>
    \<forall>pkt. S.sent(hdr(pkt)) = R.received(hdr(b)) + Sch(pkt)
\<close>


subsection \<open>Invariant 2\<close>

text \<open>
This expresses a complicated relationship about how many messages are
sent and header bits.

    R.header = S.header
    \<and> S.mode = SENDING
    \<and> R.replies (flip S.header) \<subseteq> S.sent (flip S.header)
    \<and> S.sent (flip S.header) \<subseteq> R.replies header
    OR
    R.header = flip S.header
    \<and> R.mode = SENDING
    \<and> S.sent (flip S.header) \<subseteq> R.replies S.header
    \<and> R.replies S.header \<subseteq> S.sent S.header
\<close>


subsection \<open>Invariant 3\<close>

text \<open>
The number of incoming messages in the Receiver plus the number of those
messages in transit (in Schannel) is not greater than the number of
replies, provided the message isn't current and the header bits agree.

    let mesg = <S.header, m>
    in
    R.header = S.header
    \<Longrightarrow>
    \<forall>m. (S.messages = [] \<or> m \<noteq> hd S.messages)
        \<Longrightarrow> R.received mesg + Sch mesg \<subseteq> R.replies (flip S.header)
\<close>


subsection \<open>Invariant 4\<close>

text \<open>
If the headers are opposite, then the Sender queue has a message in it.

    R.header = flip S.header \<Longrightarrow> S.messages \<noteq> []
\<close>

end
