(*  Title:      Pure/Pure.thy
    ID:         $Id$
    Author:     Larry Paulson and Makarius

The Pure theory.
*)

theory Pure
imports ProtoPure
begin

setup "Context.setup ()"


text{*These meta-level elimination rules facilitate the use of assumptions
that contain !! and ==>, especially in linear scripts. *}

lemma meta_mp:
  assumes major: "PROP P ==> PROP Q" and minor: "PROP P"
  shows "PROP Q"
proof -
  show "PROP Q" by (rule major [OF minor])
qed

lemma meta_spec:
  assumes major: "!!x. PROP P(x)"
  shows "PROP P(x)"
proof -
  show "PROP P(x)" by (rule major)
qed

lemmas meta_allE = meta_spec [elim_format]

end
