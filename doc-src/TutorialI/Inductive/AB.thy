theory AB = Main:;

datatype alfa = a | b;

lemma [simp]: "(x ~= a) = (x = b) & (x ~= b) = (x = a)";
apply(case_tac x);
by(auto);

consts S :: "alfa list set"
       A :: "alfa list set"
       B :: "alfa list set";

inductive S A B
intros
"[] : S"
"w : A ==> b#w : S"
"w : B ==> a#w : S"

"w : S ==> a#w : A"
"[| v:A; w:A |] ==> b#v@w : A"

"w : S ==> b#w : B"
"[| v:B; w:B |] ==> a#v@w : B";

thm S_A_B.induct[no_vars];

lemma "(w : S --> size[x:w. x=a] = size[x:w. x=b]) &
       (w : A --> size[x:w. x=a] = size[x:w. x=b] + 1) &
       (w : B --> size[x:w. x=b] = size[x:w. x=a] + 1)";
apply(rule S_A_B.induct);
by(auto);

lemma intermed_val[rule_format(no_asm)]:
 "(!i<n. abs(f(i+1) - f i) <= #1) --> 
  f 0 <= k & k <= f n --> (? i <= n. f i = (k::int))";
apply(induct n);
 apply(simp);
 apply(arith);
apply(rule);
apply(erule impE);
 apply(simp);
apply(rule);
apply(erule_tac x = n in allE);
apply(simp);
apply(case_tac "k = f(n+1)");
 apply(force);
apply(erule impE);
 apply(simp add:zabs_def split:split_if_asm);
 apply(arith);
by(blast intro:le_SucI);

lemma step1: "ALL i < size w.
  abs((int(size[x:take (i+1) w . P x]) - int(size[x:take (i+1) w . ~P x])) -
      (int(size[x:take i w . P x]) - int(size[x:take i w . ~P x]))) <= #1";
apply(induct w);
 apply(simp);
apply(simp add:take_Cons split:nat.split);
apply(clarsimp);
apply(rule conjI);
 apply(clarify);
 apply(erule allE);
 apply(erule impE);
  apply(assumption);
 apply(arith);
apply(clarify);
apply(erule allE);
apply(erule impE);
 apply(assumption);
by(arith);


lemma part1:
 "size[x:w. P x] = Suc(Suc(size[x:w. ~P x])) ==>
  EX i<=size w. size[x:take i w. P x] = size[x:take i w. ~P x]+1";
apply(insert intermed_val[OF step1, of "P" "w" "#1"]);
apply(simp);
apply(erule exE);
apply(rule_tac x=i in exI);
apply(simp);
apply(rule int_int_eq[THEN iffD1]);
apply(simp);
by(arith);

lemma part2:
"[| size[x:take i xs @ drop i xs. P x] = size[x:take i xs @ drop i xs. ~P x]+2;
    size[x:take i xs. P x] = size[x:take i xs. ~P x]+1 |]
 ==> size[x:drop i xs. P x] = size[x:drop i xs. ~P x]+1";
by(simp del:append_take_drop_id);

lemmas [simp] = S_A_B.intros;

lemma "(size[x:w. x=a] = size[x:w. x=b] --> w : S) &
       (size[x:w. x=a] = size[x:w. x=b] + 1 --> w : A) &
       (size[x:w. x=b] = size[x:w. x=a] + 1 --> w : B)";
apply(induct_tac w rule: length_induct);
apply(case_tac "xs");
 apply(simp);
apply(simp);
apply(rule conjI);
 apply(clarify);
 apply(frule part1[of "%x. x=a", simplified]);
 apply(erule exE);
 apply(erule conjE);
 apply(drule part2[of "%x. x=a", simplified]);
  apply(assumption);
 apply(rule_tac n1=i and t=list in subst[OF append_take_drop_id]);
 apply(rule S_A_B.intros);
  apply(force simp add:min_less_iff_disj);
 apply(force split add: nat_diff_split);
apply(clarify);
apply(frule part1[of "%x. x=b", simplified]);
apply(erule exE);
apply(erule conjE);
apply(drule part2[of "%x. x=b", simplified]);
 apply(assumption);
apply(rule_tac n1=i and t=list in subst[OF append_take_drop_id]);
apply(rule S_A_B.intros);
 apply(force simp add:min_less_iff_disj);
by(force simp add:min_less_iff_disj split add: nat_diff_split);

end;
