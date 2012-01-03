(*  Title:      HOL/Record_Benchmark/Record_Benchmark.thy
    Author:     Norbert Schirmer, DFKI
*)

header {* Benchmark for large record *}

theory Record_Benchmark
imports Main
begin

declare [[record_timing]]

record many_A =
A000::nat
A001::nat
A002::nat
A003::nat
A004::nat
A005::nat
A006::nat
A007::nat
A008::nat
A009::nat
A010::nat
A011::nat
A012::nat
A013::nat
A014::nat
A015::nat
A016::nat
A017::nat
A018::nat
A019::nat
A020::nat
A021::nat
A022::nat
A023::nat
A024::nat
A025::nat
A026::nat
A027::nat
A028::nat
A029::nat
A030::nat
A031::nat
A032::nat
A033::nat
A034::nat
A035::nat
A036::nat
A037::nat
A038::nat
A039::nat
A040::nat
A041::nat
A042::nat
A043::nat
A044::nat
A045::nat
A046::nat
A047::nat
A048::nat
A049::nat
A050::nat
A051::nat
A052::nat
A053::nat
A054::nat
A055::nat
A056::nat
A057::nat
A058::nat
A059::nat
A060::nat
A061::nat
A062::nat
A063::nat
A064::nat
A065::nat
A066::nat
A067::nat
A068::nat
A069::nat
A070::nat
A071::nat
A072::nat
A073::nat
A074::nat
A075::nat
A076::nat
A077::nat
A078::nat
A079::nat
A080::nat
A081::nat
A082::nat
A083::nat
A084::nat
A085::nat
A086::nat
A087::nat
A088::nat
A089::nat
A090::nat
A091::nat
A092::nat
A093::nat
A094::nat
A095::nat
A096::nat
A097::nat
A098::nat
A099::nat
A100::nat
A101::nat
A102::nat
A103::nat
A104::nat
A105::nat
A106::nat
A107::nat
A108::nat
A109::nat
A110::nat
A111::nat
A112::nat
A113::nat
A114::nat
A115::nat
A116::nat
A117::nat
A118::nat
A119::nat
A120::nat
A121::nat
A122::nat
A123::nat
A124::nat
A125::nat
A126::nat
A127::nat
A128::nat
A129::nat
A130::nat
A131::nat
A132::nat
A133::nat
A134::nat
A135::nat
A136::nat
A137::nat
A138::nat
A139::nat
A140::nat
A141::nat
A142::nat
A143::nat
A144::nat
A145::nat
A146::nat
A147::nat
A148::nat
A149::nat
A150::nat
A151::nat
A152::nat
A153::nat
A154::nat
A155::nat
A156::nat
A157::nat
A158::nat
A159::nat
A160::nat
A161::nat
A162::nat
A163::nat
A164::nat
A165::nat
A166::nat
A167::nat
A168::nat
A169::nat
A170::nat
A171::nat
A172::nat
A173::nat
A174::nat
A175::nat
A176::nat
A177::nat
A178::nat
A179::nat
A180::nat
A181::nat
A182::nat
A183::nat
A184::nat
A185::nat
A186::nat
A187::nat
A188::nat
A189::nat
A190::nat
A191::nat
A192::nat
A193::nat
A194::nat
A195::nat
A196::nat
A197::nat
A198::nat
A199::nat
A200::nat
A201::nat
A202::nat
A203::nat
A204::nat
A205::nat
A206::nat
A207::nat
A208::nat
A209::nat
A210::nat
A211::nat
A212::nat
A213::nat
A214::nat
A215::nat
A216::nat
A217::nat
A218::nat
A219::nat
A220::nat
A221::nat
A222::nat
A223::nat
A224::nat
A225::nat
A226::nat
A227::nat
A228::nat
A229::nat
A230::nat
A231::nat
A232::nat
A233::nat
A234::nat
A235::nat
A236::nat
A237::nat
A238::nat
A239::nat
A240::nat
A241::nat
A242::nat
A243::nat
A244::nat
A245::nat
A246::nat
A247::nat
A248::nat
A249::nat
A250::nat
A251::nat
A252::nat
A253::nat
A254::nat
A255::nat
A256::nat
A257::nat
A258::nat
A259::nat
A260::nat
A261::nat
A262::nat
A263::nat
A264::nat
A265::nat
A266::nat
A267::nat
A268::nat
A269::nat
A270::nat
A271::nat
A272::nat
A273::nat
A274::nat
A275::nat
A276::nat
A277::nat
A278::nat
A279::nat
A280::nat
A281::nat
A282::nat
A283::nat
A284::nat
A285::nat
A286::nat
A287::nat
A288::nat
A289::nat
A290::nat
A291::nat
A292::nat
A293::nat
A294::nat
A295::nat
A296::nat
A297::nat
A298::nat
A299::nat

record many_B = many_A +
B000::nat
B001::nat
B002::nat
B003::nat
B004::nat
B005::nat
B006::nat
B007::nat
B008::nat
B009::nat
B010::nat
B011::nat
B012::nat
B013::nat
B014::nat
B015::nat
B016::nat
B017::nat
B018::nat
B019::nat
B020::nat
B021::nat
B022::nat
B023::nat
B024::nat
B025::nat
B026::nat
B027::nat
B028::nat
B029::nat
B030::nat

lemma "A155 (r\<lparr>A255:=x\<rparr>) = A155 r"
  by simp

lemma "A155 (r\<lparr>A255:=x,A253:=y,A255:=z \<rparr>) = A155 r"
  by simp

lemma "(r\<lparr>A255:=x,A253:=y,A255:=z \<rparr>) = r\<lparr>A253:=y,A255:=z\<rparr>"
  by simp

lemma "(r\<lparr>A255:=x,A253:=y,A255:=z \<rparr>) = r\<lparr>A253:=y,A255:=z\<rparr>"
  apply (tactic {* simp_tac (HOL_basic_ss addsimprocs [Record.upd_simproc]) 1*})
  done

lemma "(\<forall>r. P (A155 r)) \<longrightarrow> (\<forall>x. P x)"
  apply (tactic {* simp_tac (HOL_basic_ss addsimprocs [Record.split_simproc (K ~1)]) 1*})
  apply simp
  done

lemma "(\<forall>r. P (A155 r)) \<longrightarrow> (\<forall>x. P x)"
  apply (tactic {* Record.split_simp_tac [] (K ~1) 1*})
  apply simp
  done

lemma "(\<exists>r. P (A155 r)) \<longrightarrow> (\<exists>x. P x)"
  apply (tactic {* simp_tac (HOL_basic_ss addsimprocs [Record.split_simproc (K ~1)]) 1*})
  apply simp
  done

lemma "(\<exists>r. P (A155 r)) \<longrightarrow> (\<exists>x. P x)"
  apply (tactic {* Record.split_simp_tac [] (K ~1) 1*})
  apply simp
  done

lemma "\<And>r. P (A155 r) \<Longrightarrow> (\<exists>x. P x)"
  apply (tactic {* simp_tac (HOL_basic_ss addsimprocs [Record.split_simproc (K ~1)]) 1*})
  apply auto
  done

lemma "\<And>r. P (A155 r) \<Longrightarrow> (\<exists>x. P x)"
  apply (tactic {* Record.split_simp_tac [] (K ~1) 1*})
  apply auto
  done

lemma "P (A155 r) \<Longrightarrow> (\<exists>x. P x)"
  apply (tactic {* Record.split_simp_tac [] (K ~1) 1*})
  apply auto
  done

lemma fixes r shows "P (A155 r) \<Longrightarrow> (\<exists>x. P x)"
  apply (tactic {* Record.split_simp_tac [] (K ~1) 1*})
  apply auto
  done


notepad
begin
  fix P r
  assume "P (A155 r)"
  then have "\<exists>x. P x"
    apply -
    apply (tactic {* Record.split_simp_tac [] (K ~1) 1*})
    apply auto 
    done
end


lemma "\<exists>r. A155 r = x"
  apply (tactic {*simp_tac (HOL_basic_ss addsimprocs [Record.ex_sel_eq_simproc]) 1*})
  done


end