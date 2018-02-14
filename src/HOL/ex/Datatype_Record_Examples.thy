theory Datatype_Record_Examples
imports "HOL-Library.Datatype_Records"
begin

text \<open>Standard usage\<close>

datatype_record ('a, 'b) foo =
  field_1 :: 'a
  field_2 :: 'b

lemma "\<lparr> field_1 = 3, field_2 = () \<rparr> = (make_foo 3 () :: (nat, unit) foo)" ..

lemma "(make_foo a b) \<lparr> field_1 := y \<rparr> = make_foo y b"
  by (simp add: datatype_record_update)

lemma "(make_foo a b) \<lparr> foo.field_1 := y \<rparr> = make_foo y b"
  by (simp add: datatype_record_update)

text \<open>Existing datatypes\<close>

datatype x = X (a: int) (b: int)

lemma "\<lparr> a = 1, b = 2 \<rparr> = X 1 2" ..

local_setup \<open>Datatype_Records.mk_update_defs @{type_name x}\<close>

lemma "(X 1 2) \<lparr> b := 3 \<rparr> = X 1 3"
  by (simp add: datatype_record_update)

text \<open>Nested recursion\<close>

datatype_record 'a container =
  content :: "'a option"

datatype 'a contrived = Contrived "'a contrived container"

term "Contrived \<lparr> content = None \<rparr>"

text \<open>Supports features of @{command datatype}\<close>

datatype_record (plugins del: code) (dead 'a :: finite, b_set: 'b) rec =
  field_1 :: 'a
  field_2 :: 'b

lemma "b_set \<lparr> field_1 = True, field_2 = False \<rparr> = {False}"
  by simp

end