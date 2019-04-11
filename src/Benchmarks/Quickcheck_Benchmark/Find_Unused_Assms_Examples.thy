theory Find_Unused_Assms_Examples
imports Complex_Main
begin

section \<open>Arithmetics\<close>

context notes [[quickcheck_finite_types = false]]
begin
  find_unused_assms Divides
  find_unused_assms GCD
  find_unused_assms Real
end


section \<open>Set Theory\<close>

context notes [[quickcheck_finite_types = true]]
begin
  find_unused_assms Fun
  find_unused_assms Relation
  find_unused_assms Set
  find_unused_assms Wellfounded
end


section \<open>Datatypes\<close>

context notes [[quickcheck_finite_types = true]]
begin
  find_unused_assms List
  find_unused_assms Map
end

end
