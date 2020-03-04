header {* AR, Exercise Sheet 4 *}

theory ex4
imports Main

begin

lemma one : "(\<forall>x. P x \<longrightarrow> Q) \<longrightarrow> (\<exists>x. P x \<longrightarrow> Q)"
apply (rule impI)
apply (rule exI)
apply (erule allE)
apply assumption
done

lemma two : "\<not>(\<exists>x. P x)\<longrightarrow>(\<forall>x. \<not>P x)"
apply (rule impI)
apply (rule allI)
apply (rule notI)
apply (erule_tac P="(\<exists>x. P x)" in notE)
apply (rule_tac x="x" in exI)
apply assumption
done

lemma three : "\<not>(\<forall> x. P x) \<Longrightarrow> \<exists> x. \<not>P x"
apply (rule ccontr)
apply (erule notE)
apply (rule allI)
apply (rule ccontr)
apply (erule notE)
apply (rule_tac x=x in exI)
apply assumption
done

end