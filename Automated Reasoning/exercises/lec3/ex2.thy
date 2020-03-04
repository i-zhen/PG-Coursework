header {* Automated Reasoning, Exercise Sheet 2 *}

theory ex2
imports Main

begin

text {* Prove the following lemmas in Isabelle *}

lemma one: "(P \<longrightarrow> (Q \<longrightarrow> R)) \<longrightarrow> ((P \<longrightarrow> Q) \<longrightarrow> (P \<longrightarrow> R))"
apply (rule impI)
apply (rule impI)
apply (rule impI)
apply (erule impE)
apply assumption
apply (erule impE)
apply assumption
apply (erule impE)
apply assumption
apply assumption
done

lemma two: "\<not>\<not>P \<longrightarrow> P"
apply (rule impI)
apply (rule ccontr)
apply (erule notE)
apply assumption
done

lemma three: "(P \<longrightarrow> Q \<and> R) \<longrightarrow> ((P \<longrightarrow> Q) \<and> (P \<longrightarrow> R))"
apply (rule impI)
apply (rule conjI)
apply (rule impI)
apply (rule conjunct1)
apply (rule mp)
apply assumption
apply assumption
apply (rule impI)
apply (rule conjunct2)
apply (rule mp)
apply assumption
apply assumption
done

lemma four: "(\<not>P \<longrightarrow> Q) \<longrightarrow> (\<not>Q \<longrightarrow> P)"
apply (rule impI)
apply (rule impI)
apply (rule ccontr)
apply (rule notE)
apply assumption
apply (erule impE)
by assumption+

lemma five: "P \<or> \<not>P"
apply (rule disjE)
apply (rule excluded_middle)
apply (rule disjI2)
apply assumption
apply (rule disjI1)
by assumption+

text {* To fully understand the proofs you have constructed, try
drawing out the proof trees that correspond to the proof steps
accepted by Isabelle. *}

end
