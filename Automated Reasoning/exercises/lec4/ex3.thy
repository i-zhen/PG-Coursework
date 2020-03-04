header {* Automated Reasoning, Exercise Sheet 3 *}

theory ex3
imports Main

begin

text {* Prove the following lemmas in Isabelle *}

text {* The following tautology is known as "modus tollens". According
        to Wikipedia, this is Latin for "the way that denies by
        denying" *}
lemma one : "(P \<longrightarrow> Q) \<Longrightarrow> \<not> Q \<longrightarrow> \<not> P"
apply (rule impI)
apply (rule notI)
apply (erule notE)
apply (erule impE)
by assumption+


text {* This lemma can be either be proved directly, or can be proved
        more quickly by using 'cut_tac' with the lemma above *}
lemma two : "\<not> (P \<or> Q) \<longrightarrow> \<not> P"
apply (rule impI)
apply (rule notI)
apply (erule notE)
apply (rule disjI1)
apply assumption
done

lemma two2 : "\<not> (P \<or> Q) \<longrightarrow> \<not> P"
apply (cut_tac P="P" and Q="P\<or>Q" in one)
apply (rule impI)
apply (rule disjI1)
by assumption+


text {* The following lemma is the symmetric version of 'two'. We will
        use both in the final lemma below. *}
lemma three : "\<not> (P \<or> Q) \<longrightarrow> \<not> Q"
apply (cut_tac P="Q" and Q="P\<or>Q" in one)
apply (rule impI)
apply (rule disjI2)
by assumption+

text {* The following lemma can now be proved by using the lemmas
        'two' and 'three'. *}
lemma four : "\<not> (P \<or> Q) \<longleftrightarrow> (\<not> P \<and> \<not> Q)"
apply (rule iffI)
apply (rule conjI)
apply (cut_tac P="P" and Q="Q" in two)
apply (erule impE)
apply assumption
apply assumption
apply (cut_tac P="P" and Q="Q" in three)
apply (erule impE)
apply assumption
apply assumption
apply (erule conjE)
apply (rule notI)
apply (erule disjE)
apply (erule_tac P=P in notE)
apply assumption
apply (erule_tac P=Q in notE)
apply assumption
done

end