theory NM_logic
  imports BA_logic
begin
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=3] (*default Nitpick settings*)


(**Neighbourhood semantics for LFIs*)

consts S1::"\<sigma>\<Rightarrow>\<sigma>" ("S\<^sub>\<not>")   (** introduces additional (unconstrained) constant *)
consts S2::"\<sigma>\<Rightarrow>\<sigma>" ("S\<^sub>\<circ>")   (** introduces additional (unconstrained) constant *)

(** Paraconsistent LFI operators:*)
definition pneg::"\<sigma>\<Rightarrow>\<sigma>"       ("\<^bold>\<not>_" [57]58)   where   "\<^bold>\<not>A  \<equiv> \<^bold>\<sim>A \<^bold>\<or> (S\<^sub>\<not> A)"
definition pcon_mbC::"\<sigma>\<Rightarrow>\<sigma>"   ("\<^bold>\<circ>_" [57]58) where  "\<^bold>\<circ>A  \<equiv> \<^bold>\<sim>(A \<^bold>\<and> S\<^sub>\<not> A) \<^bold>\<and> (S\<^sub>\<circ> A)"
definition pcon_ciw :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<circ>\<^sup>w_" [57]58) where "\<^bold>\<circ>\<^sup>wA  \<equiv> \<^bold>\<sim>(A \<^bold>\<and> \<^bold>\<not>A)"  (* for mbC-ciw*)
declare pneg_def[conn] pcon_mbC_def[conn] pcon_ciw_def[conn]

lemma pcon_rel1: "(A \<^bold>\<and> \<^bold>\<not>A) = (A \<^bold>\<and> S\<^sub>\<not> A)" unfolding conn by auto
lemma pcon_rel2: "\<^bold>\<circ>A = (\<^bold>\<circ>\<^sup>wA  \<^bold>\<and> S\<^sub>\<circ> A)" unfolding conn by simp

lemma LEM:  "A \<^bold>\<or> \<^bold>\<not>A \<^bold>\<approx> \<^bold>\<top>" unfolding conn by simp
lemma CONS: "a \<^bold>\<and> \<^bold>\<not>a \<^bold>\<and> \<^bold>\<circ>a \<^bold>\<approx> \<^bold>\<bottom>" unfolding conn by simp
lemma "A \<^bold>\<and> \<^bold>\<not>A \<^bold>\<approx> \<^bold>\<bottom>" nitpick oops (*counterexample found*)

(**The following axioms are commonly employed in the literature on LFIs to obtain stronger logics.
We explore under which conditions they can be assumed while keeping the logic boldly paraconsistent.*)
abbreviation ciw where "ciw \<equiv> \<forall>a. [\<^bold>\<turnstile> \<^bold>\<circ>a \<^bold>\<or> (a \<^bold>\<and> \<^bold>\<not>a)]"
abbreviation ci  where  "ci \<equiv> \<forall>a. [\<^bold>\<turnstile> \<^bold>\<not>\<^bold>\<circ>a \<^bold>\<rightarrow> (a \<^bold>\<and> \<^bold>\<not>a)]"
abbreviation cl  where  "cl \<equiv> \<forall>a. [\<^bold>\<turnstile> \<^bold>\<not>(a \<^bold>\<and> \<^bold>\<not>a) \<^bold>\<rightarrow> \<^bold>\<circ>a]"
abbreviation cf where "cf \<equiv> \<forall>a. [\<^bold>\<turnstile> \<^bold>\<not>\<^bold>\<not>a \<^bold>\<rightarrow> a]"
abbreviation ce where "ce \<equiv> \<forall>a. [\<^bold>\<turnstile> a \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>\<not>a]"

lemma "ciw \<longleftrightarrow> (\<forall>X. \<^bold>\<sim>(X \<^bold>\<and> S\<^sub>\<not> X) \<^bold>\<preceq> S\<^sub>\<circ> X)" unfolding conn by metis
lemma "ci \<longleftrightarrow> (\<forall>X. \<^bold>\<sim>(X \<^bold>\<and> S\<^sub>\<not> X) \<^bold>\<preceq> (S\<^sub>\<circ> X \<^bold>\<leftharpoonup> S\<^sub>\<not>(\<^bold>\<sim>(X \<^bold>\<and> S\<^sub>\<not> X) \<^bold>\<and> (S\<^sub>\<circ> X))))" unfolding conn by metis
lemma "cl \<longleftrightarrow> (\<forall>X. S\<^sub>\<not>(X \<^bold>\<and> S\<^sub>\<not> X) \<^bold>\<preceq> \<^bold>\<sim>(X \<^bold>\<and> S\<^sub>\<not> X) \<and> \<^bold>\<sim>(X \<^bold>\<and> S\<^sub>\<not> X) \<^bold>\<preceq> S\<^sub>\<circ> X)" using pcon_rel1 unfolding conn by metis
lemma "cf \<longleftrightarrow> (\<forall>X. (X \<^bold>\<leftharpoonup> (S\<^sub>\<not> X)) \<^bold>\<or> S\<^sub>\<not>(X \<^bold>\<rightarrow> (S\<^sub>\<not> X)) \<^bold>\<preceq> X)" unfolding conn by simp
lemma "ce \<longleftrightarrow> (\<forall>X. X \<^bold>\<preceq> (X \<^bold>\<leftharpoonup> (S\<^sub>\<not> X)) \<^bold>\<or> S\<^sub>\<not>(X \<^bold>\<rightarrow> (S\<^sub>\<not> X)))" unfolding conn by simp

end