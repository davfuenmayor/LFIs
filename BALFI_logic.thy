theory BALFI_logic
  imports BA_logic
begin
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=3] (*default Nitpick settings*)

(**The LFIs are a family of paraconsistent logics featuring a paraconsistent negation \<^bold>\<not>
and a consistency operator \<^bold>\<circ> that can be used to recover some classical properties
of the negation \<^bold>\<not> (in particular 'explosion').
We axiomatize below extensions of Boolean algebras with additional LFI operators (BALFIs).*)

consts pneg:: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<not>_" [57]58)
consts pcons::"\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<circ>_" [57]58)

axiomatization where
          LEM:  "a \<^bold>\<or> \<^bold>\<not>a \<^bold>\<approx> \<^bold>\<top>" and
          CONS: "a \<^bold>\<and> \<^bold>\<not>a \<^bold>\<and> \<^bold>\<circ>a \<^bold>\<approx> \<^bold>\<bottom>"


(**This negation is of course boldly paraconsistent.*)
lemma "[a, \<^bold>\<not>a \<^bold>\<turnstile> b]" nitpick oops (*countermodel*)
lemma "[a, \<^bold>\<not>a \<^bold>\<turnstile> \<^bold>\<not>b]" nitpick oops (*countermodel*)
lemma "[a, \<^bold>\<not>a \<^bold>\<turnstile>\<^sub>g b]" nitpick oops (*countermodel*) 
lemma "[a, \<^bold>\<not>a \<^bold>\<turnstile>\<^sub>g \<^bold>\<not>b]" nitpick oops (*countermodel*)

(**We can recover explosion using \<^bold>\<circ> (cf. 'principle of gentle explosion')*)
lemma "[a, \<^bold>\<not>a, \<^bold>\<circ>a \<^bold>\<turnstile> b]" by (simp add: CONS bottom_def)


(**The following axioms are commonly employed in the literature on LFIs to obtain stronger logics.
We explore under which conditions they can be assumed while keeping the logic boldly paraconsistent.*)
abbreviation ciw where "ciw \<equiv> \<forall>a. [\<^bold>\<turnstile> \<^bold>\<circ>a \<^bold>\<or> (a \<^bold>\<and> \<^bold>\<not>a)]"
abbreviation ci  where  "ci \<equiv> \<forall>a. [\<^bold>\<turnstile> \<^bold>\<not>\<^bold>\<circ>a \<^bold>\<rightarrow> (a \<^bold>\<and> \<^bold>\<not>a)]"
abbreviation cl  where  "cl \<equiv> \<forall>a. [\<^bold>\<turnstile> \<^bold>\<not>(a \<^bold>\<and> \<^bold>\<not>a) \<^bold>\<rightarrow> \<^bold>\<circ>a]"
abbreviation cf where "cf \<equiv> \<forall>a. [\<^bold>\<turnstile> \<^bold>\<not>\<^bold>\<not>a \<^bold>\<rightarrow> a]"
abbreviation ce where "ce \<equiv> \<forall>a. [\<^bold>\<turnstile> a \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>\<not>a]"
abbreviation ca_conj where "ca_conj \<equiv> \<forall>a b. [\<^bold>\<turnstile> (\<^bold>\<circ>a \<^bold>\<and> \<^bold>\<circ>b) \<^bold>\<rightarrow> \<^bold>\<circ>(a \<^bold>\<and> b)]"
abbreviation ca_disj where "ca_disj \<equiv> \<forall>a b. [\<^bold>\<turnstile> (\<^bold>\<circ>a \<^bold>\<and> \<^bold>\<circ>b) \<^bold>\<rightarrow> \<^bold>\<circ>(a \<^bold>\<or> b)]"
abbreviation ca_impl where "ca_impl \<equiv> \<forall>a b. [\<^bold>\<turnstile> (\<^bold>\<circ>a \<^bold>\<and> \<^bold>\<circ>b) \<^bold>\<rightarrow> \<^bold>\<circ>(a \<^bold>\<rightarrow> b)]"
abbreviation ca where "ca \<equiv> ca_conj \<and> ca_disj \<and> ca_impl"

lemma "ciw \<longleftrightarrow> (\<forall>a. \<^bold>\<circ>a \<^bold>\<approx> \<^bold>\<midarrow>(a \<^bold>\<and> \<^bold>\<not>a))" by (metis CONS compl_def join_def meet_def)
lemma "ci \<longleftrightarrow> (\<forall>a. \<^bold>\<not>\<^bold>\<circ>a \<^bold>\<approx> a \<^bold>\<and> \<^bold>\<not>a)" by (metis CONS LEM impl_def join_def meet_def)
lemma "cl \<longleftrightarrow> (\<forall>a. \<^bold>\<circ>a \<^bold>\<approx> \<^bold>\<not>(a \<^bold>\<and> \<^bold>\<not>a))" by (metis CONS LEM impl_def join_def meet_def)
lemma "cf \<longleftrightarrow> (\<forall>a. a \<^bold>\<and> \<^bold>\<not>\<^bold>\<not>a \<^bold>\<approx> \<^bold>\<not>\<^bold>\<not>a)" by (metis impl_def meet_def)
lemma "ce \<longleftrightarrow> (\<forall>a. a \<^bold>\<and> \<^bold>\<not>\<^bold>\<not>a \<^bold>\<approx> a)" by (metis impl_def meet_def)
lemma "ca_conj \<longleftrightarrow> (\<forall>a b. (\<^bold>\<circ>a \<^bold>\<and> \<^bold>\<circ>b) \<^bold>\<and> \<^bold>\<circ>(a \<^bold>\<and> b) \<^bold>\<approx> \<^bold>\<circ>a \<^bold>\<and> \<^bold>\<circ>b)" by (metis impl_def meet_def)
lemma "ca_disj \<longleftrightarrow> (\<forall>a b. (\<^bold>\<circ>a \<^bold>\<and> \<^bold>\<circ>b) \<^bold>\<and> \<^bold>\<circ>(a \<^bold>\<or> b) \<^bold>\<approx> \<^bold>\<circ>a \<^bold>\<and> \<^bold>\<circ>b)" by (metis impl_def meet_def)
lemma "ca_impl \<longleftrightarrow> (\<forall>a b. (\<^bold>\<circ>a \<^bold>\<and> \<^bold>\<circ>b) \<^bold>\<and> \<^bold>\<circ>(a \<^bold>\<rightarrow> b) \<^bold>\<approx> \<^bold>\<circ>a \<^bold>\<and> \<^bold>\<circ>b)" by (metis impl_def meet_def)

lemma "cl \<and> ce \<longrightarrow> (\<forall>a. [a \<^bold>\<turnstile> \<^bold>\<circ>a])" using CONS oops (*TODO*)


lemma "cl \<and> ci" nitpick[satisfy] oops (*TODO*)
end