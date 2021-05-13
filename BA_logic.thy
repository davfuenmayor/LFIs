theory BA_logic
  imports Main
begin
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=3] (*default Nitpick settings*)

(**We introduce a type w for the domain of points (aka. 'worlds', 'states', etc.).
\<sigma> is a type alias for sets of points (i.e. propositions) encoded as characteristic functions.*)
typedecl w                  
type_synonym \<sigma> = "w\<Rightarrow>bool"

(**We start with an ordered algebra,*)
abbreviation sequ::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" (infixr "\<^bold>\<approx>" 45) where "A \<^bold>\<approx> B \<equiv> \<forall>w. (A w) \<longleftrightarrow> (B w)"
abbreviation subs::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" (infixr "\<^bold>\<preceq>" 45) where "A \<^bold>\<preceq> B \<equiv> \<forall>w. (A w) \<longrightarrow> (B w)"
abbreviation sups::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" (infixr "\<^bold>\<succeq>" 45) where "B \<^bold>\<succeq> A \<equiv> A \<^bold>\<preceq> B"

(**define meet and join by reusing HOL metalogical conjunction and disjunction,*)
definition meet::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<^bold>\<and>" 54) where "A \<^bold>\<and> B \<equiv> \<lambda>w. (A w) \<and> (B w)"
definition join::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<^bold>\<or>" 53) where "A \<^bold>\<or> B \<equiv> \<lambda>w. (A w) \<or> (B w)"

(**and introduce further operations, thus obtaining a Boolean algebra.*)
definition top::"\<sigma>" ("\<^bold>\<top>")    where "\<^bold>\<top> \<equiv> \<lambda>w. True"
definition bottom::"\<sigma>" ("\<^bold>\<bottom>") where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"
definition impl::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<^bold>\<rightarrow>" 51) where "A \<^bold>\<rightarrow> B \<equiv> \<lambda>w. (A w)\<longrightarrow>(B w)"
definition dimp::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<^bold>\<leftrightarrow>" 51) where "A \<^bold>\<leftrightarrow> B \<equiv> \<lambda>w. (A w)\<longleftrightarrow>(B w)"
definition diff::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<^bold>\<leftharpoonup>" 51) where "A \<^bold>\<leftharpoonup> B \<equiv> \<lambda>w. (A w) \<and> \<not>(B w)"
definition compl::"\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<midarrow>_" [57]58) where "\<^bold>\<midarrow>A  \<equiv> \<lambda>w. \<not>(A w)"

(**In fact the algebra is atomic (because of the presence of primitive equality in HOL)
This indirect restriction to atomic algebras does not influence our results
(see arxiv.org/abs/2104.04284 for a discussion).*)
definition "atom a \<equiv> \<not>(a \<^bold>\<approx> \<^bold>\<bottom>) \<and> (\<forall>p. a \<^bold>\<preceq> p \<or> a \<^bold>\<preceq> \<^bold>\<midarrow>p)"
lemma atomic: "\<forall>w. \<exists>q. q w \<and> atom(q)" using the_sym_eq_trivial by (metis (full_types) atom_def compl_def bottom_def)


(**Our aim is to obtain a complete Boolean algebra which we can use to interpret
quantified formulas. 
So we start by defining infinite meet (infimum) and infinite join (supremum) operations,*)
definition infimum:: "(\<sigma>\<Rightarrow>bool)\<Rightarrow>\<sigma>" ("\<^bold>\<And>_") where "\<^bold>\<And>S \<equiv> \<lambda>w. \<forall>X. S X \<longrightarrow> X w"
definition supremum::"(\<sigma>\<Rightarrow>bool)\<Rightarrow>\<sigma>" ("\<^bold>\<Or>_") where "\<^bold>\<Or>S \<equiv> \<lambda>w. \<exists>X. S X  \<and>  X w"

(**and show that the lattice-reduct (and therefore the Boolean algebra) is complete.*)
abbreviation "upper_bound U S \<equiv> \<forall>X. (S X) \<longrightarrow> X \<^bold>\<preceq> U"
abbreviation "lower_bound L S \<equiv> \<forall>X. (S X) \<longrightarrow> L \<^bold>\<preceq> X"
abbreviation "is_supremum U S \<equiv> upper_bound U S \<and> (\<forall>X. upper_bound X S \<longrightarrow> U \<^bold>\<preceq> X)"
abbreviation "is_infimum  L S \<equiv> lower_bound L S \<and> (\<forall>X. lower_bound X S \<longrightarrow> X \<^bold>\<preceq> L)"

lemma sup_char: "is_supremum \<^bold>\<Or>S S" unfolding supremum_def by auto
lemma sup_ext: "\<forall>S. \<exists>X. is_supremum X S" by (metis supremum_def)
lemma inf_char: "is_infimum \<^bold>\<And>S S" unfolding infimum_def by auto
lemma inf_ext: "\<forall>S. \<exists>X. is_infimum X S" by (metis infimum_def)

(**We introduce an useful construct for the range of a function (with codomain \<sigma>),*)
definition funRange::"('t\<Rightarrow>\<sigma>)\<Rightarrow>(\<sigma>\<Rightarrow>bool)" ("Ra(_)") where "Ra(\<pi>) \<equiv> \<lambda>Y. \<exists>x. (\<pi> x) = Y"

(**and use it to encode quantification over individuals of any type (exploiting type polymorphism): *)  
definition qforall::"('t\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<forall>_" [55]56) where "\<^bold>\<forall>\<pi> \<equiv> \<^bold>\<And>Ra(\<pi>)"
definition qexists::"('t\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<exists>_" [55]56) where "\<^bold>\<exists>\<pi> \<equiv> \<^bold>\<Or>Ra(\<pi>)"
(**To improve readability, we introduce for them an useful binder notation.*)
abbreviation mforallB (binder"\<^bold>\<forall>"[55]56) where "\<^bold>\<forall>X. \<pi> X \<equiv> \<^bold>\<forall>\<pi>"
abbreviation mexistsB (binder"\<^bold>\<exists>"[55]56) where "\<^bold>\<exists>X. \<pi> X \<equiv> \<^bold>\<exists>\<pi>"

(**In fact, we can prove the following interesting relationships: *)
lemma Ra_all: "\<^bold>\<forall>\<pi> = (\<lambda>w. \<forall>X. (\<pi> X) w)" by (metis (full_types) funRange_def infimum_def qforall_def)
lemma Ra_ex:  "\<^bold>\<exists>\<pi> = (\<lambda>w. \<exists>X. (\<pi> X) w)" by (metis funRange_def qexists_def supremum_def)

(**Logical validity can be defined as truth in all worlds/points (i.e. as denoting the top element)*)
abbreviation gtrue::"\<sigma>\<Rightarrow>bool" ("[\<^bold>\<turnstile> _]") where  "[\<^bold>\<turnstile>  A] \<equiv> \<forall>w. A w"   
lemma gtrue_def: "[\<^bold>\<turnstile> A] \<equiv> A \<^bold>\<approx> \<^bold>\<top>"  by (simp add: top_def)

(**When defining a logic over an existing algebra we have two choices: a global (truth preserving)
and a local (degree preserving) notion of logical consequence. For LFIs we mostly work with the latter.*)
abbreviation conseq_global1::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" ("[_ \<^bold>\<turnstile>\<^sub>g _]") where "[A \<^bold>\<turnstile>\<^sub>g B] \<equiv> [\<^bold>\<turnstile> A] \<longrightarrow> [\<^bold>\<turnstile> B]"
abbreviation conseq_global2::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" ("[_,_ \<^bold>\<turnstile>\<^sub>g _]") where "[A\<^sub>1, A\<^sub>2 \<^bold>\<turnstile>\<^sub>g B] \<equiv> [\<^bold>\<turnstile> A\<^sub>1] \<and> [\<^bold>\<turnstile> A\<^sub>2] \<longrightarrow> [\<^bold>\<turnstile> B]"
abbreviation conseq_global3::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" ("[_,_,_ \<^bold>\<turnstile>\<^sub>g _]") where "[A\<^sub>1, A\<^sub>2, A\<^sub>3 \<^bold>\<turnstile>\<^sub>g B] \<equiv> [\<^bold>\<turnstile> A\<^sub>1] \<and> [\<^bold>\<turnstile> A\<^sub>2] \<and> [\<^bold>\<turnstile> A\<^sub>3] \<longrightarrow> [\<^bold>\<turnstile> B]"
abbreviation conseq_local1::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" ("[_ \<^bold>\<turnstile> _]") where "[A \<^bold>\<turnstile> B] \<equiv> A \<^bold>\<preceq> B"
abbreviation conseq_local2::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" ("[_,_ \<^bold>\<turnstile> _]") where "[A\<^sub>1, A\<^sub>2 \<^bold>\<turnstile> B] \<equiv> A\<^sub>1 \<^bold>\<and> A\<^sub>2 \<^bold>\<preceq> B"
abbreviation conseq_local3::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" ("[_,_,_ \<^bold>\<turnstile> _]") where "[A\<^sub>1, A\<^sub>2, A\<^sub>3 \<^bold>\<turnstile> B] \<equiv> A\<^sub>1 \<^bold>\<and> A\<^sub>2 \<^bold>\<and> A\<^sub>3 \<^bold>\<preceq> B"
(*add more as the need arises...*)

end