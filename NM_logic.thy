theory NM_logic
  imports BA_logic
begin
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=3] (*default Nitpick settings*)


(**Neighbourhood semantics for LFIs*)


(* lemma "cl \<and> ce \<longrightarrow> (\<forall>a. [a \<^bold>\<turnstile> \<^bold>\<circ>a])" using CONS oops (*TODO*) *)
(* lemma "cf \<and> ci \<longrightarrow> cl" using LEM CONS oops (*TODO*) *)

end