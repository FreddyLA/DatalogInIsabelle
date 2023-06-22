section \<open>Model Semantics\<close>

(*
  Author: Frederik Lyhne Andersen, DTU Compute, 2023
*)

theory ModelSemantics imports DatalogBase
begin

subsection \<open>Definitions\<close>

definition solve_m :: \<open>rule set \<Rightarrow> atom set\<close> (\<open>\<bbbM>\<lparr>_\<rparr>\<close>) where
  \<open>\<bbbM>\<lparr>p\<rparr> \<equiv> \<Inter>{m. m \<Turnstile>\<^sub>p p}\<close>

definition solve_m_herbrand :: \<open>rule set \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> atom set\<close> (\<open>\<bbbM>\<^sub>\<bool>\<lparr>_\<rparr>\<^bsub>_\<^esub>\<close>) where
  \<open>\<bbbM>\<^sub>\<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub> \<equiv> \<Inter>{m. m \<subseteq> \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub> \<and> m \<Turnstile>\<^sub>p p}\<close>


subsection \<open>Proofs\<close>

theorem finite_solve_m:
    \<open>wf_p p ar \<Longrightarrow> 
     safe_p p \<Longrightarrow> 
     finite \<bbbM>\<lparr>p\<rparr>\<close>
proof -
  assume a1: \<open>wf_p p ar\<close>
  assume a2: \<open>safe_p p\<close>
  then have \<open>\<exists>m. m \<Turnstile>\<^sub>p p \<and> finite m\<close>
    using a1 safe_wf_p_finite
    by simp
  then have \<open>finite (\<Inter> {m. m \<Turnstile>\<^sub>p p})\<close>
    using finite_Inter
    by auto
  then show \<open>finite \<bbbM>\<lparr>p\<rparr>\<close> 
    using solve_m_def
    by simp
qed

theorem solve_m_subset_herbrand:
    \<open>wf_p p ar \<Longrightarrow> 
     safe_p p \<Longrightarrow> 
     \<bbbM>\<lparr>p\<rparr> \<subseteq> \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub>\<close>
  unfolding solve_m_def
  using Inter_lower herbrand_sat_prog 
  by auto

theorem solve_m_wf_interp:
    \<open>wf_p p ar \<Longrightarrow> 
     safe_p p \<Longrightarrow> 
     wf_i \<bbbM>\<lparr>p\<rparr> ar\<close>
proof -
  assume a1: \<open>wf_p p ar\<close>
  assume a2: \<open>safe_p p\<close>
  have a3: \<open>wf_i \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub> ar\<close>
    using a1 herbrand_wf_i
    by simp
  have \<open>\<bbbM>\<lparr>p\<rparr> \<subseteq> \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub>\<close>
    using a1 a2 solve_m_subset_herbrand
    by simp
  then have \<open>finite \<bbbM>\<lparr>p\<rparr> \<and> (\<forall>a\<in>\<bbbM>\<lparr>p\<rparr>. ground_a a \<and> wf_a a ar)\<close>
    using wf_i_def a3 finite_subset
    by blast
  then show \<open>wf_i \<bbbM>\<lparr>p\<rparr> ar\<close>
    using wf_i_def
    by simp
qed

lemma adom_eval_herbrand:
    \<open>wf_p p ar \<Longrightarrow> 
     safe_p p \<Longrightarrow> 
     adom \<bbbM>\<lparr>p\<rparr> \<subseteq> adom \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub>\<close>
  using adom_subset solve_m_subset_herbrand 
  by auto

lemma adom_eval_prog:
    \<open>wf_p p ar \<Longrightarrow> 
     safe_p p \<Longrightarrow>
     adom \<bbbM>\<lparr>p\<rparr> \<subseteq> adom_p p\<close>
  using adom_eval_herbrand adom_herbrand_adom_p
  by blast

lemma solve_m_sat_rule:
    \<open>r \<in> p \<Longrightarrow> 
     \<bbbM>\<lparr>p\<rparr> \<Turnstile>\<^sub>r r\<close>
proof (induct r)
  case (Rule h b)
  then show ?case 
  proof -
    assume \<open>Rule h b \<in> p\<close>
    then have \<open>\<forall>x. (\<forall>r \<in> p. x \<Turnstile>\<^sub>r r) \<longrightarrow> 
              (\<forall>v. (\<forall>a\<in>set b. \<lbrakk>a\<rbrakk>\<^sub>av \<in> x) \<longrightarrow> \<lbrakk>h\<rbrakk>\<^sub>av \<in> x)\<close> 
      by auto
    then have \<open>\<forall>x v. (\<forall>a\<in>set b. (\<forall>r \<in> p. x \<Turnstile>\<^sub>r r) \<longrightarrow> \<lbrakk>a\<rbrakk>\<^sub>av \<in> x) \<longrightarrow> 
                     (\<forall>r \<in> p. x \<Turnstile>\<^sub>r r) \<longrightarrow> \<lbrakk>h\<rbrakk>\<^sub>av \<in> x\<close> 
      by simp
    then have \<open>\<forall>v. (\<forall>a\<in>set b. \<lbrakk>a\<rbrakk>\<^sub>av \<in> \<Inter> {m. \<forall>r \<in> p. m \<Turnstile>\<^sub>r r}) \<longrightarrow> 
                   \<lbrakk>h\<rbrakk>\<^sub>av \<in> \<Inter> {m. \<forall>r \<in> p. m \<Turnstile>\<^sub>r r}\<close> 
      by simp
    then have \<open>\<Inter> {m. \<forall>r \<in> p. m \<Turnstile>\<^sub>r r} \<Turnstile>\<^sub>r Rule h b\<close> 
      by simp
    then show \<open>\<bbbM>\<lparr>p\<rparr> \<Turnstile>\<^sub>r Rule h b\<close>
      using solve_m_def sat_prog_def 
      by auto
  qed
qed

theorem solve_m_sat_prog:
    \<open>\<bbbM>\<lparr>p\<rparr> \<Turnstile>\<^sub>p p\<close>
  unfolding sat_prog_def
  using solve_m_sat_rule 
  by simp

theorem solve_m_herbrand_equiv:
    \<open>wf_p p ar \<Longrightarrow> 
     safe_p p \<Longrightarrow> 
     \<bbbM>\<lparr>p\<rparr> = \<bbbM>\<^sub>\<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub>\<close>
proof
  show \<open>\<bbbM>\<lparr>p\<rparr> \<subseteq> \<bbbM>\<^sub>\<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub>\<close>
    unfolding solve_m_herbrand_def solve_m_def
    by auto
next
  assume a1: \<open>wf_p p ar\<close>
  assume a2: \<open>safe_p p\<close>
  have \<open>\<bbbM>\<lparr>p\<rparr> \<subseteq> \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub>\<close>
    using a1 a2 solve_m_subset_herbrand
    by simp
  then show \<open>\<bbbM>\<^sub>\<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub> \<subseteq> \<bbbM>\<lparr>p\<rparr>\<close> 
    using solve_m_sat_prog solve_m_herbrand_def
    by auto
qed

lemma solve_m_no_sub:
    \<open>\<not> (\<exists>m\<subset>\<bbbM>\<lparr>p\<rparr>. m \<Turnstile>\<^sub>p p)\<close>
  unfolding solve_m_def
  by auto

theorem solve_m_mini:
    \<open>\<bbbM>\<lparr>p\<rparr> \<Turnstile>\<^sub>m\<^sub>i\<^sub>n p\<close>
  unfolding min_model_def
  using solve_m_no_sub solve_m_sat_prog
  by simp

theorem solve_m_mini_unique:
    \<open>min p = \<bbbM>\<lparr>p\<rparr>\<close>
  unfolding min_def
proof (rule the_equality) 
  show \<open>\<bbbM>\<lparr>p\<rparr> \<Turnstile>\<^sub>m\<^sub>i\<^sub>n p\<close> 
    using solve_m_mini
    by simp
next 
  fix i                           
  assume a1: \<open>i \<Turnstile>\<^sub>m\<^sub>i\<^sub>n p\<close>
  then have \<open>i \<Turnstile>\<^sub>p p\<close> 
    using min_model_def
    by simp
  then have \<open>\<bbbM>\<lparr>p\<rparr> \<subseteq> i\<close> 
    using solve_m_def 
    by auto
  then have \<open>i = \<bbbM>\<lparr>p\<rparr>\<close> 
    using a1 min_model_def solve_m_sat_prog 
    by blast
  then show \<open>i \<Turnstile>\<^sub>m\<^sub>i\<^sub>n p \<Longrightarrow> i = \<bbbM>\<lparr>p\<rparr>\<close> 
    by auto
qed

theorem unique_minimal_model:
    \<open>min p \<Turnstile>\<^sub>m\<^sub>i\<^sub>n p\<close>
  using solve_m_mini solve_m_mini_unique
  by simp

lemma program_subset_model:
    \<open>p1 \<subseteq> p2 \<Longrightarrow> 
     \<bbbM>\<lparr>p1\<rparr> \<subseteq> \<bbbM>\<lparr>p2\<rparr>\<close>
  unfolding solve_m_def sat_prog_def
  by auto

lemma program_subset_sat:
    \<open>p1 \<subseteq> p2 \<Longrightarrow> 
     \<bbbM>\<lparr>p2\<rparr> \<Turnstile>\<^sub>p p1\<close>
  unfolding sat_prog_def
  using solve_m_sat_rule 
  by auto

lemma fact_in_model:
    \<open>safe_p p \<Longrightarrow> 
     Rule h [] \<in> p \<Longrightarrow> 
     h \<in> \<bbbM>\<lparr>p\<rparr>\<close>
  using solve_m_sat_prog fact_in_interp
  by simp

lemma syms_solve_m_subset_herbrand_syms:
    \<open>wf_p p ar \<Longrightarrow> 
     safe_p p \<Longrightarrow> 
     syms \<bbbM>\<lparr>p\<rparr> \<subseteq> syms \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub>\<close>
  unfolding syms_def
  using solve_m_subset_herbrand image_mono
  by auto
  
theorem syms_solve_m_subset_prog_syms:
    \<open>wf_p p ar \<Longrightarrow> 
     safe_p p \<Longrightarrow> 
     syms \<bbbM>\<lparr>p\<rparr> \<subseteq> syms_p p\<close>
  using syms_solve_m_subset_herbrand_syms syms_herbrand_in_prog_syms 
  by blast

end