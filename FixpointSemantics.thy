section \<open>Fixpoint Semantics\<close>

(*
  Author: Frederik Lyhne Andersen, DTU Compute, 2023
*)

theory FixpointSemantics imports ModelSemantics
begin

subsection \<open>Definitions\<close>

primrec imm_conseq_r :: \<open>atom set \<Rightarrow> rule \<Rightarrow> atom set\<close> (\<open>\<bbbT>\<^sub>r\<lparr>_, _\<rparr>\<close>) where
  \<open>\<bbbT>\<^sub>r\<lparr>i, Rule h b\<rparr> = {\<lbrakk>h\<rbrakk>\<^sub>av | v. \<forall>a \<in> set b. \<lbrakk>a\<rbrakk>\<^sub>av \<in> i}\<close>

definition imm_conseq_p :: \<open>atom set \<Rightarrow> rule set \<Rightarrow> atom set\<close> (\<open>\<bbbT>\<^sub>p\<lparr>_, _\<rparr>\<close>) where
  \<open>\<bbbT>\<^sub>p\<lparr>i, p\<rparr> \<equiv> \<Union>r \<in> p. \<bbbT>\<^sub>r\<lparr>i, r\<rparr>\<close>

primrec imm_conseq_p_iter :: \<open>nat \<Rightarrow> atom set \<Rightarrow> rule set \<Rightarrow> atom set\<close> (\<open>\<bbbT>\<^sub>p\<^bsup>_\<^esup>\<lparr>_, _\<rparr>\<close>) where
  \<open>\<bbbT>\<^sub>p\<^bsup>0\<^esup>\<lparr>i, p\<rparr> = i\<close> |
  \<open>\<bbbT>\<^sub>p\<^bsup>Suc n\<^esup>\<lparr>i, p\<rparr> = \<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>\<bbbT>\<^sub>p\<lparr>i, p\<rparr> \<union> i, p\<rparr>\<close>

definition solve_f :: \<open>rule set \<Rightarrow> atom set\<close> (\<open>\<bbbT>\<^sub>p\<^sup>\<omega>\<lparr>_\<rparr>\<close>) where
  \<open>\<bbbT>\<^sub>p\<^sup>\<omega>\<lparr>p\<rparr> = \<bbbT>\<^sub>p\<^bsup>card (min p)\<^esup>\<lparr>{}, p\<rparr>\<close>


subsection \<open>Proofs\<close>

subsubsection \<open>Monotonicity and least fixpoint\<close>

lemma imm_conseq_rule_mono:
  \<open>i \<subseteq> j \<Longrightarrow>
   \<bbbT>\<^sub>r\<lparr>i, r\<rparr> \<subseteq> \<bbbT>\<^sub>r\<lparr>j, r\<rparr>\<close>
  by (induct r) auto

theorem imm_conseq_p_mono:
  \<open>i \<subseteq> j \<Longrightarrow>
   \<bbbT>\<^sub>p\<lparr>i, p\<rparr> \<subseteq> \<bbbT>\<^sub>p\<lparr>j, p\<rparr>\<close>
  unfolding imm_conseq_p_def
  using imm_conseq_rule_mono SUP_mono'
  by metis

lemma imm_conseq_p_mono2:
  \<open>mono (\<lambda>i p. \<bbbT>\<^sub>p\<lparr>i, p\<rparr>)\<close>
proof -
  have \<open>\<forall>x y. x \<subseteq> y \<longrightarrow> (\<forall>p. \<bbbT>\<^sub>p\<lparr>x, p\<rparr> \<le> \<bbbT>\<^sub>p\<lparr>y, p\<rparr>)\<close>
    using imm_conseq_p_mono
    by simp
  then have \<open>\<forall>x y. x \<subseteq> y \<longrightarrow> (\<lambda>p. \<bbbT>\<^sub>p\<lparr>x, p\<rparr>) \<le> (\<lambda>p. \<bbbT>\<^sub>p\<lparr>y, p\<rparr>)\<close>
    using le_fun_def
    by metis
  then show \<open>mono (\<lambda>i p. \<bbbT>\<^sub>p\<lparr>i, p\<rparr>)\<close>
    using monoI
    by auto
qed

theorem least_fixpoint:
  \<open>M = {i. \<bbbT>\<^sub>p\<lparr>i, p\<rparr> \<subseteq> i} \<Longrightarrow> 
   \<bbbT>\<^sub>p\<lparr>\<Inter>M, p\<rparr> = \<Inter>M\<close>    
proof -
  assume a1: \<open>M = {i. \<bbbT>\<^sub>p\<lparr>i, p\<rparr> \<subseteq> i}\<close>
  have \<open>\<forall>i. i \<in> M \<longrightarrow> \<Inter>M \<subseteq> i\<close>
    by auto
  then have \<open>\<forall>i. i \<in> M \<longrightarrow> \<bbbT>\<^sub>p\<lparr>\<Inter>M, p\<rparr> \<subseteq> \<bbbT>\<^sub>p\<lparr>i, p\<rparr>\<close>
    using imm_conseq_p_mono
    by auto
  then have \<open>\<forall>i. i \<in> M \<longrightarrow> \<bbbT>\<^sub>p\<lparr>\<Inter>M, p\<rparr> \<subseteq> i\<close>
    using a1
    by auto
  then have a2: \<open>\<bbbT>\<^sub>p\<lparr>\<Inter>M, p\<rparr> \<subseteq> \<Inter>M\<close> 
    by auto
  then have \<open>\<bbbT>\<^sub>p\<lparr>\<bbbT>\<^sub>p\<lparr>\<Inter>M, p\<rparr>, p\<rparr> \<subseteq> \<bbbT>\<^sub>p\<lparr>\<Inter>M, p\<rparr>\<close>
    using imm_conseq_p_mono
    by simp
  then have \<open>\<Inter>M \<subseteq> \<bbbT>\<^sub>p\<lparr>\<Inter>M, p\<rparr>\<close> 
    using a1
    by auto
  then show \<open>\<bbbT>\<^sub>p\<lparr>\<Inter>M, p\<rparr> = \<Inter>M\<close>
    using a2
    by simp
qed

theorem fixpoint_exists:
  \<open>\<exists>i. \<bbbT>\<^sub>p\<lparr>i, p\<rparr> = i\<close>
proof 
  show \<open>\<bbbT>\<^sub>p\<lparr>lfp (\<lambda>i. \<bbbT>\<^sub>p\<lparr>i, p\<rparr>), p\<rparr> = lfp (\<lambda>i. \<bbbT>\<^sub>p\<lparr>i, p\<rparr>)\<close>
    unfolding lfp_def
    using least_fixpoint
    by simp
qed
  

subsubsection \<open>Satisfiability\<close>

lemma body_sat_head_sat_imm_conseq_r:
    \<open>\<forall>a \<in> set b. \<lbrakk>a\<rbrakk>\<^sub>av \<in> i \<Longrightarrow> 
     \<lbrakk>h\<rbrakk>\<^sub>av \<in> \<bbbT>\<^sub>r\<lparr>i, Rule h b\<rparr>\<close>
  by auto

lemma body_sat_head_sat_imm_conseq_p:
    \<open>Rule h b \<in> p \<Longrightarrow>
     \<forall>a \<in> set b. \<lbrakk>a\<rbrakk>\<^sub>av \<in> i \<Longrightarrow> 
     \<lbrakk>h\<rbrakk>\<^sub>av \<in> \<bbbT>\<^sub>p\<lparr>i, p\<rparr>\<close>
proof -
  assume a1: \<open>Rule h b \<in> p\<close>
  assume \<open>\<forall>a \<in> set b. \<lbrakk>a\<rbrakk>\<^sub>av \<in> i\<close>
  then have \<open>\<lbrakk>h\<rbrakk>\<^sub>av \<in> \<bbbT>\<^sub>r\<lparr>i, Rule h b\<rparr>\<close>
    using body_sat_head_sat_imm_conseq_r
    by simp
  then have \<open>\<lbrakk>h\<rbrakk>\<^sub>av \<in> \<Union> ((\<lambda>r. \<bbbT>\<^sub>r\<lparr>i, r\<rparr>) ` p)\<close>
    using a1
    by blast
  then show \<open>\<lbrakk>h\<rbrakk>\<^sub>av \<in> \<bbbT>\<^sub>p\<lparr>i, p\<rparr>\<close> 
    using imm_conseq_p_def
    by simp
qed

lemma fixpoint_sat_rule:
    \<open>\<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr> = \<bbbT>\<^sub>p\<^bsup>Suc n\<^esup>\<lparr>i, p\<rparr> \<Longrightarrow> 
     r \<in> p \<Longrightarrow>
     \<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr> \<Turnstile>\<^sub>r r\<close>
proof (induct n arbitrary: i)
  case 0
  then show ?case 
  proof (induct r)
    case (Rule h b)
    then show ?case 
    proof -
      assume a1: \<open>\<bbbT>\<^sub>p\<^bsup>0\<^esup>\<lparr>i, p\<rparr> = \<bbbT>\<^sub>p\<^bsup>Suc 0\<^esup>\<lparr>i, p\<rparr>\<close>
      assume a2: \<open>Rule h b \<in> p\<close>
      have a3: \<open>\<bbbT>\<^sub>p\<lparr>i, p\<rparr> \<subseteq> i\<close>
        using a1
        by auto
      have \<open>\<forall>v. (\<forall>a\<in>set b. \<lbrakk>a\<rbrakk>\<^sub>av \<in> i) \<longrightarrow> \<lbrakk>h\<rbrakk>\<^sub>av \<in> \<bbbT>\<^sub>p\<lparr>i, p\<rparr>\<close>
        using body_sat_head_sat_imm_conseq_p a2
        by simp
      then have \<open>\<forall>v. (\<forall>a\<in>set b. \<lbrakk>a\<rbrakk>\<^sub>av \<in> i) \<longrightarrow> \<lbrakk>h\<rbrakk>\<^sub>av \<in> i\<close>
        using a3
        by auto
      then show \<open>\<bbbT>\<^sub>p\<^bsup>0\<^esup>\<lparr>i, p\<rparr> \<Turnstile>\<^sub>r Rule h b\<close> 
        by auto
    qed
  qed
next
  case (Suc n)
  then show ?case 
  proof (induct r)
    case (Rule h b)
    then show ?case 
    proof -
      assume a1: \<open>(\<And>i. \<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr> = \<bbbT>\<^sub>p\<^bsup>Suc n\<^esup>\<lparr>i, p\<rparr> \<Longrightarrow> 
                        Rule h b \<in> p \<Longrightarrow> 
                        \<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr> \<Turnstile>\<^sub>r Rule h b)\<close>
      assume a2: \<open>\<bbbT>\<^sub>p\<^bsup>Suc n\<^esup>\<lparr>i, p\<rparr> = \<bbbT>\<^sub>p\<^bsup>Suc (Suc n)\<^esup>\<lparr>i, p\<rparr>\<close>
      assume a3: \<open>Rule h b \<in> p\<close>
      have \<open>\<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>\<bbbT>\<^sub>p\<lparr>i, p\<rparr> \<union> i, p\<rparr> = \<bbbT>\<^sub>p\<^bsup>Suc n\<^esup>\<lparr>\<bbbT>\<^sub>p\<lparr>i, p\<rparr> \<union> i, p\<rparr>\<close>
        using a2
        by simp
      then have \<open>\<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>\<bbbT>\<^sub>p\<lparr>i, p\<rparr> \<union> i, p\<rparr> \<Turnstile>\<^sub>r Rule h b\<close>
        using a1 a3
        by simp
      then show \<open>\<bbbT>\<^sub>p\<^bsup>Suc n\<^esup>\<lparr>i, p\<rparr> \<Turnstile>\<^sub>r Rule h b\<close> 
        by simp
    qed
  qed
qed

theorem fixpoint_sat:
    \<open>\<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr> = \<bbbT>\<^sub>p\<^bsup>Suc n\<^esup>\<lparr>i, p\<rparr> \<Longrightarrow>
     \<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr> \<Turnstile>\<^sub>p p\<close>
  unfolding sat_prog_def
  using fixpoint_sat_rule 
  by simp

subsubsection \<open>Relation to Model Semantics\<close>

lemma imm_conseq_r_subset_solve_m:
    \<open>i \<subseteq> \<bbbM>\<lparr>p\<rparr> \<Longrightarrow> 
     r \<in> p \<Longrightarrow> 
     a \<in> \<bbbT>\<^sub>r\<lparr>i, r\<rparr> \<Longrightarrow>
     a \<in> \<bbbM>\<lparr>p\<rparr>\<close>
proof (induct r)
  case (Rule h b)
  then show ?case 
  proof -
    assume a1: \<open>i \<subseteq> \<bbbM>\<lparr>p\<rparr>\<close>
    assume a2: \<open>Rule h b \<in> p\<close>
    assume a3: \<open>a \<in> \<bbbT>\<^sub>r\<lparr>i, Rule h b\<rparr>\<close>
    then have \<open>a \<in> {\<lbrakk>h\<rbrakk>\<^sub>av |v. \<forall>a\<in>set b. \<lbrakk>a\<rbrakk>\<^sub>av \<in> i}\<close>
      by simp
    then have \<open>a \<in> {\<lbrakk>h\<rbrakk>\<^sub>av |v. \<forall>a\<in>set b. \<lbrakk>a\<rbrakk>\<^sub>av \<in> \<bbbM>\<lparr>p\<rparr>}\<close>
      using a1 
      by auto
    then have a4: \<open>\<exists>v. a = \<lbrakk>h\<rbrakk>\<^sub>av \<and> (\<forall>a\<in>set b. \<lbrakk>a\<rbrakk>\<^sub>av \<in> \<bbbM>\<lparr>p\<rparr>)\<close>
      by simp
    have \<open>\<bbbM>\<lparr>p\<rparr> \<Turnstile>\<^sub>r Rule h b\<close>
      using solve_m_sat_rule a2
      by blast
    then show \<open>a \<in> \<bbbM>\<lparr>p\<rparr>\<close>
      using a4
      by auto
  qed
qed

lemma imm_conseq_p_subset_solve_m:
    \<open>i \<subseteq> \<bbbM>\<lparr>p\<rparr> \<Longrightarrow> 
     \<bbbT>\<^sub>p\<lparr>i, p\<rparr> \<subseteq> \<bbbM>\<lparr>p\<rparr>\<close>
proof -
  assume \<open>i \<subseteq> \<bbbM>\<lparr>p\<rparr>\<close>
  then have \<open>\<forall>r a. r \<in> p \<longrightarrow> a \<in> \<bbbT>\<^sub>r\<lparr>i, r\<rparr> \<longrightarrow> a \<in> \<bbbM>\<lparr>p\<rparr>\<close>
    using imm_conseq_r_subset_solve_m
    by simp
  then have \<open>\<Union> (imm_conseq_r i ` p) \<subseteq> \<bbbM>\<lparr>p\<rparr>\<close>
    by blast
  then show \<open>\<bbbT>\<^sub>p\<lparr>i, p\<rparr> \<subseteq> \<bbbM>\<lparr>p\<rparr>\<close> 
    using imm_conseq_p_def
    by simp
qed

lemma imm_conseq_p_step_subset_solve_m:
    \<open>i \<subseteq> \<bbbM>\<lparr>p\<rparr> \<Longrightarrow> 
     \<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr> \<subseteq> \<bbbM>\<lparr>p\<rparr>\<close>
proof (induct n arbitrary: i)
  case 0
  then show ?case 
    by simp
next
  case (Suc n)
  then show ?case 
  proof - 
    assume a1: \<open>\<And>i. i \<subseteq> \<bbbM>\<lparr>p\<rparr> \<Longrightarrow> 
                     \<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr> \<subseteq> \<bbbM>\<lparr>p\<rparr>\<close>
    assume a2: \<open>i \<subseteq> \<bbbM>\<lparr>p\<rparr>\<close>
    then have \<open>\<bbbT>\<^sub>p\<lparr>i, p\<rparr> \<subseteq> \<bbbM>\<lparr>p\<rparr>\<close> 
      using imm_conseq_p_subset_solve_m
      by simp
    then have \<open>\<bbbT>\<^sub>p\<lparr>i, p\<rparr> \<union> i \<subseteq> \<bbbM>\<lparr>p\<rparr>\<close> 
      using a2 
      by simp
    then have \<open>\<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>\<bbbT>\<^sub>p\<lparr>i, p\<rparr> \<union> i, p\<rparr> \<subseteq> \<bbbM>\<lparr>p\<rparr>\<close>
      using a1
      by auto
    then show \<open>\<bbbT>\<^sub>p\<^bsup>Suc n\<^esup>\<lparr>i, p\<rparr> \<subseteq> \<bbbM>\<lparr>p\<rparr>\<close> 
      by simp
  qed
qed

lemma fixpoint_no_sub:
    \<open>i \<subseteq> \<bbbM>\<lparr>p\<rparr> \<Longrightarrow>
     \<not> (\<exists>m\<subset>\<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr>. m \<Turnstile>\<^sub>p p)\<close>
proof -
  assume \<open>i \<subseteq> \<bbbM>\<lparr>p\<rparr>\<close>
  then have \<open>\<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr> \<subseteq> \<bbbM>\<lparr>p\<rparr>\<close> 
    using imm_conseq_p_step_subset_solve_m 
    by simp
  then show \<open>\<not> (\<exists>m\<subset>\<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr>. m \<Turnstile>\<^sub>p p)\<close> 
    using solve_m_no_sub 
    by auto
qed

theorem fixpoint_mini:
    \<open>i \<subseteq> \<bbbM>\<lparr>p\<rparr> \<Longrightarrow>
     \<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr> = \<bbbT>\<^sub>p\<^bsup>Suc n\<^esup>\<lparr>i, p\<rparr> \<Longrightarrow> 
     \<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr> \<Turnstile>\<^sub>m\<^sub>i\<^sub>n p\<close>
  unfolding min_model_def
  using fixpoint_sat fixpoint_no_sub 
  by blast

theorem fixpoint_eval_equiv:
    \<open>i \<subseteq> \<bbbM>\<lparr>p\<rparr> \<Longrightarrow> 
     \<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr> = \<bbbT>\<^sub>p\<^bsup>Suc n\<^esup>\<lparr>i, p\<rparr> \<Longrightarrow>
     \<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr> = \<bbbM>\<lparr>p\<rparr>\<close>
proof -
  assume a1: \<open>i \<subseteq> \<bbbM>\<lparr>p\<rparr>\<close>
  assume a2: \<open>\<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr> = \<bbbT>\<^sub>p\<^bsup>Suc n\<^esup>\<lparr>i, p\<rparr>\<close>
  have \<open>\<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr> \<Turnstile>\<^sub>m\<^sub>i\<^sub>n p\<close>
    using fixpoint_mini a1 a2
    by simp
  then have a3: \<open>\<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr> \<Turnstile>\<^sub>p p\<close>
    using min_model_def
    by simp
  have \<open>\<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr> \<subseteq> \<bbbM>\<lparr>p\<rparr>\<close> 
    using imm_conseq_p_step_subset_solve_m a1
    by simp
  then show \<open>\<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr> = \<bbbM>\<lparr>p\<rparr>\<close> 
    using solve_m_no_sub a3
    by auto
qed


subsubsection \<open>Fixpoint Termination\<close>

lemma imm_conseq_p_gteq_subset:
    \<open>j \<le> n \<Longrightarrow> 
     a \<in> \<bbbT>\<^sub>p\<^bsup>j\<^esup>\<lparr>i, p\<rparr> \<Longrightarrow>
     a \<in> \<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr>\<close>
proof (induct j arbitrary: i n)
  case 0
  then show ?case 
    by (induct n arbitrary: i) simp_all
next
  case (Suc j)
  then show ?case 
  proof -
    assume a1: \<open>\<And>n i. j \<le> n \<Longrightarrow> 
                       a \<in> \<bbbT>\<^sub>p\<^bsup>j\<^esup>\<lparr>i, p\<rparr> \<Longrightarrow> 
                       a \<in> \<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr>\<close> 
    assume a2: \<open>Suc j \<le> n\<close>
    assume a3: \<open>a \<in> \<bbbT>\<^sub>p\<^bsup>Suc j\<^esup>\<lparr>i, p\<rparr>\<close>
    have \<open>\<exists>m. n = Suc m\<close> 
      using a2 Suc_le_D 
      by simp
    then obtain m where a4: \<open>n = Suc m\<close> 
      by blast
    then have \<open>Suc j \<le> Suc m\<close> 
      using a2 
      by auto
    then have \<open>a \<in> \<bbbT>\<^sub>p\<^bsup>Suc m\<^esup>\<lparr>i, p\<rparr>\<close> 
      using a3 a1
      by auto
    then show \<open>a \<in> \<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr>\<close> 
      using a4 
      by auto
  qed
qed

lemma fixpoint_card_increasing:
    \<open>wf_p p ar \<Longrightarrow> 
     safe_p p \<Longrightarrow> 
     i \<subseteq> \<bbbM>\<lparr>p\<rparr> \<Longrightarrow>
     \<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr> \<noteq> \<bbbT>\<^sub>p\<^bsup>Suc n\<^esup>\<lparr>i, p\<rparr> \<Longrightarrow>
     card \<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr> < card \<bbbT>\<^sub>p\<^bsup>Suc n\<^esup>\<lparr>i, p\<rparr>\<close>
proof -
  assume a1: \<open>wf_p p ar\<close>
  assume a2: \<open>safe_p p\<close>
  assume a3: \<open>i \<subseteq> \<bbbM>\<lparr>p\<rparr>\<close>
  assume a4: \<open>\<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr> \<noteq> \<bbbT>\<^sub>p\<^bsup>Suc n\<^esup>\<lparr>i, p\<rparr>\<close>
  have \<open>finite \<bbbM>\<lparr>p\<rparr>\<close> 
    using finite_solve_m a1 a2 
    by simp
  then have a6: \<open>finite \<bbbT>\<^sub>p\<^bsup>Suc n\<^esup>\<lparr>i, p\<rparr>\<close> 
    using finite_subset imm_conseq_p_step_subset_solve_m a3 
    by metis
  have \<open>\<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr> \<subseteq> \<bbbT>\<^sub>p\<^bsup>Suc n\<^esup>\<lparr>i, p\<rparr>\<close> 
    using imm_conseq_p_gteq_subset nat_less_le 
    by blast
  then have \<open>\<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr> \<subset> \<bbbT>\<^sub>p\<^bsup>Suc n\<^esup>\<lparr>i, p\<rparr>\<close> 
    using psubsetI a4 
    by simp
  then show \<open>card \<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr> < card \<bbbT>\<^sub>p\<^bsup>Suc n\<^esup>\<lparr>i, p\<rparr>\<close> 
    using a6 psubset_card_mono 
    by auto
qed

lemma imm_conseq_p_iter_subseteq:
    \<open>\<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr> \<subseteq> \<bbbT>\<^sub>p\<^bsup>Suc n\<^esup>\<lparr>i, p\<rparr>\<close> 
  using imm_conseq_p_gteq_subset nat_less_le 
  by blast

lemma card_gteq_n:
    \<open>wf_p p ar \<Longrightarrow> 
     safe_p p \<Longrightarrow> 
     i \<subseteq> \<bbbM>\<lparr>p\<rparr> \<Longrightarrow> 
     \<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr> \<noteq> \<bbbT>\<^sub>p\<^bsup>Suc n\<^esup>\<lparr>i, p\<rparr> \<Longrightarrow> 
     card \<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr> \<ge> n\<close>
proof (induct n)
  case 0
  then show ?case 
    by simp
next
  case (Suc n)
  then show ?case 
  proof -
    assume a1: \<open>wf_p p ar \<Longrightarrow> 
                safe_p p \<Longrightarrow> 
                i \<subseteq> \<bbbM>\<lparr>p\<rparr> \<Longrightarrow> 
                \<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr> \<noteq> \<bbbT>\<^sub>p\<^bsup>Suc n\<^esup>\<lparr>i, p\<rparr> \<Longrightarrow> 
                n \<le> card \<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr>\<close>
    assume a2: \<open>wf_p p ar\<close>
    assume a3: \<open>safe_p p\<close>
    assume a4: \<open>i \<subseteq> \<bbbM>\<lparr>p\<rparr>\<close>
    assume a5: \<open>\<bbbT>\<^sub>p\<^bsup>Suc n\<^esup>\<lparr>i, p\<rparr> \<noteq> \<bbbT>\<^sub>p\<^bsup>Suc (Suc n)\<^esup>\<lparr>i, p\<rparr>\<close>
    have a8:\<open>\<bbbT>\<^sub>p\<^bsup>Suc (Suc n)\<^esup>\<lparr>i, p\<rparr> \<subseteq> \<bbbM>\<lparr>p\<rparr>\<close> 
      using imm_conseq_p_step_subset_solve_m a4 
      by blast
    have a10:\<open>\<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr> = \<bbbT>\<^sub>p\<^bsup>Suc n\<^esup>\<lparr>i, p\<rparr> \<longrightarrow> 
              \<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr> = \<bbbM>\<lparr>p\<rparr>\<close> 
      using a4 fixpoint_eval_equiv 
      by auto
    then have \<open>n \<le> card \<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr> \<or> \<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr> = \<bbbM>\<lparr>p\<rparr>\<close> 
      using a1 a2 a3 a4 
      by auto
    then have a12:\<open>n \<le> card \<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr> \<and> \<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr> \<noteq> \<bbbM>\<lparr>p\<rparr>\<close> 
      using a8 imm_conseq_p_iter_subseteq a5
      by blast
    then have \<open>card \<bbbT>\<^sub>p\<^bsup>n\<^esup>\<lparr>i, p\<rparr> < card \<bbbT>\<^sub>p\<^bsup>Suc n\<^esup>\<lparr>i, p\<rparr>\<close> 
      using a2 a10 a3 a4 fixpoint_card_increasing 
      by blast
    then show \<open>Suc n \<le> card \<bbbT>\<^sub>p\<^bsup>Suc n\<^esup>\<lparr>i, p\<rparr>\<close> 
      using a12 
      by simp
  qed
qed

theorem fp_solve_m_equiv:
    \<open>wf_p p ar \<Longrightarrow> 
     safe_p p \<Longrightarrow> 
     i \<subseteq> \<bbbM>\<lparr>p\<rparr> \<Longrightarrow> 
     \<bbbT>\<^sub>p\<^bsup>card \<bbbM>\<lparr>p\<rparr>\<^esup>\<lparr>i, p\<rparr> = \<bbbM>\<lparr>p\<rparr>\<close>
proof -
  fix n
  assume a1: \<open>wf_p p ar\<close>
  assume a2: \<open>safe_p p\<close>
  assume a3: \<open>i \<subseteq> \<bbbM>\<lparr>p\<rparr>\<close>
  have a4:\<open>finite \<bbbM>\<lparr>p\<rparr>\<close> 
    using finite_solve_m a1 a2 
    by simp
  have a5:\<open>\<bbbT>\<^sub>p\<^bsup>card \<bbbM>\<lparr>p\<rparr>\<^esup>\<lparr>i, p\<rparr> \<subseteq> \<bbbM>\<lparr>p\<rparr>\<close> 
    using a1 a3 imm_conseq_p_step_subset_solve_m 
    by simp
  have a6:\<open>\<bbbT>\<^sub>p\<^bsup>card \<bbbM>\<lparr>p\<rparr>\<^esup>\<lparr>i, p\<rparr> \<noteq> \<bbbT>\<^sub>p\<^bsup>Suc (card \<bbbM>\<lparr>p\<rparr>)\<^esup>\<lparr>i, p\<rparr> \<longrightarrow>
           card \<bbbM>\<lparr>p\<rparr> \<le> card \<bbbT>\<^sub>p\<^bsup>card \<bbbM>\<lparr>p\<rparr>\<^esup>\<lparr>i, p\<rparr>\<close> 
    using card_gteq_n a1 a2 a3 
    by simp
  have \<open>\<bbbT>\<^sub>p\<^bsup>card \<bbbM>\<lparr>p\<rparr>\<^esup>\<lparr>i, p\<rparr> = \<bbbT>\<^sub>p\<^bsup>Suc (card \<bbbM>\<lparr>p\<rparr>)\<^esup>\<lparr>i, p\<rparr> \<longrightarrow>
        \<bbbT>\<^sub>p\<^bsup>card \<bbbM>\<lparr>p\<rparr>\<^esup>\<lparr>i, p\<rparr> = \<bbbM>\<lparr>p\<rparr>\<close> 
    using fixpoint_eval_equiv a1 a3 
    by simp
  then have \<open>\<bbbM>\<lparr>p\<rparr> = \<bbbT>\<^sub>p\<^bsup>card \<bbbM>\<lparr>p\<rparr>\<^esup>\<lparr>i, p\<rparr> \<or> 
             card \<bbbM>\<lparr>p\<rparr> \<le> card \<bbbT>\<^sub>p\<^bsup>card \<bbbM>\<lparr>p\<rparr>\<^esup>\<lparr>i, p\<rparr>\<close> 
    using a6 
    by auto
  then show \<open>\<bbbT>\<^sub>p\<^bsup>card \<bbbM>\<lparr>p\<rparr>\<^esup>\<lparr>i, p\<rparr> = \<bbbM>\<lparr>p\<rparr>\<close> 
    using card_seteq a5 a4 
    by auto
qed


subsubsection \<open>Evaluation method\<close>

theorem solve_f_sat:
    \<open>wf_p p ar \<Longrightarrow> 
     safe_p p \<Longrightarrow> 
     \<bbbT>\<^sub>p\<^sup>\<omega>\<lparr>p\<rparr> \<Turnstile>\<^sub>p p\<close>
  unfolding solve_f_def
  using fp_solve_m_equiv solve_m_sat_prog solve_m_mini_unique
  by simp

theorem solve_f_finite:
    \<open>wf_p p ar \<Longrightarrow> 
     safe_p p \<Longrightarrow> 
     finite \<bbbT>\<^sub>p\<^sup>\<omega>\<lparr>p\<rparr>\<close>
  unfolding solve_f_def
  using finite_solve_m fp_solve_m_equiv solve_m_mini_unique
  by simp

theorem solve_f_mini:
    \<open>wf_p p ar \<Longrightarrow> 
     safe_p p \<Longrightarrow> 
     \<bbbT>\<^sub>p\<^sup>\<omega>\<lparr>p\<rparr> \<Turnstile>\<^sub>m\<^sub>i\<^sub>n p\<close>
  unfolding solve_f_def
  using fp_solve_m_equiv solve_m_mini solve_m_mini_unique
  by simp

theorem solve_f_mini_unique:
    \<open>wf_p p ar \<Longrightarrow> 
     safe_p p \<Longrightarrow> 
     \<bbbT>\<^sub>p\<^sup>\<omega>\<lparr>p\<rparr> = min p\<close>
  unfolding solve_f_def
  using fp_solve_m_equiv solve_m_mini solve_m_mini_unique
  by simp

theorem solve_f_equiv_solve_m:
    \<open>wf_p p ar \<Longrightarrow> 
     safe_p p \<Longrightarrow> 
     \<bbbT>\<^sub>p\<^sup>\<omega>\<lparr>p\<rparr> = \<bbbM>\<lparr>p\<rparr>\<close>
  unfolding solve_f_def
  using fp_solve_m_equiv solve_m_mini_unique
  by simp

end
