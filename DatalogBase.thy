(*
  Author: Frederik Lyhne Andersen, DTU Compute, 2023
*)

theory DatalogBase
  imports Main
begin

section \<open>Datatypes\<close>

datatype tm = Const nat | Var nat
datatype atom = Pre nat \<open>tm list\<close>
datatype rule = Rule atom \<open>atom list\<close>


section \<open>Util\<close>

subsection \<open>Definitions\<close>

primrec is_var where
  \<open>is_var (Const _) \<longleftrightarrow> False\<close> |
  \<open>is_var (Var _) \<longleftrightarrow> True\<close>

primrec is_const where
  \<open>is_const (Const _) \<longleftrightarrow> True\<close> |
  \<open>is_const (Var _) \<longleftrightarrow> False\<close>

primrec sym where
  \<open>sym (Pre n _) = n\<close>

primrec syms_r where
  \<open>syms_r (Rule h b) = {sym h} \<union> sym ` set b\<close>

definition \<open>syms i \<equiv> sym ` i\<close>

definition \<open>syms_p p \<equiv> \<Union>r \<in> p. syms_r r\<close>

primrec vars_a where
  \<open>vars_a (Pre _ tms) = {tm \<in> set tms. is_var tm}\<close>

primrec vars_r where
  \<open>vars_r (Rule h b) = vars_a h \<union> (\<Union>a \<in> set b. vars_a a)\<close>

definition \<open>vars i \<equiv> \<Union>a \<in> i. vars_a a\<close>

definition \<open>vars_p p \<equiv> \<Union>r \<in> p. vars_r r\<close>

primrec adom_a where
  \<open>adom_a (Pre _ tms) = {tm \<in> set tms. is_const tm}\<close>

primrec adom_r where
  \<open>adom_r (Rule h b) = adom_a h \<union> (\<Union>a \<in> set b. adom_a a)\<close>

definition \<open>adom i \<equiv> \<Union>a \<in> i. adom_a a\<close>

definition \<open>adom_p p \<equiv> (\<Union>r \<in> p. adom_r r)\<close>


subsection \<open>Proofs\<close>

lemma adom_a_interp:
    \<open>\<not> adom_a a \<subseteq> adom i \<Longrightarrow> 
     a \<notin> i\<close>
  unfolding adom_def 
  by (induct a) auto

lemma vars_a_finite:
    \<open>finite (vars_a a)\<close>
  by (induct a) simp

lemma vars_finite:
    \<open>finite i \<Longrightarrow> 
     finite (vars i)\<close>
  unfolding vars_def
  using vars_a_finite 
  by simp

lemma adom_a_finite:
    \<open>finite (adom_a a)\<close>
  by (induct a) simp

lemma adom_r_finite:
    \<open>finite (adom_r r)\<close>
  using adom_a_finite 
  by (induct r) simp

lemma adom_p_finite:
    \<open>finite p \<Longrightarrow>
     finite (adom_p p)\<close>
  unfolding adom_p_def
  using adom_r_finite 
  by simp

lemma syms_r_finite:
    \<open>finite (syms_r r)\<close>
  by (induct r) simp

lemma syms_p_finite:
    \<open>finite p \<Longrightarrow> 
     finite (syms_p p)\<close>
  unfolding syms_p_def
  using syms_r_finite 
  by simp

lemma adom_finite:
    \<open>finite i \<Longrightarrow> 
     finite (adom i)\<close>
  unfolding adom_def
  using adom_a_finite 
  by simp

lemma const_not_var:
    \<open>is_const tm \<noteq> is_var tm\<close>
  by (induct tm) simp_all

lemma adom_a_adom_interp:
    \<open>a \<in> i \<Longrightarrow> 
     adom_a a \<subseteq> adom i\<close>
  unfolding adom_def
  by auto

lemma adom_a_const:
    \<open>tm \<in> adom_a a \<Longrightarrow> 
     is_const tm\<close>
  by (induct a) simp

lemma adom_const:
    \<open>tm \<in> adom i \<Longrightarrow> 
     is_const tm\<close>
  unfolding adom_def
  using adom_a_const 
  by auto

lemma adom_r_const:
    \<open>tm \<in> adom_r r \<Longrightarrow> 
     is_const tm\<close>
  using adom_a_const 
  by (induct r) auto

lemma adom_p_const:
    \<open>tm \<in> adom_p p \<Longrightarrow> 
     is_const tm\<close>
  unfolding adom_p_def
  using adom_r_const 
  by auto

lemma vars_a_var:
    \<open>tm \<in> vars_a a \<Longrightarrow> 
     is_var tm\<close>
  by (induct a) simp

lemma vars_var:
    \<open>tm \<in> vars i \<Longrightarrow> 
     is_var tm\<close>
  unfolding vars_def
  using vars_a_var 
  by auto

lemma vars_r_var:
    \<open>tm \<in> vars_r r \<Longrightarrow> 
     is_var tm\<close>
  using vars_a_var 
  by (induct r) auto

lemma vars_p_var:
    \<open>tm \<in> vars_p p \<Longrightarrow> 
     is_var tm\<close>
  unfolding vars_p_def
  using vars_r_var
  by auto

lemma adom_subset:
    \<open>i1 \<subseteq> i2 \<Longrightarrow>
     adom i1 \<subseteq> adom i2\<close>
  unfolding adom_def
  by auto

lemma adom_p_subset:
    \<open>p1 \<subseteq> p2 \<Longrightarrow>
     adom_p p1 \<subseteq> adom_p p2\<close>
  unfolding adom_p_def
  by auto

lemma syms_subset:
    \<open>i1 \<subseteq> i2 \<Longrightarrow>
     syms i1 \<subseteq> syms i2\<close>
  unfolding syms_def
  by auto

lemma syms_p_subset:
    \<open>p1 \<subseteq> p2 \<Longrightarrow>
     syms_p p1 \<subseteq> syms_p p2\<close>
  unfolding syms_p_def
  by auto

lemma head_adom_in_program:
    \<open>Rule h b \<in> p \<Longrightarrow> 
     adom_a h \<subseteq> adom_p p\<close>
  unfolding adom_p_def 
  by (induct h) auto

lemma rule_head_pred_in_syms:
    \<open>Rule (Pre n tms) b \<in> p \<Longrightarrow> 
     n \<in> syms_p p\<close>
  unfolding syms_p_def 
  by force

lemma rule_head_pred_in_syms2:
    \<open>Rule h b \<in> p \<Longrightarrow> 
     sym h \<in> syms_p p\<close>
  unfolding syms_p_def 
  by force

section \<open>Well Formedness and Safety\<close>

subsection \<open>Definitions\<close>

primrec safe_r where
  \<open>safe_r (Rule h b) \<longleftrightarrow> vars_a h \<subseteq> vars (set b)\<close>

definition \<open>safe_p p \<equiv> \<forall>r \<in> p. safe_r r\<close>

primrec wf_a where
  \<open>wf_a (Pre n tms) ar \<longleftrightarrow> ar n = length tms\<close>

primrec wf_r where
  \<open>wf_r (Rule h b) ar \<longleftrightarrow> wf_a h ar \<and> (\<forall>a \<in> set b. wf_a a ar)\<close>

primrec ground_a where
  \<open>ground_a (Pre _ tms) \<longleftrightarrow> (\<forall>tm \<in> set tms. is_const tm)\<close>

definition \<open>wf_i i ar \<equiv> finite i \<and> (\<forall>a \<in> i. ground_a a \<and> wf_a a ar)\<close>

definition \<open>wf_p p ar \<equiv> finite p \<and> p \<noteq> {} \<and> (\<forall>r \<in> p. wf_r r ar)\<close>


subsection \<open>Proofs\<close>

lemma wf_p_subset:
    \<open>wf_p p1 ar \<Longrightarrow> 
     p2 \<noteq> {} \<Longrightarrow> 
     p2 \<subseteq> p1 \<Longrightarrow> 
     wf_p p2 ar\<close>
  unfolding wf_p_def
  using finite_subset 
  by auto

lemma wf_p_subset2:
    \<open>wf_p p1 ar \<Longrightarrow> 
     \<forall>p2 \<le> p1. p2 \<noteq> {} \<longrightarrow> wf_p p2 ar\<close>
  unfolding wf_p_def
  using finite_subset 
  by auto

lemma wf_p_union:
    \<open>wf_p p1 ar \<Longrightarrow>
     wf_p p2 ar \<Longrightarrow>
     wf_p (p1 \<union> p2) ar\<close>
  unfolding wf_p_def
  by auto

lemma safe_p_subset:
    \<open>safe_p p1 \<Longrightarrow>
     p2 \<subseteq> p1 \<Longrightarrow>
     safe_p p2\<close>
  unfolding safe_p_def
  by auto

lemma safe_p_subset2:
    \<open>safe_p p1 \<Longrightarrow>
     \<forall>p2 \<le> p1. safe_p p2\<close>
  unfolding safe_p_def
  by auto

lemma safe_p_union:
    \<open>safe_p p1 \<Longrightarrow> 
     safe_p p2 \<Longrightarrow> 
     safe_p (p1 \<union> p2)\<close>
  unfolding safe_p_def
  by auto

lemma no_vars_ground_a:
    \<open>vars_a a = {} \<longleftrightarrow> ground_a a\<close>
  using const_not_var 
  by (induct a) auto

lemma ground_a_safe_r:
    \<open>ground_a h \<Longrightarrow> 
     safe_r (Rule h b)\<close>
  using const_not_var 
  by (induct h) auto


section \<open>Satisfiability\<close>

subsection \<open>Definitions\<close>

primrec assign_tm :: \<open>tm \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> tm\<close> (\<open>\<lbrakk>_\<rbrakk>\<^sub>t\<^sub>m_\<close> [100,100]) where
  \<open>\<lbrakk>Const n\<rbrakk>\<^sub>t\<^sub>mv = Const n\<close> |
  \<open>\<lbrakk>Var n\<rbrakk>\<^sub>t\<^sub>mv = Const (v n)\<close>

primrec assign :: \<open>atom \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> atom\<close> (\<open>\<lbrakk>_\<rbrakk>\<^sub>a_\<close> [100,100]) where
  \<open>\<lbrakk>Pre n tms\<rbrakk>\<^sub>av = Pre n (map (\<lambda>tm. \<lbrakk>tm\<rbrakk>\<^sub>t\<^sub>mv) tms)\<close>

primrec sat_rule :: \<open>atom set \<Rightarrow> rule \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>r\<close> 100) where
  \<open>i \<Turnstile>\<^sub>r Rule h b \<longleftrightarrow> (\<forall>v. (\<forall>a \<in> set b. \<lbrakk>a\<rbrakk>\<^sub>av \<in> i) \<longrightarrow> \<lbrakk>h\<rbrakk>\<^sub>av \<in> i)\<close>

definition sat_prog :: \<open>atom set \<Rightarrow> rule set \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>p\<close> 100) where 
  \<open>i \<Turnstile>\<^sub>p p \<equiv> \<forall>r \<in> p. i \<Turnstile>\<^sub>r r\<close>

definition min_model :: \<open>atom set \<Rightarrow> rule set \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>m\<^sub>i\<^sub>n\<close> 100) where
  \<open>i \<Turnstile>\<^sub>m\<^sub>i\<^sub>n p \<equiv> i \<Turnstile>\<^sub>p p \<and> \<not>(\<exists>m \<subset> i. m \<Turnstile>\<^sub>p p)\<close>

definition min :: \<open>rule set \<Rightarrow> atom set\<close> where
  \<open>min p \<equiv> THE i. i \<Turnstile>\<^sub>m\<^sub>i\<^sub>n p\<close>


subsection \<open>Proofs\<close>  

lemma sat_rule_UNIV:
    \<open>UNIV \<Turnstile>\<^sub>r r\<close>
  by (induct r) auto

lemma sat_prog_UNIV:
    \<open>UNIV \<Turnstile>\<^sub>p p\<close>
  unfolding sat_prog_def
  using sat_rule_UNIV 
  by simp
  
theorem prog_has_model:
    \<open>\<exists>m. m \<Turnstile>\<^sub>p p\<close>
  using sat_prog_UNIV 
  by auto

lemma sat_prog_union:
    \<open>i \<Turnstile>\<^sub>p (p1 \<union> p2) \<longleftrightarrow> i \<Turnstile>\<^sub>p p1 \<and> i \<Turnstile>\<^sub>p p2\<close>
  using sat_prog_def 
  by auto

lemma prog_subset_sat:
    \<open>p1 \<subseteq> p2 \<Longrightarrow> 
     i \<Turnstile>\<^sub>p p2 \<Longrightarrow> 
     i \<Turnstile>\<^sub>p p1\<close>
  unfolding sat_prog_def
  by auto

lemma prog_subset_sat2:
    \<open>i \<Turnstile>\<^sub>p p \<Longrightarrow> 
     \<forall>ps \<le> p. i \<Turnstile>\<^sub>p ps\<close>
  using prog_subset_sat
  by simp

lemma const_assign_to_self:
    \<open>is_const tm \<Longrightarrow> 
     \<lbrakk>tm\<rbrakk>\<^sub>t\<^sub>mv = tm\<close>
  by (induct tm) auto

lemma assign_tm_const:
    \<open>is_const (\<lbrakk>tm\<rbrakk>\<^sub>t\<^sub>mv)\<close>
  by (induct tm) auto

lemma ground_a_assign:
    \<open>ground_a a \<Longrightarrow> 
     \<lbrakk>a\<rbrakk>\<^sub>av = a\<close>
proof (induct a)
  case (Pre n tms)
  then show ?case
  proof -
    assume \<open>ground_a (Pre n tms)\<close>
    then have \<open>\<forall>tm \<in> set tms. is_const tm\<close>
      by simp
    then have \<open>\<forall>tm \<in> set tms. \<lbrakk>tm\<rbrakk>\<^sub>t\<^sub>mv = tm\<close>
      using const_assign_to_self
      by simp
    then have \<open>map (\<lambda>tm. \<lbrakk>tm\<rbrakk>\<^sub>t\<^sub>mv) tms = tms\<close>
      using map_idI
      by metis
    then show \<open>\<lbrakk>Pre n tms\<rbrakk>\<^sub>av = Pre n tms\<close>
      by simp
  qed
qed

lemma assign_ground_a:
    \<open>ground_a (\<lbrakk>a\<rbrakk>\<^sub>av)\<close>
  using assign_tm_const 
  by (induct a) simp

lemma assign_wf_a:
    \<open>wf_a a ar \<Longrightarrow> 
     wf_a (\<lbrakk>a\<rbrakk>\<^sub>av) ar\<close>
  by (induct a) auto

lemma assign_same_sym:
    \<open>sym a \<in> syms_p p \<Longrightarrow> 
     sym (\<lbrakk>a\<rbrakk>\<^sub>av) \<in> syms_p p\<close>
  by (induct a) auto

lemma fact_in_interp_rule:
    \<open>safe_r (Rule h []) \<Longrightarrow> 
     i \<Turnstile>\<^sub>r Rule h [] \<Longrightarrow> 
     h \<in> i\<close>
  using vars_def ground_a_assign no_vars_ground_a
  by auto

lemma fact_in_interp:
    \<open>safe_p p \<Longrightarrow>
     Rule h [] \<in> p \<Longrightarrow> 
     i \<Turnstile>\<^sub>p p \<Longrightarrow> 
     h \<in> i\<close>
  unfolding safe_p_def sat_prog_def
  using fact_in_interp_rule 
  by blast

lemma const_not_in_adom:
    \<open>Const (v x) \<notin> adom_a (\<lbrakk>a\<rbrakk>\<^sub>av) \<Longrightarrow> 
     Var x \<notin> vars_a a\<close>
proof (induct a)
  case (Pre n tms)
  then show ?case
  proof -
    assume \<open>Const (v x) \<notin> adom_a (\<lbrakk>Pre n tms\<rbrakk>\<^sub>av)\<close>
    then have \<open>Const (v x) \<notin> (\<lambda>tm. \<lbrakk>tm\<rbrakk>\<^sub>t\<^sub>mv) ` set tms\<close>
      by simp
    then have \<open>\<lbrakk>Var x\<rbrakk>\<^sub>t\<^sub>mv \<notin> (\<lambda>tm. \<lbrakk>tm\<rbrakk>\<^sub>t\<^sub>mv) ` set tms\<close>
      by simp
    then have \<open>Var x \<notin> set tms\<close>
      by blast
    then show \<open>Var x \<notin> vars_a (Pre n tms)\<close> 
      by simp
  qed
qed

lemma adom_assign_subset_head_body:
    \<open>safe_r (Rule h b) \<Longrightarrow>                          
     tm \<in> adom_a (\<lbrakk>h\<rbrakk>\<^sub>av) \<Longrightarrow>
     tm \<notin> adom_a h \<Longrightarrow>
     tm \<in> adom {\<lbrakk>a\<rbrakk>\<^sub>av | a. a \<in> set b}\<close>
proof (induct tm)
  case (Const x)
  then show ?case
  proof (induct h)
    case (Pre n tmsn)
    then show ?case 
    proof -
      assume a1: \<open>safe_r (Rule (Pre n tmsn) b)\<close>
      assume a2: \<open>Const x \<in> adom_a (\<lbrakk>Pre n tmsn\<rbrakk>\<^sub>av)\<close>
      assume a3: \<open>Const x \<notin> adom_a (Pre n tmsn)\<close>
      then have a4: \<open>Const x \<notin> {tm \<in> set tmsn. is_const tm}\<close>
        by simp
      have \<open>Const x \<in> set (map (\<lambda>tm. \<lbrakk>tm\<rbrakk>\<^sub>t\<^sub>mv) tmsn)\<close>
        using a2
        by simp
      then have \<open>Const x \<in> {tm \<in> set tmsn. is_const tm} \<union> 
                           (\<lambda>tm. \<lbrakk>tm\<rbrakk>\<^sub>t\<^sub>mv) ` {tm \<in> set tmsn. is_var tm}\<close>
        using const_assign_to_self const_not_var 
        by force
      then have \<open>Const x \<in> (\<lambda>tm. \<lbrakk>tm\<rbrakk>\<^sub>t\<^sub>mv) ` {tm \<in> set tmsn. is_var tm}\<close>
        using a4
        by simp
      then have \<open>Const x \<in> (\<lambda>tm. \<lbrakk>tm\<rbrakk>\<^sub>t\<^sub>mv) ` \<Union> (vars_a ` set b)\<close>
        using a1 vars_def 
        by auto
      then have \<open>\<exists>a\<in>set b. Const x \<in> (\<lambda>tm. \<lbrakk>tm\<rbrakk>\<^sub>t\<^sub>mv) ` (vars_a a)\<close>
        by auto
      then obtain j tmsj where \<open>Pre j tmsj \<in> set b \<and> 
                                Const x \<in> (\<lambda>tm. \<lbrakk>tm\<rbrakk>\<^sub>t\<^sub>mv) ` (vars_a (Pre j tmsj))\<close>
        using atom.exhaust
        by metis
      then have \<open>Pre j tmsj \<in> set b \<and> 
                 Const x \<in> (\<lambda>tm. \<lbrakk>tm\<rbrakk>\<^sub>t\<^sub>mv) ` {tm \<in> set tmsj. is_var tm}\<close>
        by simp
      then have \<open>Pre j tmsj \<in> set b \<and> Const x \<in> set (map (\<lambda>tm. \<lbrakk>tm\<rbrakk>\<^sub>t\<^sub>mv) tmsj)\<close>
        by auto
      then have \<open>Pre j tmsj \<in> set b \<and> Const x \<in> adom_a (\<lbrakk>Pre j tmsj\<rbrakk>\<^sub>av)\<close>
        by auto
      then have \<open>\<exists>a\<in>set b. Const x \<in> adom_a (\<lbrakk>a\<rbrakk>\<^sub>av)\<close>
        by blast
      then show \<open>Const x \<in> adom {\<lbrakk>a\<rbrakk>\<^sub>av | a. a \<in> set b}\<close> 
        using adom_def 
        by auto
    qed
  qed
next
  case (Var x)
  then show ?case 
  proof -
    assume \<open>Var x \<in> adom_a (\<lbrakk>h\<rbrakk>\<^sub>av)\<close>
    then have a1: \<open>is_const (Var x)\<close>
      using adom_a_const
      by blast
    have \<open>is_var (Var x)\<close>
      by simp
    then have \<open>False\<close> 
      using a1 const_not_var
      by simp
    then show \<open>Var x \<in> adom {\<lbrakk>a\<rbrakk>\<^sub>av |a. a \<in> set b}\<close> 
      by simp
  qed
qed


section \<open>Herbrand Base\<close>

subsection \<open>Definitions\<close>

definition \<open>lists_len i len \<equiv> {tms. set tms \<subseteq> i \<and> length tms = len}\<close>

definition \<open>sym_atoms n i len \<equiv> {Pre n tms | tms. tms \<in> lists_len i len}\<close>

definition herbrand :: \<open>rule set \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> atom set\<close> (\<open>\<bool>\<lparr>_\<rparr>\<^bsub>_\<^esub>\<close>) where
  \<open>\<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub>\<equiv> \<Union>n \<in> syms_p p. sym_atoms n (adom_p p) (ar n)\<close>

subsection \<open>Proofs\<close>

subsubsection \<open>Finiteness\<close>

lemma lists_len_finite:
    \<open>finite i \<Longrightarrow> 
     finite (lists_len i len)\<close>
  unfolding lists_len_def
  using finite_lists_length_eq 
  by auto

lemma sym_atoms_finite:
    \<open>finite i \<Longrightarrow> 
     finite (sym_atoms n i len)\<close>
proof -
  assume \<open>finite i\<close>
  then have \<open>finite (lists_len i len)\<close>
    using lists_len_finite
    by auto
  then have a1: \<open>finite (Pre n ` {tms. tms \<in> lists_len i len})\<close>
    by simp
  have \<open>Pre n ` {tms. tms \<in> lists_len i len} = sym_atoms n i len\<close>
    using sym_atoms_def
    by auto
  then show \<open>finite (sym_atoms n i len)\<close>
    using sym_atoms_def a1
    by simp
qed

theorem herbrand_finite:
    \<open>finite p \<Longrightarrow> 
     finite \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub>\<close>
  unfolding herbrand_def
  using adom_p_finite sym_atoms_finite syms_p_finite 
  by simp

subsubsection \<open>Satisfiability\<close>

theorem wf_ground_a_in_herbrand:
      \<open>wf_a a ar \<Longrightarrow> 
       ground_a a \<Longrightarrow> 
       sym a \<in> syms_p p \<Longrightarrow> 
       adom_a a \<subseteq> adom_p p \<Longrightarrow> 
       a \<in> \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub>\<close>
  unfolding herbrand_def sym_atoms_def lists_len_def
  by (induct a) auto

lemma replicate_atom_in_herbrand:
    \<open>wf_a (Pre n tms) ar \<Longrightarrow> 
     tm \<in> adom_a (Pre n tms) \<Longrightarrow> 
     Rule (Pre n tms) b \<in> p \<Longrightarrow>
     Pre n (replicate (length tms) tm) \<in> \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub>\<close>
proof -
  assume a1: \<open>wf_a (Pre n tms) ar\<close>
  assume a2: \<open>tm \<in> adom_a (Pre n tms)\<close>
  assume a3: \<open>Rule (Pre n tms) b \<in> p\<close>
  have a4 :\<open>n \<in> syms_p p\<close>
    using rule_head_pred_in_syms a3
    by simp
  have \<open>adom_a (Pre n tms) \<subseteq> adom_p p\<close>
    using head_adom_in_program a3
    by blast
  then have \<open>set (replicate (length tms) tm) \<subseteq> adom_p p\<close>
    using a2
    by auto
  then have \<open>replicate (length tms) tm \<in> 
             {tms. set tms \<subseteq> adom_p p \<and> length tms = ar n}\<close>
    using a1
    by auto
  then have \<open>Pre n (replicate (length tms) tm) \<in> 
             {Pre n tms |tms. tms \<in> lists_len (adom_p p) (ar n)}\<close>
    using lists_len_def
    by blast
  then have \<open>Pre n (replicate (length tms) tm) \<in> 
             (\<Union>n\<in>syms_p p. sym_atoms n (adom_p p) (ar n))\<close>
    using sym_atoms_def a4
    by auto
  then show \<open>Pre n (replicate (length tms) tm) \<in> \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub>\<close> 
    using herbrand_def
    by simp
qed

lemma in_adom_replicate_in_herbrand:
    \<open>tm \<in> adom_a (Pre n tms) \<Longrightarrow> 
     Pre n (replicate (length tms) tm) \<in> \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub> \<Longrightarrow> 
     tm \<in> adom \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub>\<close>
proof -
  assume a1: \<open>tm \<in> adom_a (Pre n tms)\<close>
  assume a2: \<open>Pre n (replicate (length tms) tm) \<in> \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub>\<close>
  then have a3: \<open>adom_a (Pre n (replicate (length tms) tm)) \<subseteq> adom \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub>\<close>
    using adom_a_adom_interp
    by blast
  have \<open>adom_a (Pre n (replicate (length tms) tm)) = {tm}\<close>
    using a1
    by auto
  then show \<open>tm \<in> adom \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub>\<close> 
    using a3 
    by simp
qed

lemma adom_head_adom_herbrand:
    \<open>wf_a h ar \<Longrightarrow> 
     Rule h b \<in> p \<Longrightarrow> 
     adom_a h \<subseteq> adom \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub>\<close>
proof -
  assume a1: \<open>wf_a h ar\<close>
  assume a2: \<open>Rule h b \<in> p\<close>
  obtain n tms where a3: \<open>h = Pre n tms\<close>
    using atom.exhaust
    by auto
  then have \<open>\<forall>tm. tm \<in> adom_a (Pre n tms) \<longrightarrow> 
                  Pre n (replicate (length tms) tm) \<in> \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub>\<close>
    using replicate_atom_in_herbrand a1 a2 
    by simp
  then have \<open>\<forall>tm. tm \<in> adom_a (Pre n tms) \<longrightarrow> tm \<in> adom \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub>\<close>
    using in_adom_replicate_in_herbrand
    by auto
  then show \<open>adom_a h \<subseteq> adom \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub>\<close> 
    using a3
    by auto
qed

lemma adom_assign_head_adom_herbrand:
    \<open>wf_r (Rule h b) ar \<Longrightarrow>
     safe_r (Rule h b) \<Longrightarrow> 
     Rule h b \<in> p \<Longrightarrow> 
     \<forall>a\<in>set b. \<lbrakk>a\<rbrakk>\<^sub>av \<in> \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub> \<Longrightarrow>
     adom_a (\<lbrakk>h\<rbrakk>\<^sub>av) \<subseteq> adom \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub>\<close>
proof -
  assume a1: \<open>wf_r (Rule h b) ar\<close>
  assume a2: \<open>safe_r (Rule h b)\<close>
  assume a3: \<open>Rule h b \<in> p\<close>
  assume a4: \<open>\<forall>a\<in>set b. \<lbrakk>a\<rbrakk>\<^sub>av \<in> \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub>\<close>
  have a5: \<open>adom_a (\<lbrakk>h\<rbrakk>\<^sub>av) \<subseteq> adom {\<lbrakk>a\<rbrakk>\<^sub>av |a. a \<in> set b} \<union> adom_a h\<close>
    using adom_assign_subset_head_body a2
    by auto
  have \<open>wf_a h ar\<close>
    using a1
    by simp
  then have a6:\<open>adom_a h \<subseteq> adom \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub>\<close>
    using a3 adom_head_adom_herbrand
    by simp
  have \<open>adom {\<lbrakk>a\<rbrakk>\<^sub>av |a. a \<in> set b} \<subseteq> adom \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub>\<close>
    using adom_def a4
    by auto
  then have \<open>adom_a h \<union> adom {\<lbrakk>a\<rbrakk>\<^sub>av |a. a \<in> set b} \<subseteq> adom \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub>\<close>
    using a6
    by simp
  then show \<open>adom_a (\<lbrakk>h\<rbrakk>\<^sub>av) \<subseteq> adom \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub>\<close> 
    using a5
    by auto
qed

lemma adom_herbrand_adom_p:
    \<open>adom \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub> \<subseteq> adom_p p\<close>
  unfolding herbrand_def sym_atoms_def lists_len_def adom_def
  by auto

lemma herbrand_sat_rule:
    \<open>wf_p p ar \<Longrightarrow> 
     safe_p p \<Longrightarrow> 
     r \<in> p \<Longrightarrow> 
     \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub> \<Turnstile>\<^sub>r r\<close>
proof (induct r)
  case (Rule h b)
  then show ?case 
  proof -
    assume a1: \<open>wf_p p ar\<close>
    assume a2: \<open>safe_p p\<close>
    assume a3: \<open>Rule h b \<in> p\<close>
    have a7: \<open>wf_r (Rule h b) ar\<close> 
      using a1 a3 wf_p_def 
      by auto 
    then have \<open>wf_a h ar\<close> 
      by auto
    then have a9: \<open>\<forall>v. wf_a (\<lbrakk>h\<rbrakk>\<^sub>av) ar\<close> 
      using assign_wf_a 
      by simp
    have a10: \<open>\<forall>v. ground_a (\<lbrakk>h\<rbrakk>\<^sub>av)\<close> 
      using assign_ground_a 
      by simp
    have a11: \<open>\<forall>v. sym (\<lbrakk>h\<rbrakk>\<^sub>av) \<in> syms_p p\<close> 
      using rule_head_pred_in_syms2 a3 assign_same_sym
      by simp
    have \<open>safe_r (Rule h b)\<close>
      using a2 a3 safe_p_def
      by blast
    then have \<open>\<forall>v. (\<forall>a\<in>set b. \<lbrakk>a\<rbrakk>\<^sub>av \<in> \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub>) \<longrightarrow> 
                   adom_a (\<lbrakk>h\<rbrakk>\<^sub>av) \<subseteq> adom \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub>\<close> 
      using a7 a3 adom_assign_head_adom_herbrand 
      by blast
    then have \<open>\<forall>v. (\<forall>a\<in>set b. \<lbrakk>a\<rbrakk>\<^sub>av \<in> \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub>) \<longrightarrow> 
                   adom_a (\<lbrakk>h\<rbrakk>\<^sub>av) \<subseteq> adom_p p\<close> 
      using adom_herbrand_adom_p 
      by blast
    then have \<open>\<forall>v. (\<forall>a\<in>set b. \<lbrakk>a\<rbrakk>\<^sub>av \<in> \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub>) \<longrightarrow> 
                   \<lbrakk>h\<rbrakk>\<^sub>av \<in> \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub>\<close> 
      using a9 a10 a11 wf_ground_a_in_herbrand 
      by simp
    then show \<open>\<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub> \<Turnstile>\<^sub>r Rule h b\<close> 
      by simp
  qed
qed

theorem herbrand_sat_prog:
    \<open>safe_p p \<Longrightarrow> 
     wf_p p ar \<Longrightarrow> 
     \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub> \<Turnstile>\<^sub>p p\<close>
  unfolding sat_prog_def
  using herbrand_sat_rule
  by auto

theorem safe_wf_p_finite:
    \<open>safe_p p \<Longrightarrow> 
     wf_p p ar \<Longrightarrow>
     \<exists>m. m \<Turnstile>\<^sub>p p \<and> finite m\<close>
proof -
  assume a1: \<open>safe_p p\<close>
  assume a2: \<open>wf_p p ar\<close>
  then have a3: \<open>finite \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub>\<close> 
    using herbrand_finite wf_p_def 
    by simp
  have \<open>\<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub> \<Turnstile>\<^sub>p p\<close> 
    using herbrand_sat_prog a1 a2 
    by simp
  then show \<open>\<exists>m. m \<Turnstile>\<^sub>p p \<and> finite m\<close> 
    using a3 
    by auto
qed

subsubsection \<open>Other proofs\<close>

lemma sym_atoms_ground:
    \<open>a \<in> sym_atoms n (adom_p p) len \<Longrightarrow> 
     ground_a a\<close>
proof -
  assume \<open>a \<in> sym_atoms n (adom_p p) len\<close>
  then have a1: \<open>a \<in> {Pre n tms |tms. tms \<in> {tms. set tms \<subseteq> adom_p p \<and> 
                                                   length tms = len}}\<close>
    using sym_atoms_def lists_len_def
    by metis
  then obtain tms where a2: \<open>a = Pre n tms\<close> 
    by blast
  then have \<open>set tms \<subseteq> adom_p p\<close>
    using a1
    by blast
  then have \<open>\<forall>tm \<in> set tms. is_const tm\<close>
    using adom_p_const
    by auto
  then show \<open>ground_a a\<close> 
    using a2
    by simp
qed

theorem herbrand_ground:
    \<open>a \<in> \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub> \<Longrightarrow> 
     ground_a a\<close>
  unfolding herbrand_def
  using sym_atoms_ground 
  by auto

lemma wf_a_herbrand:
    \<open>a \<in> \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub> \<Longrightarrow> 
     wf_a a ar\<close>
  unfolding herbrand_def sym_atoms_def lists_len_def
  by auto

theorem herbrand_wf_i:
    \<open>wf_p p ar \<Longrightarrow>
     wf_i \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub> ar\<close>
  unfolding wf_i_def
  using herbrand_ground wf_a_herbrand herbrand_finite wf_p_def 
  by auto

theorem herbrand_union:
    \<open>\<bool>\<lparr>p1\<rparr>\<^bsub>ar\<^esub> \<union> \<bool>\<lparr>p2\<rparr>\<^bsub>ar\<^esub> \<subseteq> \<bool>\<lparr>p1 \<union> p2\<rparr>\<^bsub>ar\<^esub>\<close>
  unfolding herbrand_def syms_p_def sym_atoms_def lists_len_def adom_p_def
  by auto

lemma herbrand_atom_sym_in_prog_syms:
    \<open>Pre n tms \<in> \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub> \<Longrightarrow> 
     n \<in> syms_p p\<close>
  unfolding herbrand_def syms_p_def sym_atoms_def lists_len_def
  by auto

theorem syms_herbrand_in_prog_syms: 
    \<open>n \<in> syms \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub> \<Longrightarrow> 
     n \<in> syms_p p\<close>
proof -
  fix n
  assume \<open>n \<in> syms (\<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub>)\<close>
  then have \<open>\<exists>a \<in> \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub>. sym a = n\<close>
    using syms_def
    by auto
  then obtain tmsn where \<open>Pre n tmsn \<in> \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub>\<close>
    using atom.exhaust sym.simps
    by metis
  then have \<open>\<exists>tms. Pre n tms \<in> \<bool>\<lparr>p\<rparr>\<^bsub>ar\<^esub>\<close>
    by auto
  then show \<open>n \<in> syms_p p\<close> 
    using herbrand_atom_sym_in_prog_syms
    by auto
qed

end
