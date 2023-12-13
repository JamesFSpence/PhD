theory ArcLengthParam
  imports "$AFP/Green/Green"
begin

definition speed :: "(real \<Rightarrow> real \<times> real) \<Rightarrow> (real  \<Rightarrow> real)" where
"speed f \<equiv> (\<lambda>t. norm (vector_derivative f (at t)))"

definition well_parametrised_on :: "real set \<Rightarrow> (real \<Rightarrow> (real \<times> real)) \<Rightarrow> bool" where
"well_parametrised_on I f \<equiv> (\<exists>f'. (\<forall>t\<in>I. (f has_vector_derivative (f' t)) (at t) \<and> f' t \<noteq> 0 \<and> isCont f' t))"

lemma speed_ge_0 : fixes f :: "(real \<Rightarrow> real \<times> real)"
  shows "\<forall>t. speed f t \<ge> 0"
proof
  fix t
  show "speed f t \<ge> 0" using speed_def by auto
qed

lemma WP_speed_gr_0: fixes f :: "(real \<Rightarrow> real \<times> real)" and I :: "real set" and t :: real
  assumes "well_parametrised_on I f" and "t \<in> I"
  shows "speed f t > 0"
proof -
  show ?thesis using assms vector_derivative_at
    unfolding speed_def well_parametrised_on_def
    by fastforce
qed

lemma integral_non_zero_f_gr_0: fixes f :: "real \<Rightarrow> real" and a :: real and b :: real
  assumes "a<b" "\<forall>t \<in>{a..b}. (f t > 0)" "\<forall>x\<in>{a..b}. isCont f x"
  shows "integral {a..b} f > 0"
proof-
  have "\<exists>L. (\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> L \<le> f x) \<and> (\<exists>x\<ge>a. x \<le> b \<and> f x = L)"
    using assms by (auto simp add: isCont_eq_Lb)
  then obtain L where L_def: "(\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> L \<le> f x) \<and> (\<exists>x\<ge>a. x \<le> b \<and> f x = L)" by auto
  hence "L>0" using assms(2) by auto
  hence "(b-a)*L > 0" by (simp add: assms)
  have "f integrable_on {a..b}"
    thm integrable_continuous_interval[OF continuous_at_imp_continuous_on]
    by (rule integrable_continuous_interval[OF continuous_at_imp_continuous_on[OF assms(3)]])
  hence "integral {a..b} (\<lambda>x. L) \<le> integral {a..b} f"
    by (intro integral_le) (auto simp add: L_def)
  hence "integral {a..b} f \<ge> (b-a)*L"
    using \<open>a<b\<close> by auto
  thus ?thesis using \<open>(b-a)*L > 0\<close> by auto
qed

lemma negl_ge_le_minus_gt_le: "negligible ({r..s} - {r<..s})" for r::real and s
proof cases
  assume "r\<le>s"
  hence "{r..s} - {r<..s} = {r}" by (simp add: double_diff greaterThanAtMost_eq_atLeastAtMost_diff)
  thus ?thesis by auto
next
  assume 0: "~r\<le>s"
  hence 1: "negligible {r..s}" by auto
  have "{r<..s} = {}" using 0 by auto
  thus ?thesis using 1 by auto
qed

lemma negl_gt_le_minus_ge_le: "negligible ({r<..s} - {r..s})" for r::real and s
  by (simp add: greaterThanAtMost_eq_atLeastAtMost_diff)

lemma insert_gt_le_eq_closed: "integral (insert r {r<..s}) g = integral {r..s} g" for r s::real and g
proof cases
  assume "r\<le>s"
  hence "insert r {r<..s} = {r..s}" by auto
  thus ?thesis by auto
next
  assume "~r\<le>s"
  thus ?thesis by auto
qed

lemma fixes f :: "real \<Rightarrow> real \<times> real" and a :: real and b :: real
  assumes "well_parametrised_on {a..b} f" and "d = (\<lambda>t. integral {a..t} (speed f))"
  shows "strict_mono_on {a..b} d"
proof -
  have "(\<exists>f'. (\<forall>t\<in>{a..b}. (f has_vector_derivative (f' t)) (at t) \<and> f' t \<noteq> 0 \<and> isCont f' t))"
    using assms(1) well_parametrised_on_def by auto
  then obtain f' where f'_def: "\<forall>t\<in>{a..b}. (f has_vector_derivative (f' t)) (at t) \<and> f' t \<noteq> 0 \<and> isCont f' t" by auto
  hence "\<forall>t\<in>{a..b}. isCont f' t" by auto
  have "\<forall>t\<in>{a..b}. (f has_vector_derivative (f' t)) (at t)" using f'_def by auto
  hence "\<forall>t\<in>{a..b}. vector_derivative f (at t) = f' t" by (simp add: vector_derivative_at)
  hence "\<forall>t\<in>{a..b}. (speed f) t = norm (f' t)" by (simp add: speed_def)
  have "\<forall>t\<in>{a..b}. isCont (\<lambda>x. vector_derivative f (at x)) t"
    (*ALL THE ABOVE IS USELESS*)
    sorry
  hence speed_f_isCont: "\<forall>t\<in>{a..b}. isCont (speed f) t"
    using speed_def by fastforce
  have "{c..d} \<subseteq> {a..b} \<Longrightarrow> \<forall>x\<in>{a..b}. isCont g x \<Longrightarrow> g integrable_on {c..d}" for c and d and g::"(real \<Rightarrow> 'a::euclidean_space)"
    apply(rule integrable_continuous_interval[OF continuous_at_imp_continuous_on])
    by auto
  hence speed_f_integrable_on: "{c..d} \<subseteq> {a..b} \<Longrightarrow> (speed f) integrable_on {c..d}" for c d using speed_f_isCont by auto
  hence "a \<le> r \<Longrightarrow> r<s \<Longrightarrow> s\<le>b \<Longrightarrow> integral {a..s} (speed f) - integral {a..r} (speed f) = integral {r<..s} (speed f)" for r s
    apply(subst sym[OF integral_setdiff])
       apply(auto)
    sorry
  have "g integrable_on {r..s} \<Longrightarrow> integral ({r<..s}\<union>{r}) g = integral {r<..s} g + integral {r} g" for r::real and  s and g ::"real \<Rightarrow> real"
    apply(rule integral_Un)
      apply(subst integrable_spike_set_eq[of "{r<..s}" "{r..s}"])
      prefer 3
      apply(subst integrable_spike_set_eq[of "{r}" "{}"])
     apply (simp add: greaterThanAtMost_subseteq_atLeastAtMost_iff)
       apply blast
    by(auto simp add: negl_ge_le_minus_gt_le negl_gt_le_minus_ge_le)
  hence "g integrable_on {r..s} \<Longrightarrow> integral ({r..s}) g = integral {r<..s} g" for r::real and  s and g ::"real \<Rightarrow> real"
    by(simp add: insert_gt_le_eq_closed)
  hence "{r..s}\<subseteq>{a..b} \<Longrightarrow> integral ({r<..s}) (speed f) = integral {r..s} (speed f)" for r s
    using speed_f_integrable_on by auto
  hence ?thesis using assms unfolding strict_mono_on_def well_parametrised_on_def
    apply(auto)
    find_theorems "integral ?S _ - integral ?T _"
end