theory ArcLengthParam
  imports "$AFP/Green/Green"
begin

definition speed :: "(real \<Rightarrow> real \<times> real) \<Rightarrow> (real  \<Rightarrow> real)" where
"speed f \<equiv> (\<lambda>t. norm (vector_derivative f (at t)))"

definition well_parametrised_on :: "real set \<Rightarrow> (real \<Rightarrow> (real \<times> real)) \<Rightarrow> bool" where
"well_parametrised_on I f \<equiv> (\<exists>f'. (\<forall>t\<in>I. (f has_vector_derivative (f' t)) (at t) \<and> f' t \<noteq> 0 \<and> isCont f' t))"

term  eventually
term filtermap
term filterlim
term is_filter
term Abs_filter
lemma speed_ge_0 : fixes f :: "(real \<Rightarrow> real \<times> real)"
  shows "\<forall>t. speed f t \<ge> 0"
proof
  fix t
  show "speed f t \<ge> 0" using speed_def by auto
qed

lemma WP_speed_gr_0: fixes f :: "(real \<Rightarrow> real \<times> real)" and I :: "real set" and t :: real
  assumes "well_parametrised_on I f"
  shows "\<forall>t\<in>I. speed f t > 0"
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

lemma dist_is_strict_mono: fixes f :: "real \<Rightarrow> real \<times> real" and a :: real and b :: real
  assumes "well_parametrised_on {a..b} f" and "d = (\<lambda>t. integral {a..t} (speed f))" (*Want to make this be contstant after reaching b*)
  shows "strict_mono_on {a..b} d" "inj_on d {a..b}" "\<forall>t\<in>{a..b}. isCont d t"
proof -
  obtain f' where f'_def: "\<forall>t\<in>{a..b}. (f has_vector_derivative (f' t)) (at t) \<and> f' t \<noteq> 0 \<and> isCont f' t"
    using assms(1) well_parametrised_on_def by auto
  hence f_isCont: "\<forall>t\<in>{a..b}. isCont f' t" by auto
  let ?spd_f = "norm \<circ> f'"
  have spd_f_isCont: "\<forall>t\<in>{a..b}. isCont ?spd_f t"
    using f_isCont by (auto simp add: o_def)
  moreover have "\<forall>t\<in>{a..b}. 0 < ?spd_f t"
    using f'_def by fastforce
  moreover hence "a\<le>r \<Longrightarrow> r<s \<Longrightarrow> s\<le>b \<Longrightarrow> integral {r..s} ?spd_f > 0" for r s
    using integral_non_zero_f_gr_0 spd_f_isCont by auto
  moreover have "\<forall>t\<in>{a..b}. (speed f) t = ?spd_f t"
    using vector_derivative_at f'_def speed_def by fastforce
  moreover have "a\<le>r \<Longrightarrow> r<s \<Longrightarrow> s\<le>b \<Longrightarrow> {r..s} \<subseteq> {a..b}" for r s by simp
  ultimately have speed_integral_gr_0: "a\<le>r \<Longrightarrow> r<s \<Longrightarrow> s\<le>b \<Longrightarrow> integral {r..s} (speed f) > 0" for r s
    apply(subst integral_spike[of "{}" _ "?spd_f"])
    by auto
  hence speed_integrable: "a\<le>r \<Longrightarrow> r\<le>s \<Longrightarrow> s\<le>b \<Longrightarrow> (speed f) integrable_on {r..s}" for r s
    using not_integrable_integral
    by (metis integrable_on_refl interval_cbox less_eq_real_def order_less_irrefl)
  have 0: "integral ({r..s}) g = integral {r<..s} g" for r s ::real and g::"real \<Rightarrow> 'a::euclidean_space"
    by (metis Diff_subset greaterThanAtMost_eq_atLeastAtMost_diff integral_subset_negligible negl_ge_le_minus_gt_le)
  have " a\<le>r \<Longrightarrow> {a..s} - {a..r} = {r<..s}" for r s
    by auto
  hence "a\<le>r \<Longrightarrow> r<s \<Longrightarrow> s\<le>b \<Longrightarrow> integral {a..s} (speed f) - integral {a..r} (speed f) = integral {r<..s} (speed f)" for r s
    by(auto simp add: sym[OF integral_setdiff] speed_integrable)
  hence "a\<le>r \<Longrightarrow> r<s \<Longrightarrow> s\<le>b \<Longrightarrow> integral {a..s} (speed f) - integral {a..r} (speed f) > 0" for r s
    by(simp add: sym[OF 0] speed_integral_gr_0)
  thus "strict_mono_on {a..b} d" using assms unfolding strict_mono_on_def well_parametrised_on_def
    by(auto)
  thus "inj_on d {a..b}"
    by(rule Fun.strict_mono_on_imp_inj_on)
  thus "\<forall>t\<in>{a..b}. isCont d t"
    sorry
    by(auto simp add: Deriv.DERIV_isCont assms(2))
qed


(*
Need d to be isCont on all of [a,b] which means we must consider points slightly beyond [a,b]
which is a problem as we have no requirement of continuity of speed f outside of [a,b],
only that some other function exists which isCont on [a,b] and agrees with (vector_derivative f) on [a,b].
We could instead require that a vector derivative exists beyond the interval
i.e require f be differentiable on the whole of UNIV - bad - defeats the whole point of breaking the interval into smaller parts.
Alternatively, we work with the f' which isCont on [a,b] and apply the inverse function theorem to that.
Then since norm f' and speed f are equal on [a,b] the inverse of d will be continuous (not necessarily isCont).
*)


find_theorems name: "inverse_func"

find_theorems name: continuous_on
find_theorems name: "fundamental"
find_theorems "(_ has_vector_derivative _) _" name: fundamental
find_theorems "_ has_integral _ _" "_ \<Longrightarrow> (_ has_vector_derivative _) _"
find_theorems "(_ has_integral _) _ \<Longrightarrow> _" 
thm continuous_on_def
find_theorems "_ equiintegrable_on _"
find_theorems "continuous_on _ _" "isCont"
  

end