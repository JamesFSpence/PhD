theory ArcLengthParam
  imports "$AFP/Green/Green"
begin

(*--------------Useful theorems not specific to arclength param------------*)
lemma interval_un_ends: fixes x y:: real
  assumes "x\<le>y"
  shows "{x<..<y}\<union>{x,y} = {x..y}"
  using assms by fastforce

lemma fixes x y ::real 
  assumes "inj_on f A"
  shows "bij_betw (the_inv_into A f) (f ` A) A"
  using assms by (rule bij_betw_the_inv_into[OF inj_on_imp_bij_betw])

thm bij_betw_the_inv_into[OF inj_on_imp_bij_betw]

lemma fixes f::"real \<Rightarrow> real \<times> real"
  assumes "continuous_on {a..b} f"
          "a\<le>b"
  shows "\<exists>x_max\<in>{a..b}. (\<forall>s\<in>{a..b}. fst (f s) \<le> fst (f x_max))"
        "\<exists>x_min\<in>{a..b}. (\<forall>s\<in>{a..b}. fst (f x_min) \<le> fst (f s))"
        "\<exists>y_max\<in>{a..b}. (\<forall>s\<in>{a..b}. snd (f s) \<le> snd (f y_max))"
        "\<exists>y_min\<in>{a..b}. (\<forall>s\<in>{a..b}. snd (f y_min) \<le> snd (f s))"
proof -
  have 0: "isCont (\<lambda>x. f (clamp a b x)) x" for x
    by (auto simp add: clamp_continuous_at assms)
  let ?x_comp = "(\<lambda>t. fst (f (clamp a b t)))"
  have 1: "isCont ?x_comp x" for x using isCont_fst
    by(auto simp add: 0)
  hence "\<exists>M. (\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> ?x_comp x \<le> M) \<and> (\<exists>x\<ge>a. x \<le> b \<and> ?x_comp x = M)"
    apply -
    apply(rule isCont_eq_Ub)
    by(auto simp add: \<open>a\<le>b\<close>)
  thus "\<exists>x_max\<in>{a..b}. (\<forall>s\<in>{a..b}. fst (f s) \<le> fst (f x_max))"
    by (metis atLeastAtMost_iff box_real(2) clamp_cancel_cbox)
  have "\<exists>M. (\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> ?x_comp x \<ge> M) \<and> (\<exists>x\<ge>a. x \<le> b \<and> ?x_comp x = M)"
    apply -
    apply(rule isCont_eq_Lb)
    by(auto simp add: \<open>a\<le>b\<close> 1)
  thus "\<exists>x_min\<in>{a..b}. (\<forall>s\<in>{a..b}. fst (f x_min) \<le> fst (f s))"
    by (metis atLeastAtMost_iff box_real(2) clamp_cancel_cbox)
  let ?y_comp = "(\<lambda>t. snd (f (clamp a b t)))"
  have 1: "isCont ?y_comp x" for x using isCont_snd
    by(auto simp add: 0)
  hence "\<exists>M. (\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> ?y_comp x \<le> M) \<and> (\<exists>x\<ge>a. x \<le> b \<and> ?y_comp x = M)"
    apply -
    apply(rule isCont_eq_Ub)
    by(auto simp add: \<open>a\<le>b\<close>)
  thus "\<exists>y_max\<in>{a..b}. (\<forall>s\<in>{a..b}. snd (f s) \<le> snd (f y_max))"
    by (metis atLeastAtMost_iff box_real(2) clamp_cancel_cbox)
  have "\<exists>M. (\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> ?y_comp x \<ge> M) \<and> (\<exists>x\<ge>a. x \<le> b \<and> ?y_comp x = M)"
    apply -
    apply(rule isCont_eq_Lb)
    by(auto simp add: \<open>a\<le>b\<close> 1)
  thus "\<exists>x_min\<in>{a..b}. (\<forall>s\<in>{a..b}. snd (f x_min) \<le> snd (f s))"
    by (metis atLeastAtMost_iff box_real(2) clamp_cancel_cbox)
qed


(*-------------------------------------------------------------------------*)     

definition speed :: "(real \<Rightarrow> real \<times> real) \<Rightarrow> (real  \<Rightarrow> real)" where
"speed f \<equiv> (\<lambda>t. norm (vector_derivative f (at t)))"

definition well_parametrised_on :: "real set \<Rightarrow> (real \<Rightarrow> (real \<times> real)) \<Rightarrow> bool" where
"well_parametrised_on I f \<equiv>
        (\<exists>f'. (\<forall>t\<in>I. (f has_vector_derivative (f' t)) (at t) \<and> f' t \<noteq> 0 \<and> isCont f' t))"

lemma speed_ge_0:
  fixes f :: "(real \<Rightarrow> real \<times> real)"
  shows "\<forall>t. speed f t \<ge> 0"
  using speed_def by auto

lemma WP_speed_gr_0:
  assumes "well_parametrised_on I f"
  shows "\<forall>t\<in>I. speed f t > 0"
    using assms vector_derivative_at
    unfolding speed_def well_parametrised_on_def
    by fastforce

lemma func_gr_0_has_integral_gr_0:
  fixes f :: "real \<Rightarrow> real"
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

lemma negl_ge_le_minus_gt_le:"negligible ({r..s} - {r<..s})" for r::real and s
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

locale Well_Parametrised =
  fixes a::real and b::real and f::"(real\<Rightarrow>real\<times>real)"
  assumes f_well_param: "well_parametrised_on {a..b} f" and
          a_le_b: "a\<le>b"
begin

lemma f_cont_on: "continuous_on {a..b} f"
proof -
  have "\<exists>f'. \<forall>t\<in>{a..b}. (f has_vector_derivative f' t) (at t) \<and> f' t \<noteq> 0 \<and> isCont f' t"
    using f_well_param well_parametrised_on_def
    by auto
  thus ?thesis
    by (meson continuous_at_imp_continuous_on has_vector_derivative_continuous)
qed

lemma spd_f_cont_on: "continuous_on {a..b}(speed f)"
proof -
  obtain f' where f'_def: "\<forall>t\<in>{a..b}. (f has_vector_derivative (f' t)) (at t) \<and> f' t \<noteq> 0 \<and> isCont f' t"
    using f_well_param well_parametrised_on_def by auto
  hence f_isCont: "\<forall>t\<in>{a..b}. isCont f' t" by auto
  let ?spd_f = "norm \<circ> f'"
  have spd_f_isCont: "\<forall>t\<in>{a..b}. isCont ?spd_f t"
    using f_isCont by (auto simp add: o_def)
  have spd_f_eq: "\<forall>t\<in>{a..b}. (speed f) t = ?spd_f t"
    using vector_derivative_at f'_def speed_def by fastforce
  thus ?thesis using spd_f_isCont
   by (metis continuous_at_imp_continuous_on continuous_on_eq)
qed

lemma speed_integral_gr_0:
  fixes r::real and s::real
  shows "a\<le>r \<Longrightarrow> r<s \<Longrightarrow> s\<le>b \<Longrightarrow> integral {r..s} (speed f) > 0"
proof-
  obtain f' where f'_def: "\<forall>t\<in>{a..b}. (f has_vector_derivative (f' t)) (at t) \<and> f' t \<noteq> 0 \<and> isCont f' t"
    using f_well_param well_parametrised_on_def by auto
  hence f_isCont: "\<forall>t\<in>{a..b}. isCont f' t" by auto
  let ?spd_f = "norm \<circ> f'"
  have spd_f_isCont: "\<forall>t\<in>{a..b}. isCont ?spd_f t"
    using f_isCont by (auto simp add: o_def)
  moreover have "\<forall>t\<in>{a..b}. 0 < ?spd_f t"
    using f'_def by fastforce
  moreover hence "a\<le>r \<Longrightarrow> r<s \<Longrightarrow> s\<le>b \<Longrightarrow> integral {r..s} ?spd_f > 0" for r s
    using func_gr_0_has_integral_gr_0 spd_f_isCont by auto
  moreover have spd_f_eq: "\<forall>t\<in>{a..b}. (speed f) t = ?spd_f t"
    using vector_derivative_at f'_def speed_def by fastforce
  moreover have "a\<le>r \<Longrightarrow> r<s \<Longrightarrow> s\<le>b \<Longrightarrow> {r..s} \<subseteq> {a..b}" for r s by simp
  ultimately show speed_integral_gr_0: "a\<le>r \<Longrightarrow> r<s \<Longrightarrow> s\<le>b \<Longrightarrow> integral {r..s} (speed f) > 0" for r s
    apply(subst integral_spike[of "{}" _ "?spd_f"])
    by auto
qed

lemma speed_integrable:
  fixes r::real and s::real
  shows "a\<le>r \<Longrightarrow> r\<le>s \<Longrightarrow> s\<le>b \<Longrightarrow> (speed f) integrable_on {r..s}"
    using not_integrable_integral speed_integral_gr_0
    by (metis integrable_on_refl interval_cbox less_eq_real_def order_less_irrefl)

lemma dist_is_strict_mono_on:
  assumes "d = (\<lambda>t. integral {a..t} (speed f))"
  shows "strict_mono_on {a..b} d"
proof -
  have 0: "integral ({r<..s}) g = integral {r..s} g" for r s ::real and g::"real \<Rightarrow> 'a::euclidean_space"
    by (metis Diff_subset greaterThanAtMost_eq_atLeastAtMost_diff integral_subset_negligible negl_ge_le_minus_gt_le)
  have " a\<le>r \<Longrightarrow> {a..s} - {a..r} = {r<..s}" for r s
    by auto
  hence "a\<le>r \<Longrightarrow> r<s \<Longrightarrow> s\<le>b \<Longrightarrow> integral {a..s} (speed f) - integral {a..r} (speed f) = integral {r<..s} (speed f)" for r s
    by(auto simp add: sym[OF integral_setdiff] speed_integrable)
  hence "a\<le>r \<Longrightarrow> r<s \<Longrightarrow> s\<le>b \<Longrightarrow> integral {a..s} (speed f) - integral {a..r} (speed f) > 0" for r s
    by(simp add: 0 speed_integral_gr_0)
  thus "strict_mono_on {a..b} d" using assms unfolding strict_mono_on_def well_parametrised_on_def
    by(auto)
qed

lemma dist_inj_on:
  assumes "d = (\<lambda>t. integral {a..t} (speed f))"
  shows "inj_on d {a..b}"
  by (simp add: dist_is_strict_mono_on strict_mono_on_imp_inj_on assms)

lemma dist_deriv:
  assumes "d = (\<lambda>t. integral {a..t} (speed f))"
  shows "\<forall>t \<in>{a..b}. (d has_vector_derivative (speed f) t) (at t within {a..b})"
proof-
  have speed_integrable_on_a_b: "(speed f) integrable_on {a..b}" using speed_integrable
    by (metis atLeastatMost_empty_iff2 dual_order.refl integrable_on_empty)
  thus "\<forall>t\<in>{a..b}. (d has_vector_derivative (speed f) t) (at t within {a..b})"
    apply(subst assms)
    apply(rule ballI)
    apply(rule integral_has_vector_derivative)
    using spd_f_cont_on by blast
qed

lemma dist_cont_on:
  assumes "d = (\<lambda>t. integral {a..t} (speed f))"
  shows "continuous_on {a..b} d"
  using dist_deriv by (meson assms continuous_on_eq_continuous_within has_vector_derivative_continuous)

lemma dist_open_interval_img:
  assumes "d = (\<lambda>t. integral {a..t} (speed f))"
  shows "d ` {a<..<b} = {(d a)<..<(d b)}"
proof -
  have "x \<in> {a<..<b} \<Longrightarrow> d a < d x \<and> d x < d b" for x
    by(auto intro!: assms dist_is_strict_mono_on strict_mono_onD[of "{a..b}" d])
  hence 1:"d ` {a<..<b} \<subseteq> {(d a)<..<(d b)}"
    using greaterThanLessThan_iff by blast
  have "is_interval (d ` {a..b})" using is_interval_connected_1
    by(auto simp add: assms dist_cont_on connected_continuous_image)
  hence "x \<in> {(d a)..(d b)} \<Longrightarrow> x \<in> d ` {a..b}" for x
    by (meson a_le_b atLeastAtMost_iff is_interval_1 nle_le rev_image_eqI)
  hence "x \<in> {(d a)<..<(d b)} \<Longrightarrow> x \<in> d ` {a<..<b}" for x
    apply(subst sym[OF atLeastAtMost_diff_ends])
    by(simp add: set_mp[OF image_diff_subset])
  hence "{(d a)<..<(d b)} \<subseteq> d ` {a<..<b}"
    by auto
  thus "d` {a<..<b} = {(d a)<..<(d b)}" using 1
    by auto
qed

lemma dist_closed_interval_img:
  assumes "d = (\<lambda>t. integral {a..t} (speed f))"
  shows "d ` {a..b} = {(d a)..(d b)}"
  apply(subst sym[OF interval_un_ends])
  by (auto simp add: a_le_b assms interval_un_ends speed_integrable dist_open_interval_img integral_nonneg nle_le speed_ge_0)

lemma dist_bij_betw:
  assumes "d = (\<lambda>t. integral {a..t} (speed f))"
  shows "bij_betw d {a..b} {(d a)..(d b)}"
  by (simp add: assms bij_betw_def dist_inj_on dist_closed_interval_img)

lemma f_of_inv_d_has_unit_speed:
  assumes "d = (\<lambda>t. integral {a..t} (speed f))"
  shows "\<forall>t\<in>d ` {a<..<b}. speed (f \<circ> (the_inv_into {a..b} d)) t = 1"
proof-
  let ?s = "the_inv_into {a..b} d"
  let ?f' = "vector_derivative f"
  have 0: "?s (d a) = a" "?s (d b) = b"
    by (meson a_le_b assms atLeastAtMost_iff dist_inj_on the_inv_into_f_f verit_comp_simplify1(2))+
  have s_bij: "bij_betw ?s {d a..d b} {a..b}"
    by(intro bij_betw_the_inv_into dist_bij_betw) (rule assms)
  hence "?s ` ({d a..d b} - {d a, d b}) = ?s ` {d a..d b} - ?s ` {d a, d b}"
    by (intro bij_betw_imp_inj_on inj_on_image_set_diff) (auto simp add: assms integral_nonneg a_le_b speed_ge_0 speed_integrable)
  hence s_open_img:"?s ` {d a<..<d b} = {a<..<b}"
    by(simp add: 0 atLeastAtMost_diff_ends bij_betw_imp_surj_on[OF s_bij])
  have "continuous_on {d a..d b} (?s)"
    apply(subst sym[OF dist_closed_interval_img])
    by(auto simp add: dist_cont_on assms dist_inj_on continuous_on_inv_into)
  hence s_isCont: "\<forall>t \<in> {d a<..<d b}. isCont ?s t" using dist_open_interval_img assms
    by(simp add: continuous_on_interior)
  have "t\<in>{a..b} \<Longrightarrow> ?f' (at t) \<noteq> 0" for t
    using f_well_param well_parametrised_on_def by (metis vector_derivative_at)
  hence f'_neq_0: "t \<in> {d a<..<d b} \<Longrightarrow> ?f' (at (?s t)) \<noteq> 0" for t
    by (metis UnI1 a_le_b image_eqI interval_un_ends s_open_img)
  have "t\<in>{a..b} \<Longrightarrow> (d has_vector_derivative norm (?f' (at t))) (at t within {a..b})" for t
    using dist_deriv by(simp add: speed_def assms)
  hence 1: "t \<in> {d a<..<d b} \<Longrightarrow> (d has_vector_derivative norm (?f' (at (?s t)))) (at (?s t))" for t
    by (metis UnI1 a_le_b at_within_interior image_eqI interior_atLeastAtMost_real interval_un_ends s_open_img)
  have s_has_deriv: "t \<in> {d a<..<d b} \<Longrightarrow> (?s has_vector_derivative 1/(norm (?f' (at (?s t))))) (at t)" for t
    apply(subst sym[OF inverse_eq_divide])
    apply(subst sym[OF has_real_derivative_iff_has_vector_derivative])
    apply(rule DERIV_inverse_function[of d _ _ _ "d a" "d b"])
         apply(simp add: 1 f'_neq_0 has_real_derivative_iff_has_vector_derivative)+
    by(auto intro!: f_the_inv_into_f_bij_betw[of _ _ "{d a..d b}"] dist_bij_betw assms simp add: s_isCont)
  have s_deriv: "t\<in>{d a<..<d b} \<Longrightarrow> vector_derivative ?s (at t) = 1/norm (?f' (at (?s t)))" for t
    using vector_derivative_at assms s_has_deriv by auto
  have s_diffble: "t\<in>{d a<..<d b} \<Longrightarrow> ?s differentiable at t" for t
    using s_has_deriv assms differentiableI_vector by blast
  have 2: "t \<in> {d a<..<d b} \<Longrightarrow> f differentiable at (?s t)" for t
    by (metis UnI1 a_le_b differentiableI_vector image_eqI interval_un_ends s_open_img f_well_param well_parametrised_on_def)
  show ?thesis
    apply(subst dist_open_interval_img)
     apply(rule assms)
    by(auto simp add: f'_neq_0 s_deriv 2 s_diffble vector_derivative_chain_at speed_def)
qed

(*Exists continuous arc length parametrisation and image of f is the same when composed with the parametrisation.*)
lemma arclength_param_exists:
"\<exists>s l. \<forall>t\<in>{0<..<l}. speed (f\<circ>s) t = 1 \<and> bij_betw s {0..l} {a..b} \<and> continuous_on {0..l} s"
proof
  let ?d = "(\<lambda>t. integral {a..t} (speed f))"
  let ?s = "(the_inv_into {a..b} ?d)"
  show "\<exists>l. \<forall>t\<in>{0<..<l}. speed (f\<circ>?s) t = 1 \<and> bij_betw ?s {0..l} {a..b} \<and> continuous_on {0..l} ?s"
  proof -
    have s_bij:"bij_betw ?s ({0..?d b}) {a..b}"
      using dist_bij_betw by (auto simp add: dist_closed_interval_img  bij_betw_the_inv_into)
    moreover have s_cont: "continuous_on {0..(?d b)} ?s"
      using continuous_on_inv_into dist_closed_interval_img dist_cont_on dist_inj_on by fastforce
    moreover have "\<forall>t\<in>{0<..<(?d b)}. speed (f\<circ>?s) t = 1"
      using dist_open_interval_img f_of_inv_d_has_unit_speed by (simp)
    ultimately show ?thesis
      by auto
  qed
qed

end

find_theorems name: arclength_param_exists

definition arclength_param:: "(real \<Rightarrow> real \<times> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real \<Rightarrow> real)" where
"arclength_param g a b \<equiv> (\<lambda>t. the_inv_into {a..b} (\<lambda>x. integral {a..x} (speed g)) t)"

end