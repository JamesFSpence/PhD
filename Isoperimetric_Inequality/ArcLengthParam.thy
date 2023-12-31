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
find_theorems name: mem_interior


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

locale f_well_paramed =
  fixes a::real and b::real and f::"(real\<Rightarrow>real\<times>real)"
  assumes f_well_param: "well_parametrised_on {a..b} f" and
          a_le_b: "a\<le>b"
begin

lemma f_continuous_on: "continuous_on {a..b} f"
proof -
  have "\<exists>f'. \<forall>t\<in>{a..b}. (f has_vector_derivative f' t) (at t) \<and> f' t \<noteq> 0 \<and> isCont f' t"
    using f_well_param well_parametrised_on_def
    by auto
  thus ?thesis
    by (meson continuous_at_imp_continuous_on has_vector_derivative_continuous)
qed

lemma speed_f_cont_within_a_b: "(\<forall>x\<in>{a..b}. continuous (at x within {a..b})(speed f))"
proof -
  obtain f' where f'_def: "\<forall>t\<in>{a..b}. (f has_vector_derivative (f' t)) (at t) \<and> f' t \<noteq> 0 \<and> isCont f' t"
    using f_well_param well_parametrised_on_def by auto
  hence f_isCont: "\<forall>t\<in>{a..b}. isCont f' t" by auto
  let ?spd_f = "norm \<circ> f'"
  have spd_f_isCont: "\<forall>t\<in>{a..b}. isCont ?spd_f t"
    using f_isCont by (auto simp add: o_def)
  have spd_f_eq: "\<forall>t\<in>{a..b}. (speed f) t = ?spd_f t"
    using vector_derivative_at f'_def speed_def by fastforce
  hence "continuous_on {a..b} (speed f)" using spd_f_isCont
   by (metis continuous_at_imp_continuous_on continuous_on_eq)
  thus ?thesis
    by (simp add: continuous_on_eq_continuous_within)
qed

lemma speed_integral_gr_0: fixes r::real and s::real
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
    using integral_non_zero_f_gr_0 spd_f_isCont by auto
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

lemma dist_is_strict_mono_on: assumes "d = (\<lambda>t. integral {a..t} (speed f))"
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

lemma dist_inj_on: assumes "d = (\<lambda>t. integral {a..t} (speed f))"
  shows "inj_on d {a..b}"
  by (simp add: dist_is_strict_mono_on strict_mono_on_imp_inj_on assms)

lemma dist_deriv: assumes "d = (\<lambda>t. integral {a..t} (speed f))"
  shows "\<forall>t \<in>{a..b}. (d has_vector_derivative (speed f) t) (at t within {a..b})"
proof-
  have speed_integrable_on_a_b: "(speed f) integrable_on {a..b}" using speed_integrable
    by (metis atLeastatMost_empty_iff2 dual_order.refl integrable_on_empty)
  thus "\<forall>t\<in>{a..b}. (d has_vector_derivative (speed f) t) (at t within {a..b})" 
    apply -
    apply(subst(2) sym[OF Diff_empty])
    apply(rule ballI)
    apply(subst assms)
    apply(subst integral_has_vector_derivative_continuous_at)
    using speed_f_cont_within_a_b by auto
qed

lemma dist_cont_on: assumes "d = (\<lambda>t. integral {a..t} (speed f))"
  shows "continuous_on {a..b} d"
  using dist_deriv
  by (meson assms continuous_on_eq_continuous_within has_vector_derivative_continuous)

lemma dist_maps_to_interval: assumes "d = (\<lambda>t. integral {a..t} (speed f))"
  shows "d ` {a<..<b} = {(d a)<..<(d b)}"
proof -
  have "is_interval (d ` {a..b})" using is_interval_connected_1
    by(auto simp add: assms dist_cont_on connected_continuous_image)
  have 1: "x \<in> {a<..<b} \<Longrightarrow> d a < d x \<and> d x < d b" for x
    by(auto intro!: assms dist_is_strict_mono_on strict_mono_onD[of "{a..b}" d])
  hence 2:"d ` {a<..<b} \<subseteq> {(d a)<..<(d b)}"
    using greaterThanLessThan_iff by blast
  hence 3: "d ` ({a<..<b} \<union> {a,b}) \<subseteq> {(d a)<..<(d b)} \<union> {d a, d b}"
    by blast
  have 4: "{a<..<b} \<union> {a,b} = {a..b}" using a_le_b atLeastAtMost_diff_ends
    by auto
  hence "d ` ({a..b}) \<subseteq> {(d a)..(d b)}"
    apply(rule subst)
    apply(rule subset_trans)
     apply(rule 3)
    using a_le_b 2 linorder_linear by fastforce
  have "\<forall>x. d a \<le> x \<and> x \<le> d b \<longrightarrow> x \<in> d ` {a..b}" using \<open>is_interval (d ` {a..b})\<close>
    apply(subst (asm) is_interval_def)
    using "4" by auto
  hence "\<forall>x. d a < x \<and> x < d b \<longrightarrow> x \<in> d ` {a<..<b}"
    apply(subst sym[OF atLeastAtMost_diff_ends])
    by(simp add: set_mp[OF image_diff_subset])
  thus ?thesis using \<open>is_interval (d ` {a..b})\<close>
    by(auto simp add: is_interval_def 1)
qed

lemma f_of_inv_d_has_unit_speed: assumes "d = (\<lambda>t. integral {a..t} (speed f))" "I = d ` {a<..<b}"
  shows "\<forall>t\<in>I. speed (f \<circ> (the_inv_into {a..b} d)) t = 1"
proof-
  have "continuous_on (d ` {a..b}) (the_inv_into {a..b} d)"
    apply(rule continuous_on_inv_into)
    by (auto simp add: dist_cont_on assms dist_inj_on)
  hence the_inv_d_isCont: "\<forall>t \<in> {d a<..<d b}. isCont (the_inv_into {a..b} d) t"
    apply(subst sym[OF continuous_on_eq_continuous_at])
     apply(simp)
    by (metis assms(1) continuous_on_subset dist_maps_to_interval image_mono interior_atLeastAtMost_real interior_subset)
  have inv_into_in: "t \<in> I \<Longrightarrow> the_inv_into {a..b} d t \<in> {a..b}" for t
    apply(rule the_inv_into_into)
    by(auto simp add: assms dist_inj_on the_inv_into_into)
  hence "t \<in> I \<Longrightarrow> the_inv_into {a..b} d t \<in> {a..b} \<and> the_inv_into {a..b} d t \<noteq> a \<and> the_inv_into {a..b} d t \<noteq> b" for t
    by (metis Diff_iff assms atLeastAtMost_diff_ends dist_inj_on dist_maps_to_interval f_the_inv_into_f image_mono in_mono insert_iff interior_atLeastAtMost_real interior_subset)
  hence inv_into_in_open: "t \<in> I \<Longrightarrow> the_inv_into {a..b} d t \<in> {a<..<b}" for t
    by (metis atLeastAtMost_iff greaterThanLessThan_iff order_less_le)
  have deriv_f_non_zero: "t\<in>{a..b} \<Longrightarrow> vector_derivative f (at t) \<noteq> 0" for t
    using f_well_param well_parametrised_on_def by (metis vector_derivative_at)
  have "t\<in>{a..b} \<Longrightarrow> (d has_vector_derivative norm (vector_derivative f (at t))) (at t within {a..b})" for t using dist_deriv
    by(simp add: speed_def assms)
  hence 0: "t \<in> {d a<..<d b} \<Longrightarrow> (d has_vector_derivative norm (vector_derivative f (at (the_inv_into {a..b} d t)))) (at (the_inv_into {a..b} d t))" for t
    apply(subst sym[OF has_vector_derivative_within_open[of _ "{a<..<b}"]])
      apply (metis assms dist_maps_to_interval inv_into_in_open)
    using open_greaterThanLessThan apply blast
    by (metis assms at_within_interior dist_maps_to_interval has_vector_derivative_at_within interior_atLeastAtMost_real inv_into_in inv_into_in_open)
  have "t \<in> {d a<..<d b} \<Longrightarrow> (the_inv_into {a..b} d has_real_derivative inverse (norm (vector_derivative f (at (the_inv_into {a..b} d t))))) (at t)" for t
    apply(rule DERIV_inverse_function[of d _ _ _ "d a" "d b"])
    using dist_deriv apply(simp add: has_real_derivative_iff_has_vector_derivative 0)
    using f_well_param speed_def assms deriv_f_non_zero dist_maps_to_interval inv_into_in apply force
       apply(simp)+ 
     apply(rule f_the_inv_into_f)
      apply(simp add: dist_inj_on assms)
     apply (metis assms(1) dist_maps_to_interval greaterThanLessThan_iff greaterThanLessThan_subseteq_atLeastAtMost_iff image_mono order_refl subset_eq)
    by(simp add: the_inv_d_isCont)
  hence inv_d_has_deriv: "\<forall>t\<in>I. (the_inv_into {a..b} d has_vector_derivative 1/norm (vector_derivative f (at (the_inv_into {a..b} d t)))) (at t)"
    by(auto simp add: dist_maps_to_interval inverse_eq_divide has_real_derivative_iff_has_vector_derivative assms)
  have inv_d_deriv: "\<forall>t\<in>I. vector_derivative (the_inv_into {a..b} d) (at t) = 1/norm (vector_derivative f (at (the_inv_into {a..b} d t)))"
    using vector_derivative_at assms inv_d_has_deriv by auto
  have inv_d_differentiable: "\<forall>t\<in>I. the_inv_into {a..b} d differentiable at t"
    using inv_d_has_deriv assms by (auto simp add: differentiableI_vector)
  have 1: "t \<in> {a..b} \<Longrightarrow> f differentiable at t" for t
    using f_well_param well_parametrised_on_def by (meson differentiableI_vector)
  have f_diffble_at: "t \<in> I \<Longrightarrow> f differentiable at (the_inv_into {a..b} d t)" for t
    by (intro inv_into_in 1) (auto simp add: assms)
  show ?thesis
    apply(subst speed_def)
    apply(rule ballI)
    apply(subst vector_derivative_chain_at)
    apply(simp add: inv_d_differentiable)
    apply(simp add: f_diffble_at)
    apply(simp add: inv_d_deriv)
    by(auto intro!: deriv_f_non_zero inv_into_in simp add: assms(2))
qed

(*Exists arc length parametrisation and image of f is the same when composed with the parametrisation.*)
lemma "\<exists>s l. \<forall>t\<in>{0<..<l}. speed (f\<circ>s) t = 1 \<and> (f \<circ> s) ` {0<..<l} = f ` {a<..<b}"
proof
  let ?d = "(\<lambda>t. integral {a..t} (speed f))"
  let ?s = "(the_inv_into {a..b} ?d)"
  show "\<exists>l. \<forall>t\<in>{0<..<l}. speed (f\<circ>?s) t = 1 \<and> (f \<circ> ?s) ` {0<..<l} = f ` {a<..<b}"
  proof
    have 0: "x \<in> {a..b} \<Longrightarrow> ?s (?d x) = x" for x
      by (auto intro!: dist_inj_on the_inv_into_f_f)
    hence 1: "X \<subseteq> {a..b} \<Longrightarrow> ?s ` (?d ` X) = X" for X
      by (simp add: subset_iff image_image)
    have 2: "?d ` {a<..<b} = {0<..<(?d b)}"
      using dist_maps_to_interval[of "?d"]
      by auto
    hence "?s ` {0<..<(?d b)} = {a<..<b}" using 1
      by (metis greaterThanLessThan_subseteq_atLeastAtMost_iff order_refl)
    hence 3: "(f \<circ> ?s) ` {0<..<(?d b)} = f ` {a<..<b}"
      by (metis image_comp)
    hence "\<forall>t\<in>{0<..<(?d b)}. speed (f\<circ>?s) t = 1" using f_of_inv_d_has_unit_speed 2
      by (simp)
    thus "\<forall>t\<in>{0<..<(?d b)}. speed (f\<circ>?s) t = 1 \<and> (f \<circ> ?s) ` {0<..<(?d b)} = f ` {a<..<b}" using 3
      by simp
  qed
qed

lemma shows "\<exists>x_max\<in>{a..b}. (\<forall>s\<in>{a..b}. fst (f s) \<le> fst (f x_max))"
            "\<exists>x_min\<in>{a..b}. (\<forall>s\<in>{a..b}. fst (f x_min) \<le> fst (f s))"
            "\<exists>y_max\<in>{a..b}. (\<forall>s\<in>{a..b}. snd (f s) \<le> snd (f y_max))"
            "\<exists>y_min\<in>{a..b}. (\<forall>s\<in>{a..b}. snd (f y_min) \<le> snd (f s))"
proof -
  have 0: "isCont (\<lambda>x. f (clamp a b x)) x" for x
    by (auto simp add: clamp_continuous_at f_continuous_on)
  let ?x_comp = "(\<lambda>t. fst (f (clamp a b t)))"
  have 1: "isCont ?x_comp x" for x using isCont_fst
    by(auto simp add: 0)
  hence "\<exists>M. (\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> ?x_comp x \<le> M) \<and> (\<exists>x\<ge>a. x \<le> b \<and> ?x_comp x = M)"
    apply -
    apply(rule isCont_eq_Ub)
    by(auto simp add: a_le_b)
  thus "\<exists>x_max\<in>{a..b}. (\<forall>s\<in>{a..b}. fst (f s) \<le> fst (f x_max))"
    by (metis atLeastAtMost_iff box_real(2) clamp_cancel_cbox)
  have "\<exists>M. (\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> ?x_comp x \<ge> M) \<and> (\<exists>x\<ge>a. x \<le> b \<and> ?x_comp x = M)"
    apply -
    apply(rule isCont_eq_Lb)
    by(auto simp add: a_le_b 1)
  thus "\<exists>x_min\<in>{a..b}. (\<forall>s\<in>{a..b}. fst (f x_min) \<le> fst (f s))"
    by (metis atLeastAtMost_iff box_real(2) clamp_cancel_cbox)
  let ?y_comp = "(\<lambda>t. snd (f (clamp a b t)))"
  have 1: "isCont ?y_comp x" for x using isCont_snd
    by(auto simp add: 0)
  hence "\<exists>M. (\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> ?y_comp x \<le> M) \<and> (\<exists>x\<ge>a. x \<le> b \<and> ?y_comp x = M)"
    apply -
    apply(rule isCont_eq_Ub)
    by(auto simp add: a_le_b)
  thus "\<exists>y_max\<in>{a..b}. (\<forall>s\<in>{a..b}. snd (f s) \<le> snd (f y_max))"
    by (metis atLeastAtMost_iff box_real(2) clamp_cancel_cbox)
  have "\<exists>M. (\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> ?y_comp x \<ge> M) \<and> (\<exists>x\<ge>a. x \<le> b \<and> ?y_comp x = M)"
    apply -
    apply(rule isCont_eq_Lb)
    by(auto simp add: a_le_b 1)
  thus "\<exists>x_min\<in>{a..b}. (\<forall>s\<in>{a..b}. snd (f x_min) \<le> snd (f s))"
    by (metis atLeastAtMost_iff box_real(2) clamp_cancel_cbox)
qed

lemma  shows "\<exists>y_max\<in>{a..b}. (\<forall>s\<in>{a..b}. fst (f s) \<le> snd (f y_max))"
            "\<exists>y_min\<in>{a..b}. (\<forall>s\<in>{a..b}. fst (f y_min) \<le> snd (f s))"

find_theorems name:IVT

  thm image_set_diff
  thm inj_on_image_set_diff

find_theorems "the_inv_into ?S ?f"
find_theorems "_ differentiable _" "_ has_vector_derivative _"
find_theorems "vector_derivative" "_ has_vector_derivative _"
thm differentiableI_vector
find_theorems name: inverse_func



end

lemma dist_is_strict_mono_inj_on: fixes f :: "real \<Rightarrow> real \<times> real" and a :: real and b :: real
  assumes "well_parametrised_on {a..b} f" and "d = (\<lambda>t. integral {a..t} (speed f))" (*Want to make this be contstant after reaching b*)
  shows "strict_mono_on {a..b} d" "inj_on d {a..b}" "\<forall>t \<in>{a..b}. (d has_vector_derivative (speed f) t) (at t within {a..b})" (*could use "continuous_on {a..b} d" potentially*)
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
  moreover have spd_f_eq: "\<forall>t\<in>{a..b}. (speed f) t = ?spd_f t"
    using vector_derivative_at f'_def speed_def by fastforce
  moreover have "a\<le>r \<Longrightarrow> r<s \<Longrightarrow> s\<le>b \<Longrightarrow> {r..s} \<subseteq> {a..b}" for r s by simp
  ultimately have speed_integral_gr_0: "a\<le>r \<Longrightarrow> r<s \<Longrightarrow> s\<le>b \<Longrightarrow> integral {r..s} (speed f) > 0" for r s
    apply(subst integral_spike[of "{}" _ "?spd_f"])
    by auto
  hence speed_integrable: "a\<le>r \<Longrightarrow> r\<le>s \<Longrightarrow> s\<le>b \<Longrightarrow> (speed f) integrable_on {r..s}" for r s
    using not_integrable_integral
    by (metis integrable_on_refl interval_cbox less_eq_real_def order_less_irrefl)
  hence speed_integrable_on_a_b: "(speed f) integrable_on {a..b}"
    by (metis atLeastatMost_empty_iff2 dual_order.refl integrable_on_empty)
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
  have "continuous_on {a..b} (speed f)" using spd_f_isCont spd_f_eq
    by (metis continuous_at_imp_continuous_on continuous_on_eq)
  hence "(\<forall>x\<in>{a..b}. continuous (at x within {a..b})(speed f))"
    by (simp add: continuous_on_eq_continuous_within)
  hence "t\<in> {a..b} \<Longrightarrow> (d has_vector_derivative (speed f) t) (at t within {a..b}-{})" for t
    apply(subst assms(2))
    apply(subst integral_has_vector_derivative_continuous_at)
    by(auto intro: speed_integrable_on_a_b simp add: assms(2))
  thus "\<forall>t \<in>{a..b}. (d has_vector_derivative (speed f) t) (at t within {a..b})"
    by (simp add: atLeastAtMost_diff_ends)
qed

(*
If we need d to be isCont on all of [a,b] then we must consider points slightly beyond [a,b]
which is a problem as we have no requirement of continuity of "speed f" outside of [a,b],
only that some other function exists which isCont on [a,b] and agrees with (vector_derivative f) on [a,b].
We could instead require that a vector derivative exists beyond the interval
i.e require f be differentiable on the whole of UNIV - bad - defeats the whole point of breaking the interval into smaller parts.
Alternatively, we work with the f' which isCont on [a,b] and apply the inverse function theorem to that.
Then since norm f' and speed f are equal on [a,b] the inverse of d will be continuous (not necessarily isCont).
*)

(*Theorems of interest for the arclength parametrisation*)

thm isCont_inverse_function continuous_on_inv_into has_derivative_inverse_on Derivative.vector_derivative_diff_chain_within Brouwer_Fixpoint.has_derivative_inverse_strong

(*We need to find the derivative of "inv d" in order to prove that "f \<circ> (ind d)" is arclength param which involves finding the derivative of d.
One problem is {a..b} is not an open set and the above require S to be open.*)

find_theorems "_ o _" "_ has_vector_derivative _" name: chain
find_theorems "(?f has_vector_derivative ?f') (at ?x within ?S)" name: def
find_theorems name: "inverse_func"                                  
find_theorems "the_inv_into"
find_theorems "inv_into"
                                                              
find_theorems "_ has_derivative _" "?f \<circ> ?g" name: inv
thm has_derivative_inverse_within
thm has_derivative_inverse_within has_derivative_inverse_within[of d _ _ "{a..b}" "the_inv_into {a..b} d"]
thm rev_iffD1[OF _ inj_iff]

find_theorems "?a = ?b \<Longrightarrow> ?b"
find_theorems "inv ?f \<circ> ?f"
find_theorems "_ \<Longrightarrow> linear _"
find_theorems inj_on name: "cont" name: "inv"

find_theorems name: "inv" "_ has_derivative _"

find_theorems compact
find_theorems name: "fundamental"
find_theorems "(_ has_vector_derivative _) _" name: fundamental
find_theorems "_ has_integral _ _" "(_ has_vector_derivative _) _"
find_theorems "(_ has_integral _) _ \<Longrightarrow> _" 
thm continuous_on_def
find_theorems "_ equiintegrable_on _"
find_theorems "continuous_on _ _" "isCont"
  

end