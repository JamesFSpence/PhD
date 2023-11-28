theory GreenExercises
  imports "$AFP/Green/Green"
begin

lemma cube_plus_twotimes_deriv :
  assumes "a\<le>b" 
  shows "integral {a..b} (\<lambda>x::real. x^2 + 2*x) = integral {a..b} (\<lambda>x. x^2) + integral {a..b} ((*) 2)"
proof-
  have "\<And>x. ((\<lambda>x. (1/3)*(x ^ 3)) has_vector_derivative  (1/3) * ((real 3) * x ^ (3 -Suc 0)))  (at x within {a..b})"
    apply(intro derivative_intros)
    by (rule DERIV_pow)
  hence "\<And>x. ((\<lambda>x. (1/3)*(x ^ 3)) has_vector_derivative  x ^ 2)  (at x within {a..b})" by auto
  hence "((\<lambda>x::real. (x ^ 2)) has_integral  1/3 * (b^3 - a^3))  {a..b}" using assms
    apply(simp add: algebra_simps)
    apply(rule Henstock_Kurzweil_Integration.fundamental_theorem_of_calculus)
     by (simp)
  hence power2_intble : "(\<lambda>x::real. x^2) integrable_on {a..b}" 
    by (rule has_integral_integrable)
  have times2_intble: "(\<lambda>x::real. 2 * x) integrable_on {a..b}"
    by (auto intro: integrable_on_mult_right ident_integrable_on)
  show ?thesis using power2_intble times2_intble
    by (rule integral_add)
qed

lemma semi_circ_line_integ:
  fixes F::"real \<times> real \<Rightarrow> real \<times> real" and g::"real \<Rightarrow> real \<times> real"
  assumes "F = (\<lambda>(x,y). (1024 * sin(arctan (y/x))^4 * cos(arctan (y/x))) *\<^sub>R (-sin (arctan (y/x)),cos (arctan (y/x))))" and
          "basis = {(1,0), (0,1)}" and
          \<theta>_def: "\<theta> \<equiv> (\<lambda>t. pi * t - pi/2)" and
          "g = (\<lambda> t. (4 * cos (\<theta> t), 4 * sin (\<theta> t)))"
  shows "line_integral F basis g = 8192 / 5"
proof -
  have X_deriv: "((\<lambda>x. 4096 * sin (\<theta> x) ^ 5 /5) has_vector_derivative 4096 * pi * sin (\<theta> t) ^ 4 * cos (\<theta> t)) (at t within {0..1})" for t
  proof -
    have "(\<theta> has_real_derivative pi) (at t)"
      apply(subst sym[OF  Groups.monoid_add_class.add_0_right])
      apply(subst \<theta>_def)
      apply(subst Groups.group_add_class.diff_conv_add_uminus)
      apply(subst DERIV_add[where E = 0])
      by auto
    hence theta_deriv : "(\<theta> has_real_derivative pi) (at t)"
      by auto
    have g_deriv : "(g has_derivative (\<lambda>h. ((4*pi*(-sin (\<theta> t))) * h, (4*pi*(cos (\<theta> t))) * h))) (at t)"
    proof - 
      have cos_deriv: "((\<lambda> t. 4 * cos (\<theta> t)) has_derivative (*) (4 * pi * -sin (\<theta> t))) (at t)" using theta_deriv
        apply(subst sym[OF has_field_derivative_def])
        thm DERIV_cmult
        apply(subst Groups.semigroup_mult_class.mult.assoc)
        apply(rule DERIV_cmult)
        apply(subst Semiring_Normalization.comm_semiring_1_class.semiring_normalization_rules(7))
        apply(rule DERIV_fun_cos)
        by auto
      have sin_deriv: "((\<lambda>t. 4 * sin (\<theta> t)) has_derivative (*) (4 * pi * cos (\<theta> t))) (at t)" using theta_deriv
        apply(subst sym[OF has_field_derivative_def])
        apply(subst Groups.semigroup_mult_class.mult.assoc)
        apply(rule DERIV_cmult)
        apply(subst Semiring_Normalization.comm_semiring_1_class.semiring_normalization_rules(7))
        apply(rule DERIV_fun_sin)
        by auto
      show ?thesis using sin_deriv cos_deriv
        apply(subst assms(4))
        apply(rule has_derivative_Pair)
        by (assumption)+
    qed
    let ?g' = "(\<lambda>t. (4*pi*(-sin (\<theta> t)), (4*pi*(cos (\<theta> t)))))"
    have g_prime_scale : "(\<lambda>h. ( 4 * pi * -sin(\<theta> t) * h, 4 * pi * cos(\<theta> t) * h )) = (\<lambda>h. h *\<^sub>R ?g' t)"
      by auto
    have g_vector_deriv: "(g has_vector_derivative ?g' t) (at t)" using g_deriv
      apply(subst has_vector_derivative_def)
      apply(subst sym[OF g_prime_scale])
      by auto
    have tan_inst : "\<And>x. tan (x::real) = sin x / cos x"
      by (auto simp add: tan_def)
    have arctan_tan2: "t > 0 \<Longrightarrow> t < 1 \<Longrightarrow> arctan (tan (\<theta> t)) = \<theta> t"
      by (auto intro: arctan_tan simp add: assms)
    let ?F_of_g = "(\<lambda>t. (1024 *  sin (\<theta> t)^4 * cos (\<theta> t)) *\<^sub>R (-sin (\<theta> t), cos (\<theta> t)))"
    have "t > 0 \<Longrightarrow> t < 1 \<Longrightarrow> F (g t) = ?F_of_g t" using assms
      by (auto dest: arctan_tan2 simp add: sym[OF tan_inst])
    hence F_of_g_t : "t \<ge> 0 \<Longrightarrow> t \<le> 1 \<Longrightarrow> F (g t) = ?F_of_g t"
      apply(simp add: algebra_simps)
      apply(drule subst[OF less_eq_real_def])
      by (auto dest: subst[OF less_eq_real_def] simp add: assms)
    have g_vector_deriv2: "t \<in> {0..1} \<Longrightarrow> vector_derivative g (at t within {0..1}) = ?g' t"
      apply(rule vector_derivative_at_within_ivl)
         apply(rule g_vector_deriv)
      by auto
    let ?w = "(\<lambda>t. 4096 * pi * (sin (\<theta> t)^6 * cos (\<theta> t)) + 4096 * pi * (sin (\<theta> t)^4 * cos (\<theta> t) ^ 3))"
    have omega_simp: "?w t =  sin (\<theta> t)^2 * 4096 * pi * sin (\<theta> t)^4 * cos (\<theta> t) + cos (\<theta> t)^2 * 4096 * pi * sin (\<theta> t)^4 * cos (\<theta> t)"
      by (auto simp add: power_def)
    hence omega_simp2 : "4096 * pi * sin (\<theta> t)^4 * cos (\<theta> t) = ?w t"
      apply(simp)
      apply(subst sym [OF ring_class.ring_distribs(2)])
      apply(subst sym [OF z3_rule(134)])
      apply(subst sym[OF sin_cos_squared_add])
      apply(subst ring_class.ring_distribs(2))+
      by (simp)
    have "t > 0 \<Longrightarrow> t < 1\<Longrightarrow> (\<lambda>x. \<Sum>b\<in>basis. F (g x) \<bullet> b * (vector_derivative g (at x within {0..1}) \<bullet> b)) t = ?w t"
      apply(subst g_vector_deriv2)
      by (auto simp add: arctan_tan2 g_vector_deriv2 assms(1,2,4) power_def sym[OF tan_inst])
    hence "t \<in> {0..1} \<Longrightarrow> (\<lambda>x. \<Sum>b\<in>basis. F (g x) \<bullet> b * (vector_derivative g (at t within {0..1}) \<bullet> b)) t = ?w t"
      apply(simp)
      apply(erule conjE)
      apply(drule order_class.le_imp_less_or_eq)
      by (auto dest: order_class.le_imp_less_or_eq simp add: assms)
    hence basis_sum_vec_deriv : "t \<in> {0..1} \<Longrightarrow> (\<lambda>x. \<Sum>b\<in>basis. F (g x) \<bullet> b * (vector_derivative g (at t within {0..1}) \<bullet> b)) t = 4096 * pi * sin (\<theta> t)^4 * cos (\<theta> t)" using omega_simp2
      by auto
    have "\<And>x. ((\<lambda>t. sin t ^ 5) has_real_derivative real 5 * sin x ^ (5-1) * cos x) (at x)"
      apply(subst DERIV_fun_pow[OF DERIV_sin])
      by auto
    hence "\<And>t. ((\<lambda>t. sin t ^ 5) has_real_derivative 5 * sin t ^ 4 * cos t) (at t)"
      by auto
    hence sin_power_five_deriv: "((\<lambda>t. sin t ^ 5) has_real_derivative 5 * sin (\<theta> t) ^ 4 * cos (\<theta> t)) (at (\<theta> t))"
      by auto
    have "((\<lambda>x. sin x ^ 5) \<circ> \<theta> has_vector_derivative pi * (5 * sin (\<theta> t) ^ 4 * cos (\<theta> t))) (at t)"
      apply(rule field_vector_diff_chain_at)
      by (auto simp add: field_vector_diff_chain_at theta_deriv sin_power_five_deriv sym[OF has_real_derivative_iff_has_vector_derivative])
    hence  sin_theta_deriv : "((\<lambda>x. sin x ^ 5) \<circ> \<theta> has_vector_derivative pi * 5 * sin (\<theta> t) ^ 4 * cos (\<theta> t)) (at t)"
      by (auto simp add: algebra_simps)
    have "(\<lambda>x. sin x ^ 5) \<circ> \<theta> = (\<lambda>x. sin (\<theta> x) ^ 5)"
      by auto
    hence sin_theta_deriv2 : "((\<lambda>x. sin (\<theta> x) ^ 5) has_vector_derivative pi * 5 * sin (\<theta> t) ^ 4 * cos (\<theta> t)) (at t)"
      apply(rule subst)
      by (simp only: sin_theta_deriv)
    have "((\<lambda>x. 4096/5 * (sin (\<theta> x) ^ 5)) has_vector_derivative 4096/5 * (pi * 5 * sin (\<theta> t) ^ 4 * cos (\<theta> t))) (at t)"
      apply(intro derivative_intros)
      by (auto simp add: has_real_derivative_iff_has_vector_derivative sin_theta_deriv2)
    hence "((\<lambda>x. 4096 * sin (\<theta> x) ^ 5 /5) has_vector_derivative 4096 * pi * sin (\<theta> t) ^ 4 * cos (\<theta> t)) (at t)"
      by (auto simp add: algebra_simps)
    thus ?thesis
      by (rule has_vector_derivative_at_within)
  qed
  let ?X = "(\<lambda>(t::real). (4096/5) * sin (\<theta> t) ^ 5)"
  have "line_integral F basis g = ?X 1 - ?X 0"
    apply(subst line_integral_def)
    apply(rule integral_unique)
    apply(rule fundamental_theorem_of_calculus)
     apply(simp)
    apply(drule basis_sum_vec_deriv)
    by (auto simp add: X_deriv)
  thus ?thesis
  sorry
qed

lemma line_integral_over_vector_field :
  fixes F :: "real \<times> real \<times> real \<Rightarrow> real \<times> real \<times> real" and r :: "real \<Rightarrow> real \<times> real \<times> real"
  assumes "F = (\<lambda>(x,y,z). (8*x^2*y*z, 5*z, -4*x*y))" and
          "basis = {(1,0,0),(0,1,0),(0,0,1)}" and
          "r = (\<lambda>t. (t,t^2,t^3))"
        shows "line_integral F basis r = 1"
proof- 
  let ?r' = "(\<lambda>t. (1,2*t,3*t^2))"
  have "\<And>t. ((power2 has_vector_derivative real 2 * t ^ (2- Suc 0)) (at t))"
    thm DERIV_pow[where n = 2]
    apply(subst sym[OF has_real_derivative_iff_has_vector_derivative])
    by (rule DERIV_pow) 
  hence power2_deriv: "\<And>t. (power2 has_vector_derivative 2 * t) (at t)"
    by auto
  have "\<And>t. (((\<lambda>x. x^3) has_vector_derivative real 3 * t ^ (3 - Suc 0)) (at t))" 
     apply(subst sym[OF has_real_derivative_iff_has_vector_derivative])
    by (rule DERIV_pow)
  hence power3_deriv: "\<And>t. (((\<lambda>x. x^3) has_vector_derivative 3 * t\<^sup>2) (at t))"
    by auto
  have "\<And>t. (r has_vector_derivative ?r' t) (at t)" 
    apply(subst has_vector_derivative_def)
    apply(subst assms)+
    apply(subst scaleR_Pair)+
    apply(rule has_derivative_Pair)
     apply(simp)
    apply(rule has_derivative_Pair)
     apply(subst sym[OF has_vector_derivative_def])
    apply(rule has_vector_derivative_at_within)
    apply(rule power2_deriv)
    apply(subst sym[OF has_vector_derivative_def])
    by (auto simp add: has_vector_derivative_at_within power3_deriv)
  hence r_prime_within: "\<And>t. 0\<le>t \<Longrightarrow> t\<le>1 \<Longrightarrow> (vector_derivative r (at t within {0..1}) = (?r' t))"
    thm vector_derivative_at_within_ivl
    apply(rule vector_derivative_at_within_ivl)
    by auto
  have "\<And>t. F (r t) = (8 * t ^ 7, 5 * t ^ 3, - (t * (4 * t\<^sup>2)))"
    apply(subst assms)+
    by (auto simp add: algebra_simps)
  let ?Y = "(\<lambda>x. x^8 + 2 * x^5 - 2 * x^6)"
  have "\<And>t. (((\<lambda>x. x^8) has_vector_derivative real 8 * t ^ (8 - Suc 0)) (at t))"
    thm DERIV_pow
    apply(subst sym[OF has_real_derivative_iff_has_vector_derivative])
    by (rule DERIV_pow) 
  hence power8_deriv: "\<And>t. ((\<lambda>x. x^8) has_vector_derivative 8 * t^7) (at t)"
    by auto
  have "\<And>t. (((\<lambda>x. x^5) has_vector_derivative real 5 * t ^ (5 - Suc 0)) (at t))"
    thm DERIV_pow
    apply(subst sym[OF has_real_derivative_iff_has_vector_derivative])
    by (rule DERIV_pow)
  hence two_power5_deriv: "\<And>t. ((\<lambda>x. 2 * x^5) has_vector_derivative 10 * t^4) (at t)"
    apply(rule derivative_eq_intros(30))
    by auto
  have "\<And>t. (((\<lambda>x. x^6) has_vector_derivative real 6 * t ^ (6 - Suc 0)) (at t))"
    apply(subst sym[OF has_real_derivative_iff_has_vector_derivative])
    by (rule DERIV_pow)
  hence m2_power6_deriv: "\<And>t. (((\<lambda>x. - 2 * x ^ 6) has_vector_derivative - 12 * t ^ 5) (at t))"
    apply(rule derivative_eq_intros(30))
    by auto
  have "\<And>x. (((\<lambda>a. a ^ 8 + (2 * a ^ 5 - (2 * a ^ 6))) has_vector_derivative 8 * x ^ 7 + (10 * x ^ 4 - 12 * x ^ 5)) (at x))"
    thm has_vector_derivative_add[OF power8_deriv has_vector_derivative_add[OF two_power5_deriv m2_power6_deriv]]
    apply(rule has_vector_derivative_add)
     apply(rule power8_deriv)
    by (simp only: comm_ring_1_class.ring_normalization_rules(2) has_vector_derivative_add m2_power6_deriv two_power5_deriv sym[OF mult_minus_left])
  hence Y_deriv: "\<And>x. ((\<lambda>a. a ^ 8 + 2 * a ^ 5 - 2 * a ^ 6) has_vector_derivative 8 * x ^ 7 + 10 * x ^ 4 - 12 * x ^ 5) (at x)"
    by (simp add: algebra_simps)
  have "line_integral F basis r = ?Y 1 - ?Y 0" using assms
    apply(subst line_integral_def)
    apply(rule integral_unique)
    apply(rule fundamental_theorem_of_calculus)
    apply(simp)
    apply(subst r_prime_within)
    apply(simp)+
    apply(simp add: algebra_simps)
    apply(subst vector_space_over_itself.scale_scale)
    apply(subst vector_space_over_itself.scale_scale)
    apply(subst comm_semiring_1_class.semiring_normalization_rules(7)[where a = x and b = 10])
    apply(subst comm_semiring_1_class.semiring_normalization_rules(7)[where a = x and b = 12])
    by (simp add: sym[OF vector_space_over_itself.scale_scale] sym[OF power_class.power.power_Suc] Y_deriv has_vector_derivative_at_within)
  thus ?thesis
    by auto
qed

end