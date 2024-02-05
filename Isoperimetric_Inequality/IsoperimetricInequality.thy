theory IsoperimetricInequality
  imports Intervals "$AFP/Green/Green"
begin

lemma measurable_cross_section_typeI:
  assumes "typeI_twoCube C"
  shows "(\<lambda>x. measure lebesgue {y. (x, y) \<in> cubeImage C}) \<in> borel_measurable borel"
proof -
  obtain a b g1 g2 where C_params: "a < b" "(\<forall>x \<in> {a..b}. g2 x \<le> g1 x)"
                       "C = (\<lambda>(x,y). (a + (b-a)*x,
                                 g2 (a + (b-a)*x) + (g1 (a + (b-a)*x) - g2 (a + (b-a)*x))*y))"
                       "g1 piecewise_C1_differentiable_on {a..b}"
                       "g2 piecewise_C1_differentiable_on {a..b}"
    using assms typeI_twoCube_def by (auto simp add: algebra_simps)
  have 1:"(\<exists>w\<in>{0..1}. x = a + (b-a)*w) = (x \<in> {a..b})" for x
    using C_params(1) add_scale_img by (metis (mono_tags, lifting) image_iff)
  have "x\<in>{a..b} \<Longrightarrow> (\<lambda>y. g2 x + (g1 x - g2 x)*y) ` {0..1} = {g2 x..g1 x}" for x::real
    by(auto simp add: C_params(2) add_scale_img')
  hence 2: "x\<in>{a..b} \<Longrightarrow> (\<exists>z\<in>{0..1}.  y = g2 x + (g1 x - g2 x)*z) = (y \<in> {g2 x..g1 x})" for x y
    by (metis (mono_tags, lifting) image_iff)
  have "cubeImage C = {(x,y). \<exists>z\<in>{0..1}. \<exists>w\<in>{0..1}. x = a + (b-a)*w \<and> y = g2 x + (g1 x - g2 x)*z}"
    unfolding cubeImage_def image_def using C_params(3) by(auto split: prod.splits)
  hence "cubeImage C = {(x,y). \<exists>z\<in>{0..1}. x\<in>{a..b} \<and> y = g2 x + (g1 x - g2 x)*z}"
    using 1 by auto
  hence cubeImage_C: "cubeImage C = {(x,y). x \<in> {a..b} \<and> y \<in> {g2 x..g1 x}}"
    using 2 by auto
  hence "x\<in>{a..b} \<Longrightarrow> {y. (x,y) \<in> cubeImage C} = {g2 x..g1 x}" for x
    by auto
  hence measure_s\<^sub>x: "x\<in>{a..b} \<Longrightarrow> measure lebesgue {y. (x, y) \<in> cubeImage C} = g1 x - g2 x" for x
    by(simp add: C_params(2))
  moreover have "x\<notin>{a..b} \<Longrightarrow> measure lebesgue {y. (x, y) \<in> cubeImage C} = 0" for x
    using cubeImage_C by force
  ultimately have measure_indicat:"(\<lambda>x. measure lebesgue {y. (x, y) \<in> cubeImage C}) x =
                          (\<lambda>x. indicat_real {a..b} x *\<^sub>R (g1 x - g2 x)) x" for x
    by (metis indicator_eq_0_iff indicator_eq_1_iff scaleR_one scaleR_zero_left)
  thus "(\<lambda>x. measure lebesgue {y. (x, y) \<in> cubeImage C}) \<in> borel_measurable borel"
    apply(subst measure_indicat)
    apply(rule borel_measurable_continuous_on_indicator)
    by (auto simp add: minus_cont C_params(4,5) piecewise_C1_differentiable_on_imp_continuous_on)
qed

lemma measurable_cross_section_typeII:
  assumes "typeII_twoCube C"
  shows "(\<lambda>y. measure lebesgue {x. (x, y) \<in> cubeImage C}) \<in> borel_measurable borel"
proof -
  obtain a b g1 g2 where C_params: "a < b" "(\<forall>x \<in> {a..b}. g2 x \<le> g1 x)"
                       "C = (\<lambda>(y, x). (g2 (a + (b-a)*x) + (g1 (a + (b-a)*x) - g2 (a + (b-a)*x))*y,
                                        a + (b-a)*x))"
                       "g1 piecewise_C1_differentiable_on {a .. b}"
                       "g2 piecewise_C1_differentiable_on {a .. b}"
    using assms typeII_twoCube_def by (auto simp add: algebra_simps)
  have 1:"(\<exists>w\<in>{0..1}. y = a + (b-a)*w) = (y \<in> {a..b})" for y
    using C_params(1) add_scale_img by (metis (mono_tags, lifting) image_iff)
  have "y\<in>{a..b} \<Longrightarrow> (\<lambda>x. g2 y + (g1 y - g2 y)*x) ` {0..1} = {g2 y..g1 y}" for y::real
    by(auto simp add: C_params(2) add_scale_img')
  hence 2: "y\<in>{a..b} \<Longrightarrow> (\<exists>z\<in>{0..1}.  x = g2 y + (g1 y - g2 y)*z) = (x \<in> {g2 y..g1 y})" for x y
    by (metis (mono_tags, lifting) image_iff)
  have "cubeImage C = {(x,y). \<exists>w\<in>{0..1}. \<exists>z\<in>{0..1}. y = a + (b-a)*w \<and> x = g2 y + (g1 y - g2 y)*z}"
    unfolding cubeImage_def image_def using C_params(3) by(auto split: prod.splits)
  hence "cubeImage C = {(x,y). \<exists>z\<in>{0..1}. y\<in>{a..b} \<and> x = g2 y + (g1 y - g2 y)*z}"
    using 1 by auto
  hence cubeImage_C: "cubeImage C = {(x,y). y \<in> {a..b} \<and> x \<in> {g2 y..g1 y}}"
    using 2 by auto
  hence "y\<in>{a..b} \<Longrightarrow> {x. (x,y) \<in> cubeImage C} = {g2 y..g1 y}" for y
    by auto
  hence measure_s\<^sub>x: "y\<in>{a..b} \<Longrightarrow> measure lebesgue {x. (x, y) \<in> cubeImage C} = g1 y - g2 y" for y
    by(simp add: C_params(2))
  moreover have "y\<notin>{a..b} \<Longrightarrow> measure lebesgue {x. (x, y) \<in> cubeImage C} = 0" for y
    using cubeImage_C by force
  ultimately have measure_indicat:"(\<lambda>y. measure lebesgue {x. (x, y) \<in> cubeImage C}) y =
                          (\<lambda>y. indicat_real {a..b} y *\<^sub>R (g1 y - g2 y)) y" for y
    by (metis indicator_eq_0_iff indicator_eq_1_iff scaleR_one scaleR_zero_left)
  thus "(\<lambda>y. measure lebesgue {x. (x, y) \<in> cubeImage C}) \<in> borel_measurable borel"
    apply(subst measure_indicat)
    apply(rule borel_measurable_continuous_on_indicator)
    by (auto simp add: minus_cont C_params(4,5) piecewise_C1_differentiable_on_imp_continuous_on)
qed

lemma typeI_II_cubes_cont_on:
  assumes "typeI_twoCube C \<or> typeII_twoCube C"
  shows "continuous_on unit_cube C"
proof -
  have scale_cont: "continuous_on UNIV (\<lambda>x. a + (b-a)* fst x)" for a b::real
    by (simp add: continuous_on_fst continuous_on_add continuous_on_mult_left)
  have "fst ` unit_cube = {0..1}"
    by (metis cbox_Pair_eq fst_image_times interval_cbox)
  hence scale_img: "a<b \<Longrightarrow> (\<lambda>x. a + (b-a)* fst x) ` unit_cube = {a..b}" for a b::real
    by (metis add_scale_img image_image)
  have cont_on_unit_cube: "a<b \<Longrightarrow> continuous_on {a..b} f \<Longrightarrow>
            continuous_on unit_cube (\<lambda>x. f (a + (b-a)* fst x))" for f::"real \<Rightarrow> real" and a b ::real
    apply(subst sym[OF o_def[of f]])
    apply(rule continuous_on_compose)
     apply(rule continuous_on_subset[of UNIV])
    by(auto simp add: scale_img scale_cont continuous_on_subset)
  have 0:"a<b \<Longrightarrow> continuous_on {a..b} f1 \<Longrightarrow> continuous_on {a..b} f2 \<Longrightarrow> continuous_on unit_cube
    (\<lambda>x. f2(a+(b-a)*fst x)+(f1(a+(b-a)*fst x)-f2(a+(b-a)*fst x))* snd x)" for a b f1 f2
    using cont_on_unit_cube[of a b f1] cont_on_unit_cube[of a b f2]
      by (simp add: continuous_on_add continuous_on_diff continuous_on_mult continuous_on_snd)
  from assms show ?thesis
  proof
    assume "typeI_twoCube C"
    then obtain a b g1 g2 where C_params: "a < b" "(\<forall>x \<in> {a..b}. g2 x \<le> g1 x)"
         "C = (\<lambda>(x,y). (a + (b-a)*x, g2 (a + (b-a)*x) + (g1 (a + (b-a)*x) - g2 (a + (b-a)*x))*y))"
         "g1 piecewise_C1_differentiable_on {a..b}"
         "g2 piecewise_C1_differentiable_on {a..b}"
      using typeI_twoCube_def by (auto simp add: algebra_simps)
    have "continuous_on unit_cube
     (\<lambda>x. g2(a+(b-a)*fst x)+(g1(a+(b-a)*fst x)-g2(a+(b-a)* fst x))* snd x)"
      using 0[of a b g1 g2] C_params piecewise_C1_differentiable_on_imp_continuous_on by auto
    hence "continuous_on unit_cube
     (\<lambda>x. (a+(b-a)* fst x, g2(a+(b-a)* fst x) + (g1(a+(b-a)* fst x)-g2(a+(b-a)* fst x))* snd x))"
      apply(intro continuous_on_Pair) using continuous_on_subset scale_cont by blast+
    thus "continuous_on unit_cube C"
      using C_params(3) by (metis (no_types, lifting) case_prod_beta' continuous_on_cong)
  next
    assume "typeII_twoCube C"
    then obtain a b g1 g2 where C_params: "a < b" "(\<forall>x \<in> {a..b}. g2 x \<le> g1 x)"
         "C = (\<lambda>(y,x). (g2 (a + (b-a)*x) + (g1 (a + (b-a)*x) - g2 (a + (b-a)*x))*y,a + (b-a)*x))"
         "g1 piecewise_C1_differentiable_on {a..b}"
         "g2 piecewise_C1_differentiable_on {a..b}"
      using typeII_twoCube_def by (auto simp add: algebra_simps)
    have "continuous_on unit_cube
     (\<lambda>x. g2 (a + (b - a) * fst x) + (g1 (a + (b - a) * fst x) - g2 (a + (b - a) * fst x)) * snd x)"
      using 0[of a b g1 g2] C_params piecewise_C1_differentiable_on_imp_continuous_on by auto
    hence "continuous_on unit_cube
     (\<lambda>x. (g2(a+(b-a)* fst x) + (g1(a+(b-a)* fst x)-g2(a+(b-a)* fst x))* snd x,a+(b-a)* fst x))"
      apply(intro continuous_on_Pair) using continuous_on_subset scale_cont by blast+
    hence "continuous_on unit_cube 
     (\<lambda>(x,y). (g2(a+(b-a)* x) + (g1(a+(b-a)* x)-g2(a+(b-a)* x))* y,a+(b-a)* x))"
      by (metis (no_types, lifting) case_prod_beta' continuous_on_cong)
    thus"continuous_on unit_cube C"
      using swap_continuous C_params(3) by blast
  qed
qed

lemma typeI_div_compact:
  assumes "valid_typeI_division s two_chain"
  shows "compact s"
proof -
  have "\<forall>C\<in>two_chain. continuous_on unit_cube C"
    using assms typeI_II_cubes_cont_on by auto
  hence "\<forall>C\<in>two_chain. compact (cubeImage C)"
    using compact_cbox compact_continuous_image cubeImage_def
    by metis
  thus "compact s"
    using gen_division_def compact_Union
    by (metis (mono_tags, opaque_lifting) assms image_iff)
qed

lemma typeII_div_compact:
assumes "valid_typeII_division s two_chain"
  shows "compact s"
proof -
  have "\<forall>C\<in>two_chain. continuous_on unit_cube C"
    using assms typeI_II_cubes_cont_on by auto
  hence "\<forall>C\<in>two_chain. compact (cubeImage C)"
    using compact_cbox compact_continuous_image cubeImage_def
    by metis
  thus "compact s"
    using gen_division_def compact_Union
    by (metis (mono_tags, opaque_lifting) assms image_iff)
qed

lemma measure_func_of_intersection_AE_zero:
  assumes "typeI_twoCube C" "typeI_twoCube D" "negligible (cubeImage C \<inter> cubeImage D)"
  shows "AE x in lebesgue. (measure lebesgue {y. (x, y) \<in> (cubeImage C \<inter> cubeImage D)}) = 0"
(*suppose C and D are defined by (a b g1 g2) and (c d h1 h2) resp.
Case1: if [a,b] and [c,d] are disjoint it follows trivially
Case2: two of the endpoints are equal, then there is only one x coordinate in C\<inter>D so follows trivially
Case3: [a,b] and [c,d] intersect on some interval,
        we must have g1 \<le> h2  or g2 \<ge> h1 on the range
         otherwise due to continuity of h1 h2 g1 g2 we would have a non negligible intersection
          from this we get only the endpoints can have intersection which isn't just 1 point*)
proof -
  obtain a b g1 g2 where C_params: "a < b \<and> (\<forall>x \<in> {a..b}. g2 x \<le> g1 x) \<and>
                       C = (\<lambda>(x,y). ((1-x)*a + x*b,
                                        (1 - y) * (g2 ((1-x)*a + x*b)) + y * (g1 ((1-x)*a + x*b)))) \<and>
                       g1 piecewise_C1_differentiable_on {a..b} \<and>
                       g2 piecewise_C1_differentiable_on {a..b}"
    using typeI_twoCube_def assms by auto
  obtain c d h1 h2 where D_params: "c < d \<and> (\<forall>x \<in> {c..d}. h2 x \<le> h1 x) \<and>
                       D = (\<lambda>(x,y). ((1-x)*c + x*d,
                                        (1 - y) * (h2 ((1-x)*c + x*d)) + y * (h1 ((1-x)*c + x*d)))) \<and>
                       h1 piecewise_C1_differentiable_on {c..d} \<and>
                       h2 piecewise_C1_differentiable_on {c..d}"
    using typeI_twoCube_def assms by auto
  have "a<b" "c<d"
    using C_params D_params by auto
  have "continuous_on {a..b} g1" "continuous_on {a..b} g2" "continuous_on {c..d} h1" "continuous_on {c..d} h2"
    using C_params D_params piecewise_C1_differentiable_on_imp_continuous_on by auto
  have C_point: "p\<in>cubeImage C \<Longrightarrow> fst p \<in> {a..b}" for p
    sorry
  have D_point: "q\<in>cubeImage D \<Longrightarrow> fst q \<in> {c..d}" for q
    sorry
  have abcd_cases: "(a > d \<or> b < c)\<or>(a = d \<or> b = c)\<or>(a < d \<and> b > c)"
    by auto
  then consider "(a > d \<or> b < c)"|"(a = d \<or> b = c)"|"(a < d \<and> b > c)"
    by auto
  note abcd_cases = this
  show ?thesis
  proof (rule abcd_cases, goal_cases)
    case 1
    then show ?case sorry
  next
    case 2
    then show ?case sorry
  next
    case 3
    then show ?case sorry
  qed
    assume case1: "a > d \<or> b < c"
    then have "{a..b} \<inter> {c..d} = {}"
      by force
    hence "cubeImage C \<inter> cubeImage D = {}"
      using C_point D_point by blast
    thus ?thesis
      by simp
  next
    assume notcase1:"\<not> (a > d \<or> b < c)"
    show ?thesis
    proof cases
      assume case2: "a = d \<or> b = c"
      have "a = d \<Longrightarrow> {a..b} \<inter> {c..d} = {a}"
        using \<open>a<b\<close> \<open>c<d\<close> by auto
      moreover have "b = c \<Longrightarrow> {a..b} \<inter> {c..d} = {b}"
        using \<open>a<b\<close> \<open>c<d\<close> by auto
      ultimately have "p\<in> cubeImage C \<inter> cubeImage D \<Longrightarrow> fst p = a \<or> fst p = b" for p
        using C_point D_point
        by (metis IntD1 IntD2 atLeastAtMost_iff case2 nle_le)
      hence "(measure lebesgue {y. (x, y) \<in> (cubeImage C \<inter> cubeImage D)}) \<noteq> 0 \<Longrightarrow> x \<in> {a,b}" for x
        by (metis (mono_tags, lifting) empty_Collect_eq fst_conv insertCI negligible_empty negligible_imp_measure0)
      moreover have "negligible {a,b} \<and> {x. \<not> (measure lebesgue {y. (x, y) \<in> (cubeImage C \<inter> cubeImage D)}) = 0} \<subseteq> {a,b}"
        using calculation by blast
      ultimately show ?thesis
        using eventually_ae_filter_negligible by metis
    next
      assume "\<not> (a = d \<or> b = c)"
      then have case3: "a < d \<and> b > c"
        using notcase1 by auto
      let ?I = "{max a c.. min b d}"
      have "{a..b} \<inter> {c..d} = ?I"
        by auto
      have "max a c < min b d"
        using case3 \<open>a<b\<close> \<open>c<d\<close> by auto
(*intersection is a non-singleton interval*)
      have "(\<forall>x\<in>?I. h1 x  \<le> g2 x) \<or> (\<forall>x\<in>?I. g1 x  \<le> h2 x)"
        sorry
      hence "(\<forall>x\<in>?I. measure lebesgue {y. (x, y) \<in> (cubeImage C \<inter> cubeImage D)} = 0)"
        sorry
      hence "measure lebesgue {y. (x, y) \<in> (cubeImage C \<inter> cubeImage D)} = 0" for x
        sorry
      thus ?thesis
        by auto
    qed

(*
lemma measurable_cross_section_typeI_div:
  assumes "valid_typeI_division s two_chain"
  shows "(\<lambda>x. measure lebesgue {y. (x, y) \<in> s}) \<in> borel_measurable borel"
proof -
  have "\<forall> C \<in> two_chain. (\<lambda>x. measure lebesgue {y. (x, y) \<in> cubeImage C}) \<in> borel_measurable borel"
    using measurable_cross_section_typeI assms by auto
  have "{y. (x, y) \<in> s} = (\<Union>C\<in>two_chain.{y. (x, y) \<in> cubeImage C})" for x::real
    find_theorems "measure" "negligible" "_\<inter>_"

lemma measurable_cross_section_typeII_div:
  assumes "valid_typeI_division s two_chain"
  shows "(\<lambda>y. measure lebesgue {x. (x, y) \<in> s}) \<in> borel_measurable borel"
  sorry

lemma closed_cross_sections:
  fixes s::"(real\<times>real) set"
  assumes "closed s"
  shows "closed {y. (x,y) \<in> s}" "closed {y. (y,x) \<in> s}"
proof -
  have 0: "(\<forall>z l. (\<forall>n. z n \<in> s) \<and> z \<longlonglongrightarrow> l \<longrightarrow> l \<in> s)"
    using \<open>closed s\<close> closed_sequential_limits by auto
  hence z_pair_tends1: "\<forall>z l. (\<forall>n. (x,z n) \<in> s) \<and> (\<lambda>n. (x,z n)) \<longlonglongrightarrow> (x,l) \<longrightarrow> (x,l)\<in>s"
    by(auto)
  have "(\<forall>n. z n \<in> {y. (x,y) \<in> s}) \<and> z \<longlonglongrightarrow> l \<longrightarrow> l \<in> {y. (x,y) \<in> s}" for z l
  proof -
    have "(\<forall>n. z n \<in> {y. (x,y) \<in> s}) \<and> z \<longlonglongrightarrow> l \<Longrightarrow> (\<lambda>n. (x,z n)) \<longlonglongrightarrow> (x,l)"
      by (simp add: tendsto_Pair)
    hence "(\<forall>n. z n \<in> {y. (x,y) \<in> s}) \<and> z \<longlonglongrightarrow> l \<Longrightarrow> (x,l) \<in> s" using z_pair_tends1
      by auto
    thus ?thesis by auto
  qed
  thus "closed {y. (x,y) \<in> s}" using closed_sequential_limits[of "{y. (x, y) \<in> s}"]
    by auto
  have z_pair_tends2: "\<forall>z l. (\<forall>n. (z n, x) \<in> s) \<and> (\<lambda>n. (z n, x)) \<longlonglongrightarrow> (l,x) \<longrightarrow> (l,x)\<in>s"
    using 0 by auto
  have "(\<forall>n. z n \<in> {y. (y,x) \<in> s}) \<and> z \<longlonglongrightarrow> l \<longrightarrow> l \<in> {y. (y, x) \<in> s}" for z l
  proof -
    have "(\<forall>n. z n \<in> {y. (y,x) \<in> s}) \<and> z \<longlonglongrightarrow> l \<Longrightarrow> (\<lambda>n. (z n,x)) \<longlonglongrightarrow> (l,x)"
      by (simp add: tendsto_Pair)
    hence "(\<forall>n. z n \<in> {y. (y,x) \<in> s}) \<and> z \<longlonglongrightarrow> l \<Longrightarrow> (l,x) \<in> s" using z_pair_tends2
      by auto
    thus ?thesis by auto
  qed
  thus "closed {y. (y,x) \<in> s}" using closed_sequential_limits[of "{y. (y,x) \<in> s}"]
    by auto
qed

lemma bounded_cross_sections:
  fixes s::"(real\<times>real) set"
  assumes "bounded s"
  shows "bounded {y. (x,y) \<in> s}" "bounded {y. (y,x) \<in> s}"
proof -
  have x0: "bounded {(a, b). a = x \<and> (a, b) \<in> s}" for x
    apply(rule bounded_subset[OF assms])
    by blast
  have x1: "{y. (x,y) \<in> s} = snd ` {(a,b). (a = x \<and> (a,b)\<in>s)}" for x
    by(auto simp add: image_def snd_def)
  show "bounded {y. (x,y) \<in> s}" for x
    by(simp only: x0 x1 bounded_snd)
  have y0: "bounded {(a, b). b = x \<and> (a, b) \<in> s}" for x
    apply(rule bounded_subset[OF assms])
    by blast
  have y1: "{y. (y,x) \<in> s} = fst ` {(a,b). (b = x \<and> (a,b)\<in>s)}" for x
    by(auto simp add: image_def fst_def)
  show "bounded {y. (y,x) \<in> s}" for x
    by(simp only: y0 y1 bounded_fst)
qed

lemma compact_cross_sections:
fixes s::"(real\<times>real) set"
  assumes "compact s"
  shows "compact {y. (x,y) \<in> s}" "compact {y. (y,x) \<in> s}"
proof - 
  show "compact {y. (x,y) \<in> s}"
    using bounded_cross_sections closed_cross_sections assms compact_eq_bounded_closed
    by metis
  show "compact {y. (y,x) \<in> s}"
    using bounded_cross_sections closed_cross_sections assms compact_eq_bounded_closed
    by metis
qed

lemma p_deriv_from_has_p_deriv: assumes "has_partial_vector_derivative F b F' p"
  shows "partial_vector_derivative F b p = F'"
  by (metis assms has_partial_vector_derivative_def partial_vector_derivative_def vector_derivative_at)

lemma minus_y_analytically_valid:
  fixes s :: "(real\<times>real) set"
  assumes "compact s" "(\<lambda>x. measure lebesgue {y. (x, y) \<in> s}) \<in> borel_measurable borel" (*this assumption will follow from s have typeI division*)
  shows "analytically_valid s (\<lambda> x. - snd x) (0,1)"
proof -
  have "has_partial_vector_derivative (\<lambda>x. -snd x) (0, 1) (-1) (a, b)" for a b ::real
    by(auto simp add: has_partial_vector_derivative_def has_vector_derivative_minus)
  hence has_p_deriv: "has_partial_vector_derivative (\<lambda>x. - snd x) (0, 1) (-1) z" for z ::"real\<times>real"
    using prod_cases by blast
  hence p_diffble: "partially_vector_differentiable (\<lambda>x. - snd x) (0, 1) (a, b)" for a b ::real
    unfolding partially_vector_differentiable_def by auto
  have cont_on: "continuous_on s (\<lambda>x. - snd x)"
    using continuous_on_minus[OF continuous_on_snd[OF continuous_on_id']]
    by (simp add: case_prod_unfold)
  have p_deriv_minus_1: "partial_vector_derivative (\<lambda>x. - snd x) (0, 1) p = - 1" for p ::"real\<times>real"
    using has_p_deriv p_deriv_from_has_p_deriv by blast
  have integrable: "integrable lborel (\<lambda>p. partial_vector_derivative (\<lambda>x. - snd x) (0, 1) p * indicat_real s p)"
    apply(simp add: p_deriv_minus_1 subst[of "(\<lambda>p. - indicat_real s p)"])
    using integrable_real_indicator assms
    by (metis borel_compact emeasure_compact_finite sets_lborel)
  have sum_Basis_minus_y: "\<Sum> ({(1::real, 0), (0, 1)} - {(0, 1)}) = (1,0)"
    apply(rule subst[of "{(1,0)}"])
    by(auto)
  have s\<^sub>x_indicat: "(\<lambda>y. indicat_real s (x, y)) = indicat_real {y. (x,y)\<in>s}" for x ::real
    apply(subst indicator_def)+
    by fastforce
  have s\<^sub>x_emb_closed: "closed {y. (x, y) \<in> s}" for x::real
    by (auto simp add: closed_cross_sections compact_imp_closed assms)
  have "bounded {y. (x, y) \<in> s}" for x::real
    by (simp add: bounded_cross_sections compact_imp_bounded assms)
  hence "emeasure lborel {y. (x, y) \<in> s} < \<infinity>" for x::real
    using emeasure_bounded_finite by auto
  hence s\<^sub>x_finite_lebesgue: "{y. (x, y) \<in> s} \<in> {A \<in> sets lebesgue. emeasure lebesgue A < \<infinity>}" for x::real
    by (auto simp add: s\<^sub>x_emb_closed emeasure_bounded_finite)
  have 4: "(\<lambda>x. integral UNIV (\<lambda>y. partial_vector_derivative (\<lambda>x. - snd x) (0, 1) ((0::real, y) + x *\<^sub>R \<Sum> (Basis - {(0, 1)})) * indicat_real s ((0, y) + x *\<^sub>R \<Sum> (Basis - {(0, 1)}))))
              = (\<lambda>x. - integral UNIV (indicat_real {y. (x, y) \<in> s}))"
    apply(simp only: p_deriv_minus_1 real_pair_basis sum_Basis_minus_y scaleR_Pair sym[OF s\<^sub>x_indicat])
    by(auto)
  have borel_measurable: "(\<lambda>x. integral UNIV (\<lambda>y. partial_vector_derivative (\<lambda>x. - snd x) (0, 1) ((0::real, y) + x *\<^sub>R \<Sum> (Basis - {(0, 1)})) * indicat_real s ((0, y) + x *\<^sub>R \<Sum> (Basis - {(0, 1)})))) \<in> borel_measurable borel"
    apply(simp add: 4)
    apply(subst sym[OF lmeasure_integral_UNIV])
    apply(simp only: fmeasurable_def s\<^sub>x_finite_lebesgue)
    by (auto simp add: assms(2) fmeasurable_def s\<^sub>x_finite_lebesgue)
  show ?thesis
    apply(subst analytically_valid_def)
    by(auto simp add: p_diffble cont_on integrable borel_measurable)
qed

lemma x_analytically_valid:
  fixes s :: "(real\<times>real) set"
  assumes "compact s" "(\<lambda>y. measure lebesgue {x. (x, y) \<in> s}) \<in> borel_measurable borel" (*this assumption will follow from s have typeI division*)
  shows "analytically_valid s (\<lambda> x. fst x) (1,0)"
proof -
  have "has_partial_vector_derivative (\<lambda>x. fst x) (1, 0) (1) (a, b)" for a b ::real
    by(auto simp add: has_partial_vector_derivative_def has_vector_derivative_minus)
  hence has_p_deriv: "has_partial_vector_derivative (\<lambda>x. fst x) (1, 0) (1) z" for z ::"real\<times>real"
    using prod_cases by blast
  hence p_diffble: "partially_vector_differentiable (\<lambda>x. fst x) (1,0) (a, b)" for a b ::real
    unfolding partially_vector_differentiable_def by auto
  have cont_on: "continuous_on s (\<lambda>x. fst x)"
    using continuous_on_fst[OF continuous_on_id'] by simp
  have p_deriv_minus_1: "partial_vector_derivative (\<lambda>x. fst x) (1,0) p = 1" for p ::"real\<times>real"
    using has_p_deriv p_deriv_from_has_p_deriv by blast
  have integrable: "integrable lborel (\<lambda>p. partial_vector_derivative (\<lambda>x. fst x) (1,0) p * indicat_real s p)"
    apply(simp add: p_deriv_minus_1)
    using integrable_real_indicator assms
    by (metis borel_compact emeasure_compact_finite sets_lborel)
  have sum_Basis_minus_y: "\<Sum> ({(1::real, 0), (0, 1)} - {(1, 0)}) = (0,1)"
    apply(rule subst[of "{(0,1)}"])
    by(auto)
  have s\<^sub>x_indicat: "(\<lambda>x. indicat_real s (x, y)) = indicat_real {x. (x,y)\<in>s}" for y ::real
    apply(subst indicator_def)+
    by fastforce
  have s\<^sub>x_emb_closed: "closed {x. (x, y) \<in> s}" for y::real
    by (auto simp add: closed_cross_sections compact_imp_closed assms)
  have "bounded {x. (x, y) \<in> s}" for y::real
    by (simp add: bounded_cross_sections compact_imp_bounded assms)
  hence "emeasure lborel {x. (x, y) \<in> s} < \<infinity>" for y::real
    using emeasure_bounded_finite by auto
  hence s\<^sub>x_finite_lebesgue: "{x. (x, y) \<in> s} \<in> {A \<in> sets lebesgue. emeasure lebesgue A < \<infinity>}" for y::real
    by (auto simp add: s\<^sub>x_emb_closed emeasure_bounded_finite)
  have 4: "(\<lambda>y. integral UNIV (\<lambda>x. partial_vector_derivative (\<lambda>x. fst x) (1,0) ((x, 0::real) + y *\<^sub>R \<Sum> (Basis - {(1, 0)})) * indicat_real s ((x, 0) + y *\<^sub>R \<Sum> (Basis - {(1,0)}))))
              = (\<lambda>y. integral UNIV (indicat_real {x. (x, y) \<in> s}))"
    apply(simp only: p_deriv_minus_1 real_pair_basis sum_Basis_minus_y scaleR_Pair sym[OF s\<^sub>x_indicat])
    by(auto)
  have borel_measurable: "(\<lambda>y. integral UNIV (\<lambda>x. partial_vector_derivative (\<lambda>x. fst x) (1,0) ((x, 0::real) + y *\<^sub>R \<Sum> (Basis - {(1,0)})) * indicat_real s ((x,0) + y *\<^sub>R \<Sum> (Basis - {(1,0)})))) \<in> borel_measurable borel"
    apply(simp add: 4)
    apply(subst sym[OF lmeasure_integral_UNIV])
    apply(simp only: fmeasurable_def s\<^sub>x_finite_lebesgue)
    by (auto simp add: assms(2) fmeasurable_def s\<^sub>x_finite_lebesgue)
  show ?thesis
    apply(subst analytically_valid_def)
    by(auto simp add: p_diffble cont_on integrable borel_measurable)
qed

locale isop1 = R2 i j + G1: green_typeI_typeII_chain s i j "(\<lambda> (x,y). (-y , 0))" two_chain_typeI two_chain_typeII for i j s two_chain_typeI two_chain_typeII
begin

lemma area_as_line_integral:
  assumes
      "gen_division s (cubeImage ` two_chain_typeI)"
      "gen_division s (cubeImage ` two_chain_typeII)"
      "two_chain_horizontal_boundary two_chain_typeI \<subseteq> one_chain_typeI"
      "two_chain_vertical_boundary two_chain_typeII \<subseteq> one_chain_typeII" 
      "one_chain_typeI \<subseteq> two_chain_boundary two_chain_typeI"
      "one_chain_typeII \<subseteq> two_chain_boundary two_chain_typeII"
      "common_boundary_sudivision_exists one_chain_typeI one_chain_typeII"
  shows "integral s (\<lambda>x. 1) = one_chain_line_integral (\<lambda> (x,y). (-y , 0)) {i} one_chain_typeI"
    "integral s (\<lambda>x. 1) = one_chain_line_integral (\<lambda> (x,y). (-y , 0)) {i} one_chain_typeII"
proof -
  let ?F = "(\<lambda> (x,y). (-y , 0))"
  have curl_F: "integral s (\<lambda>x. 1) = integral s (\<lambda>x. partial_vector_derivative (\<lambda>x. (?F x) \<bullet> j) i x - partial_vector_derivative (\<lambda>x. (?F x) \<bullet> i) j x)"
  proof -
    let ?F_a' = "partial_vector_derivative (\<lambda>a. ?F a \<bullet> j) i"
    let ?F_b' = "partial_vector_derivative (\<lambda>a. ?F a \<bullet> i) j"
    have "?F_a' x = 0" for x using i_is_x_axis j_is_y_axis
      apply(subst partial_vector_derivative_def)
      apply(cases x)
      by auto
    moreover have "?F_b' x = - 1" for x using i_is_x_axis j_is_y_axis
      apply(subst partial_vector_derivative_def)
      apply(cases x)
      by auto
    ultimately show ?thesis by auto
  qed
  have area_from_F: 
    "integral s (\<lambda>x. 1) = one_chain_line_integral ?F {i, j} one_chain_typeI"
    "integral s (\<lambda>x. 1) = one_chain_line_integral ?F {i, j} one_chain_typeII"
    apply(subst curl_F)
     apply(rule Green.green_typeI_typeII_chain.GreenThm_typeI_typeII_divisible_region_equivallent_boundary)
            apply(rule G1.green_typeI_typeII_chain_axioms)
           apply(rule assms)+
    apply(subst curl_F)
    apply(rule Green.green_typeI_typeII_chain.GreenThm_typeI_typeII_divisible_region_equivallent_boundary[of _ _ _ _ _ _ one_chain_typeI])
           apply(rule G1.green_typeI_typeII_chain_axioms)                                                                                                                         
    by(rule assms)+
  show "integral s (\<lambda>x. 1) = one_chain_line_integral (\<lambda> (x,y). (-y , 0)) {i} one_chain_typeI"
    using i_is_x_axis j_is_y_axis
    apply(subst area_from_F(1))
    apply(simp add: one_chain_line_integral_def line_integral_def)
     apply(rule Finite_Cartesian_Product.sum_cong_aux)
    by (auto split: prod.splits intro: Henstock_Kurzweil_Integration.integral_cong)
  show "integral s (\<lambda>x. 1) = one_chain_line_integral (\<lambda> (x,y). (-y , 0)) {i} one_chain_typeII"
    using i_is_x_axis j_is_y_axis
    apply(subst area_from_F(2))
    apply(simp add: one_chain_line_integral_def line_integral_def)
     apply(rule Finite_Cartesian_Product.sum_cong_aux)
    by (auto split: prod.splits intro: Henstock_Kurzweil_Integration.integral_cong)
qed
end

locale isop2 = R2 i j + G1: green_typeI_typeII_chain s i j "(\<lambda> (x,y). (0 , x))" two_chain_typeI two_chain_typeII for i j s two_chain_typeI two_chain_typeII
  
begin

lemma area_as_line_integral:
  assumes
    green_assumptions:
      "gen_division s (cubeImage ` two_chain_typeI)"
      "gen_division s (cubeImage ` two_chain_typeII)"
      "two_chain_horizontal_boundary two_chain_typeI \<subseteq> one_chain_typeI"
      "two_chain_vertical_boundary two_chain_typeII \<subseteq> one_chain_typeII" 
      "one_chain_typeI \<subseteq> two_chain_boundary two_chain_typeI"
      "one_chain_typeII \<subseteq> two_chain_boundary two_chain_typeII"
      "common_boundary_sudivision_exists one_chain_typeI one_chain_typeII"
    shows "integral s (\<lambda>x. 1) = one_chain_line_integral (\<lambda> (x,y). (0 , x)) {j} one_chain_typeI"
    "integral s (\<lambda>x. 1) = one_chain_line_integral (\<lambda> (x,y). (0 , x)) {j} one_chain_typeII"
proof -
  let ?F = "(\<lambda> (x,y). (0 , x))"
   have curl_F: "integral s (\<lambda>x. 1) = integral s (\<lambda>x. partial_vector_derivative (\<lambda>x. (?F x) \<bullet> j) i x - partial_vector_derivative (\<lambda>x. (?F x) \<bullet> i) j x)"
  proof -
    let ?F_a' = "partial_vector_derivative (\<lambda>a. ?F a \<bullet> j) i"
    let ?F_b' = "partial_vector_derivative (\<lambda>a. ?F a \<bullet> i) j"
    have "?F_a' x = 1" for x using i_is_x_axis j_is_y_axis
      apply(subst partial_vector_derivative_def)
      apply(cases x)
      by auto
    moreover have "?F_b' x = 0" for x using i_is_x_axis j_is_y_axis
      apply(subst partial_vector_derivative_def)
      apply(cases x)
      by auto
    ultimately show ?thesis by auto
  qed
  have area_from_F: 
    "integral s (\<lambda>x. 1) = one_chain_line_integral ?F {i, j} one_chain_typeI"
    "integral s (\<lambda>x. 1) = one_chain_line_integral ?F {i, j} one_chain_typeII"
    apply(subst curl_F)
     apply(rule Green.green_typeI_typeII_chain.GreenThm_typeI_typeII_divisible_region_equivallent_boundary)
            apply(rule G1.green_typeI_typeII_chain_axioms)
           apply(rule assms)+
    apply(subst curl_F)
    apply(rule Green.green_typeI_typeII_chain.GreenThm_typeI_typeII_divisible_region_equivallent_boundary[of _ _ _ _ _ _ one_chain_typeI])
           apply(rule G1.green_typeI_typeII_chain_axioms)
    by(rule assms)+
  show "integral s (\<lambda>x. 1) = one_chain_line_integral (\<lambda> (x,y). (0 , x)) {j} one_chain_typeI"
    using i_is_x_axis j_is_y_axis
    apply(subst area_from_F(1))
    apply(simp add: one_chain_line_integral_def line_integral_def)
     apply(rule Finite_Cartesian_Product.sum_cong_aux)
    by (auto split: prod.splits intro: Henstock_Kurzweil_Integration.integral_cong)
  show "integral s (\<lambda>x. 1) = one_chain_line_integral (\<lambda> (x,y). (0 , x)) {j} one_chain_typeII"
    using i_is_x_axis j_is_y_axis
    apply(subst area_from_F(2))
    apply(simp add: one_chain_line_integral_def line_integral_def)
     apply(rule Finite_Cartesian_Product.sum_cong_aux)
    by (auto split: prod.splits intro: Henstock_Kurzweil_Integration.integral_cong)
qed
end

locale isop = isop1 i j s two_chain_typeI two_chain_typeII + isop2 i j s two_chain_typeI two_chain_typeII for s i j two_chain_typeI two_chain_typeII +
assumes
    green_assumptions:
      "gen_division s (cubeImage ` two_chain_typeI)"
      "gen_division s (cubeImage ` two_chain_typeII)"
      "two_chain_horizontal_boundary two_chain_typeI \<subseteq> one_chain_typeI"
      "two_chain_vertical_boundary two_chain_typeII \<subseteq> one_chain_typeII" 
      "one_chain_typeI \<subseteq> two_chain_boundary two_chain_typeI"
      "one_chain_typeII \<subseteq> two_chain_boundary two_chain_typeII"
      "common_boundary_sudivision_exists one_chain_typeI one_chain_typeII"
begin
(*Unsure which form (i.e which combinations of one_chain_typeI and one_chain_typeII) of this lemma I will need in the final proof*)
lemma shows area_from_line_integral: "integral s (\<lambda>x. 1) = (1/2) * (one_chain_line_integral (\<lambda>(x,y). (0,x)) {j} one_chain_typeI + one_chain_line_integral (\<lambda>(x,y). (-y,0)) {i} one_chain_typeI)"
proof -
  thm isop1.area_as_line_integral
  have "integral s (\<lambda>x. 1) = one_chain_line_integral (\<lambda>(x, y). (- y, 0)) {i} one_chain_typeI"
    apply(rule isop1.area_as_line_integral)
    apply(rule isop1_axioms)
    by(rule green_assumptions isop1_axioms)+
  moreover have "integral s (\<lambda>x. 1) = one_chain_line_integral (\<lambda>(x,y). (0,x)) {j} one_chain_typeI"
    apply(rule isop2.area_as_line_integral)
    apply(rule isop2_axioms)
    by(rule green_assumptions isop1_axioms)+
  ultimately show ?thesis by auto
qed
end

lemma geom_le_arith_mean:
  fixes a::real and b::real
  assumes a: "a\<ge>0" and b: "b\<ge>0"
  shows "sqrt (a*b) \<le> (a + b)/2 \<and> (sqrt (a*b) = (a + b)/2 \<longleftrightarrow> a = b)"
proof-
  have "(a-b)\<^sup>2 \<ge> 0" by auto
  hence "a * (b * 2) \<le> a\<^sup>2 + b\<^sup>2"
    by (auto simp add: Power.comm_ring_1_class.power2_diff)
  hence "a*b \<le> ((a+b)/2)\<^sup>2" using a b
    by (auto simp add: Power.comm_semiring_1_class.power2_sum Power.field_class.power_divide)
  hence 0: "sqrt (a*b) \<le> (a + b)/2" using a b
    apply(subst sym[OF Groups.ordered_ab_group_add_abs_class.abs_of_nonneg[of "(a + b)/2"]])
     apply(simp)
    apply(subst sym [OF NthRoot.root_abs_power[of 2]])
    by (auto simp add: sqrt_def NthRoot.real_root_abs)
  have "(a-b)\<^sup>2 = 0 \<longleftrightarrow> a = b" by auto
  hence "a * (b * 2) = a\<^sup>2 + b\<^sup>2 \<longleftrightarrow> a = b"
    by (auto simp add: Power.comm_ring_1_class.power2_diff)
  hence "a*b = ((a+b)/2)\<^sup>2 \<longleftrightarrow> a = b" using a b
    by (auto simp add: Power.comm_semiring_1_class.power2_sum Power.field_class.power_divide)
  hence 1: "sqrt (a*b) = (a + b)/2 \<longleftrightarrow> a = b" using a b
    apply(subst sym[OF Groups.ordered_ab_group_add_abs_class.abs_of_nonneg[of "(a + b)/2"]])
     apply(simp)
    apply(subst sym [OF NthRoot.root_abs_power[of 2]])
    by (auto simp add: sqrt_def NthRoot.real_root_abs)
  thus ?thesis using 0 1
    by auto
qed

lemma
  fixes A s r:: real
  assumes "A + pi*r\<^sup>2 \<le> l*r" "A\<ge>0" "l\<ge>0" "r>0"
  shows "l\<^sup>2 - 4*pi*A \<ge> 0" "l\<^sup>2 - 4*pi*A = 0 \<Longrightarrow> l = 2*pi*r" (*Setting l = 2\<times>pi\<times>r, we get A \<le> pi\<times>r\<^sup>2 *)
proof -
  have l_r_sqr:"(l*r/2) ^ 2 = l\<^sup>2 * r\<^sup>2 / 4"
    by (simp add: power_divide power_mult_distrib)
  have 0: "sqrt (A*(pi*r\<^sup>2)) \<le> (A + (pi*r\<^sup>2))/2  \<and> (sqrt (A*(pi*r\<^sup>2)) = (A + pi*r\<^sup>2)/2 \<longleftrightarrow> A = pi*r\<^sup>2)"
    using geom_le_arith_mean assms(2) by fastforce
  hence "A*(pi*r\<^sup>2) \<le> (l*r/2)\<^sup>2"
    using sqrt_def sqrt_le_D assms(1) by force
  hence "A*(pi*r\<^sup>2)*4 \<le> l\<^sup>2 * r\<^sup>2"
    using l_r_sqr by linarith
  thus "l\<^sup>2 - 4*pi*A \<ge> 0"
    using assms(4) by (auto simp add: mult.commute mult.left_commute)
  have "l\<^sup>2 - 4*pi*A = 0 \<longleftrightarrow> (4*pi*A)*r\<^sup>2 = l\<^sup>2 * r\<^sup>2"
    using assms(4) by auto
  hence "l\<^sup>2 - 4*pi*A = 0 \<longleftrightarrow> A*(pi*r\<^sup>2)*4 = l\<^sup>2 * r\<^sup>2"
    by (simp add: assms(4) mult.commute mult.left_commute)
  hence "l\<^sup>2 - 4*pi*A = 0 \<longleftrightarrow> A*(pi*r\<^sup>2) = l\<^sup>2 * r\<^sup>2 / 4"
    using eq_divide_eq_numeral1(1) by simp
  hence "l\<^sup>2 - 4*pi*A = 0 \<longleftrightarrow> sqrt (A*(pi*r\<^sup>2)) = sqrt (l\<^sup>2 * r\<^sup>2 / 4)"
    using real_sqrt_eq_iff by auto
  hence "l\<^sup>2 - 4*pi*A = 0 \<longleftrightarrow> sqrt (A*(pi*r\<^sup>2)) = l * r / 2"
    using l_r_sqr real_sqrt_unique[of "l*r/2"] assms by(auto)
  hence "l\<^sup>2 - 4*pi*A = 0 \<Longrightarrow> A = pi*r\<^sup>2"
    using assms(1) 0 by auto
  hence "l\<^sup>2 - 4*pi*A = 0 \<Longrightarrow> l\<^sup>2 = 4*pi\<^sup>2*r\<^sup>2"
    by (simp add: power2_eq_square)
  moreover have "4*pi\<^sup>2*r\<^sup>2 = (2*pi*r)\<^sup>2"
    by (metis four_x_squared power_mult_distrib)
  ultimately show "l\<^sup>2 - 4*pi*A = 0 \<Longrightarrow> l = 2*pi*r"
    using assms by auto
qed

lemma func_square_sum :
  fixes w x y z :: "real \<Rightarrow> real"
  shows "\<forall> t. (x t * y t - z t * w t)\<^sup>2 \<le> ((x t)\<^sup>2 + (z t)\<^sup>2)*((w t)\<^sup>2 + (y t)\<^sup>2) \<and> ((x t * y t - z t * w t)\<^sup>2 = ((x t)\<^sup>2 + (z t)\<^sup>2)*((w t)\<^sup>2 + (y t)\<^sup>2) \<longleftrightarrow> x t* w t = - z t* y t)"
proof
  fix t
  let ?w = "w t"
  let ?x = "x t"
  let ?y = "y t"
  let ?z = "z t"
  have 0: "((?x\<^sup>2 + ?z\<^sup>2) * (?w\<^sup>2 + ?y\<^sup>2)) - (?x*?y - ?z*?w)\<^sup>2 = (?x*?w + ?z*?y)\<^sup>2"
    by (auto simp add: algebra_simps Power.comm_semiring_1_class.power2_sum Power.comm_ring_1_class.power2_diff)
  hence "... \<ge> 0"by simp
  hence 1: "(?x*?y - ?z*?w)\<^sup>2 \<le> (?x\<^sup>2 + ?z\<^sup>2)*(?w\<^sup>2 + ?y\<^sup>2)" using 0
    by (auto simp add: algebra_simps)
  have 2: "(?x*?y - ?z*?w)\<^sup>2 - (?x\<^sup>2 + ?z\<^sup>2)*(?w\<^sup>2 + ?y\<^sup>2) = 0 \<longleftrightarrow> (?x*?w + ?z*?y)\<^sup>2 = 0" using 0 by auto
  show "(?x*?y - ?z*?w)\<^sup>2 \<le> (?x\<^sup>2 + ?z\<^sup>2)*(?w\<^sup>2 + ?y\<^sup>2) \<and> ((?x*?y - ?z*?w)\<^sup>2 = (?x\<^sup>2 + ?z\<^sup>2)*(?w\<^sup>2 + ?y\<^sup>2) \<longleftrightarrow> ?x*?w = -?z*?y)" using 1 2 by auto
qed

lemma
  fixes w x y z :: "real \<Rightarrow> real" and S ::"real set"
  assumes "integrable lebesgue (\<lambda>t. (x t * y t - z t * w t)\<^sup>2)" "integrable lebesgue (\<lambda>t. ((x t)\<^sup>2 + (z t)\<^sup>2)*((w t)\<^sup>2 + (y t)\<^sup>2))" "integral\<^sup>L lebesgue (\<lambda>t. (x t * y t - z t * w t)\<^sup>2) = integral\<^sup>L lebesgue (\<lambda>t. ((x t)\<^sup>2 + (z t)\<^sup>2)*((w t)\<^sup>2 + (y t)\<^sup>2))"
  shows "AE t in lebesgue. (\<lambda>t. x t * w t) t = (\<lambda>t. - z t * y t) t"
proof -
  have "(x t * y t - z t * w t)\<^sup>2 \<le> ((x t)\<^sup>2 + (z t)\<^sup>2) * ((w t)\<^sup>2 + (y t)\<^sup>2)" for t
    using func_square_sum[of x y z w] by blast
  have "integrable lebesgue (\<lambda>t. ((x t)\<^sup>2 + (z t)\<^sup>2)*((w t)\<^sup>2 + (y t)\<^sup>2) - (x t * y t - z t * w t)\<^sup>2)"
    by (simp add: assms)
  moreover have "integral\<^sup>L lebesgue (\<lambda>t. ((x t)\<^sup>2 + (z t)\<^sup>2)*((w t)\<^sup>2 + (y t)\<^sup>2) - (x t * y t - z t * w t)\<^sup>2) = 0"
    using assms by auto
  ultimately have 0: "AE t in lebesgue. (\<lambda>t. ((x t)\<^sup>2 + (z t)\<^sup>2)*((w t)\<^sup>2 + (y t)\<^sup>2) - (x t * y t - z t * w t)\<^sup>2) t = 0"
    apply (subst sym[OF integral_nonneg_eq_0_iff_AE])
    by(auto simp add: func_square_sum)
  have "(((x t)\<^sup>2 + (z t)\<^sup>2)*((w t)\<^sup>2 + (y t)\<^sup>2) - (x t * y t - z t * w t)\<^sup>2 = 0) = (x t * w t = - z t * y t)" for t
    using func_square_sum by force
  thus ?thesis using 0
    by presburger
qed

(*
Let p be a path, so p is a map from an interval I to the plane, p :  I \<rightarrow> \<real>\<^sup>2, and suppose it is injective on I (ignoring endpoints).
>>> inj_on p (I - {Max I})

We want an arclength parametrisation, or at least a constant speed parametrisation for p on the interval I.
So a function s : I \<rightarrow> J, such that p \<circ> s\<^sup>-\<^sup>1 : J \<rightarrow> \<real>\<^sup>2 has derivative of constant magnitude at all points in I.

If s is defined as s(t) =  \<integral>\<^sub>a\<^sup>t sqrt((x')\<^sup>2 + (y')\<^sup>2), this will make p \<circ> s\<^sup>-\<^sup>1 the arclength parametrisation.
We need s to have a well-defined inverse, so the integrand, sqrt((x')\<^sup>2 + (y')\<^sup>2), is never 0, i.e  p is always moving. 
If we guarantee p is injective on the range I then logically the integrand should never be 0?
We need a lemma which says "inj_on p I \<Longrightarrow> \<forall>t\<in>I. sqrt((x' t)\<^sup>2 + (y' t)\<^sup>2) \<noteq> 0"
But is this true...

I think we need "sqrt((x' t)\<^sup>2 + (y' t)\<^sup>2)" to be at least \<alpha> (where \<alpha> > 0) at all points so that
s has a well-defined inverse. (Equivalently "sqrt((x')\<^sup>2 + (y')\<^sup>2)" is non-zero and continuous on a closed range.)

If we have an \<alpha> > 0, st.  sqrt((x' t)\<^sup>2 + (y' t)\<^sup>2) > \<alpha> at all points t \<in> I,
Then we have \<integral>\<^sub>a\<^sup>t sqrt((x')\<^sup>2 + (y')\<^sup>2) \<ge>  \<integral>\<^sub>a\<^sup>t \<alpha> = \<alpha> (t - a)

Suppose b > a, and s(b) = s(
a) (i.e s does not have a well-defined inverse),
then \<integral>\<^sub>a\<^sup>b sqrt((x')\<^sup>2 + (y')\<^sup>2) \<ge>  \<integral>\<^sub>a\<^sup>b \<alpha> = (b-a)\<alpha> > 0 , giving a contradiction.
So if we have an \<alpha> > 0, st.  sqrt((x' t)\<^sup>2 + (y' t)\<^sup>2) > \<alpha> at all points t \<in> I,
this will guarantee that s is increasing and injective, which will guarantee a well-defined inverse.

A regularly parametrised curve (RPC) is a smooth curve who's derivative never vanishes. We need our curve to be piecewise regularly parametrised.
*)



end