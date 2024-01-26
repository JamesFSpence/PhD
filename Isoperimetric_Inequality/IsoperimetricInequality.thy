theory IsoperimetricInequality
  imports Intervals "$AFP/Green/Green"
begin

lemma p_deriv_from_has_p_deriv: assumes "has_partial_vector_derivative F b F' p"
  shows "partial_vector_derivative F b p = F'"
  by (metis assms has_partial_vector_derivative_def partial_vector_derivative_def vector_derivative_at)

lemma fixes f::"(real\<times>real) \<Rightarrow> (real\<times>real)"
  assumes "continuous_on s f" "compact s"
  shows "compact (f ` s)"
  by (auto simp add: compact_continuous_image assms)
(*The lemma above tells us that if we condition that each two chain be a continuous map, then their images will be compact,
and therefore s will be closed and bounded, and so the union of these will be compact (as there are a finite number of two chains)
and so each cross section s\<^sub>x and s\<^sub>y will be a closed set (and so lebesgue measurable)*)

(*Add as a theorem that the cross section of a closed set is also closed*)

lemma
  fixes s :: "(real\<times>real) set"
  assumes "compact s"
  shows "analytically_valid s (\<lambda> x. - snd x) (0,1)"
proof -
  have minus_y_zero: "has_partial_vector_derivative (\<lambda>x. -snd x) (0, 1) (-1) (a, b)" for a b ::real
    by(auto simp add: has_partial_vector_derivative_def has_vector_derivative_minus)
  hence has_p_deriv: "has_partial_vector_derivative (\<lambda>x. - snd x) (0, 1) (-1) z" for z ::"real\<times>real"
    using prod_cases by blast
  hence ex_has_p_deriv: "\<exists>F'. has_partial_vector_derivative (\<lambda>x. - snd x) (0, 1) F' z" for z ::"real\<times>real"
    by blast
  have cont_on: "continuous_on s (\<lambda>x. - snd x)"
    using continuous_on_minus[OF continuous_on_snd[OF continuous_on_id']]
    by (simp add: case_prod_unfold)
  have p_deriv_minus_1: "partial_vector_derivative (\<lambda>x. - snd x) (0, 1) p = - 1" for p ::"real\<times>real"
    apply -
    apply(rule p_deriv_from_has_p_deriv)
    using has_p_deriv by(auto)
  hence "(\<lambda>p. partial_vector_derivative (\<lambda>x. - snd x) (0, 1) p * indicat_real s p) = (\<lambda>p. - indicat_real s p)"
    by auto
  hence integrable: "integrable lborel (\<lambda>p. partial_vector_derivative (\<lambda>x. - snd x) (0, 1) p * indicat_real s p)"
    apply(simp)
    apply(intro integrable_real_indicator assms emeasure_bounded_finite)
    apply(subst sets_lborel)
    by(auto intro: borel_compact assms compact_imp_bounded)
  have Basis_minus_y:"{(1::real, 0), (0, 1)} - {(0, 1)} = {(1,0)}"
    by auto
  hence sum_Basis_minus_y: "\<Sum> ({(1::real, 0), (0, 1)} - {(0, 1)}) = (1,0)"
    apply (subst Basis_minus_y)
    by(simp)
  have s\<^sub>x_def: "(\<lambda>y. indicat_real s (x, y)) = indicat_real {y. (x,y)\<in>s}" for x ::real
    apply(subst indicator_def)+
    by fastforce
  have "closed {x. (1::real,0::real) \<bullet> x = 0}"
    by (simp add: closed_hyperplane)
  moreover have "{(a::real,b::real). a = 0} = {x. (1::real,0::real) \<bullet> x = 0}"
    by auto
  ultimately have 0: "closed {(a::real,b::real). a = 0}"
    by auto
  have "{(a::real,b::real). a = x} = ((+) (x,0)) `  {(a,b). a = 0}" for x::real
    by(auto split: prod.splits simp add: image_def)
  moreover have "closed (((+) (x,0)) `  {(a::real,b::real). a = 0})" for x::real
    using closed_translation[OF 0, of "(x,0)"] by simp
  ultimately have 1: "closed {(a::real,b::real). a = x}" for x::real
    by metis
  have 2: "{(a,b). a = x \<and> (a,b) \<in> s} = s \<inter> {(a,b). a = x}" for x::real
    by blast
  have "closed {(a,b). a = x \<and> (a,b) \<in> s}" for x::real
    by(auto simp add: 1 2 compact_imp_closed assms)
  hence s\<^sub>x_compact: "compact {(a,b). a = x \<and> (a,b) \<in> s}" for x::real
    by (simp add: "1" "2" assms compact_Int_closed)
  have 3: "snd ` {(a,b). a = x \<and> (a,b) \<in> s} =  {y. (x, y) \<in> s}" for x::real
    by(auto simp add: image_def snd_def)
  have "closed s"
    using assms by (auto simp add: compact_imp_closed)
  have s\<^sub>x_emb_closed: "closed {y. (x, y) \<in> s}" for x::real
  proof -
    have "(\<forall>z l. (\<forall>n. z n \<in> s) \<and> z \<longlonglongrightarrow> l \<longrightarrow> l \<in> s)"
      using \<open>closed s\<close> closed_sequential_limits by auto
    hence z_pair_tends: "\<forall>z l. (\<forall>n. (x, z n) \<in> s) \<and> (\<lambda>n. (x, z n)) \<longlonglongrightarrow> (x,l) \<longrightarrow> (x,l)\<in>s"
      by(auto)
    have "(\<forall>n. z n \<in> {y. (x, y) \<in> s}) \<and> z \<longlonglongrightarrow> l \<longrightarrow> l \<in> {y. (x, y) \<in> s}" for z l
    proof -
      have "(\<forall>n. z n \<in> {y. (x, y) \<in> s}) \<and> z \<longlonglongrightarrow> l \<Longrightarrow> (\<lambda>n. (x, z n)) \<longlonglongrightarrow> (x,l)"
        by (simp add: tendsto_Pair)
      hence "(\<forall>n. z n \<in> {y. (x, y) \<in> s}) \<and> z \<longlonglongrightarrow> l \<Longrightarrow> (x,l) \<in> s" using z_pair_tends
        by auto
      thus ?thesis by auto
    qed
    thus ?thesis using closed_sequential_limits[of "{y. (x, y) \<in> s}"]
      by auto
  qed
  have "bounded {y. (x, y) \<in> s}" for x::real
    by (metis (mono_tags, lifting) "3" bounded_snd compact_imp_bounded s\<^sub>x_compact)
  hence "emeasure lborel {y. (x, y) \<in> s} < \<infinity>" for x::real
    using emeasure_bounded_finite by auto
  hence "emeasure lebesgue {y. (x, y) \<in> s} < \<infinity>" for x::real
    by(auto simp add: s\<^sub>x_emb_closed)
  hence s\<^sub>x_finite_lebesgue: "{y. (x, y) \<in> s} \<in> {A \<in> sets lebesgue. emeasure lebesgue A < \<infinity>}" for x::real
    by (auto simp add: s\<^sub>x_emb_closed)
  thm emeasure_bounded_finite
  show ?thesis
  apply(subst analytically_valid_def)
    apply(rule conjI)
    apply(simp)
     apply(subst partially_vector_differentiable_def)
     apply(simp add: ex_has_p_deriv)
    apply(rule conjI)
     apply(rule cont_on)
    apply(rule conjI)
     apply(rule integrable)
    apply(subst p_deriv_minus_1)
    apply(subst real_pair_basis)
    apply(subst sum_Basis_minus_y)
    apply(subst scaleR_Pair)+
    apply(simp)
    apply(subst s\<^sub>x_def)
    apply(subst sym[OF Equivalence_Lebesgue_Henstock_Integration.lmeasure_integral_UNIV])
     apply(subst fmeasurable_def)
     apply(rule s\<^sub>x_finite_lebesgue)
    sorry
qed

find_theorems "_ \<in> borel_measurable borel"
find_theorems "measure lebesgue"
  (*each cross section s\<^sub>x needs to be lebesgue measurable for analytically valid s f j to hold
    likewise for s\<^sub>y.*)
find_theorems name: "section"
find_theorems "{y. (?x,y) \<in> ?s}"
find_theorems "emeasure lebesgue"
term fmeasurable
find_theorems "?s \<inter> ?t \<in> sets _"
find_theorems "_ \<in> lmeasurable"
find_theorems "measurable" snd

find_theorems "norm::(_ \<times> _) \<Rightarrow> _"

locale isop1 = R2 i j + G1: green_typeI_typeII_chain s i j "(\<lambda> (x,y). (-y , 0))" two_chain_typeI two_chain_typeII for i j s two_chain_typeI two_chain_typeII +
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

lemma area_C:
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
           apply(rule green_assumptions)+
    apply(subst curl_F)
    apply(rule Green.green_typeI_typeII_chain.GreenThm_typeI_typeII_divisible_region_equivallent_boundary)
           apply(rule G1.green_typeI_typeII_chain_axioms)
    by(rule green_assumptions)+
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

thm line_integral_def one_chain_line_integral_def

locale isop2 = R2 i j + G1: green_typeI_typeII_chain s i j "(\<lambda> (x,y). (0 , x))" two_chain_typeI two_chain_typeII for i j s two_chain_typeI two_chain_typeII +
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

lemma area_C:
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
           apply(rule green_assumptions)+
    apply(subst curl_F)
    apply(rule Green.green_typeI_typeII_chain.GreenThm_typeI_typeII_divisible_region_equivallent_boundary)
           apply(rule G1.green_typeI_typeII_chain_axioms)
    by(rule green_assumptions)+
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

thm isop1.area_C isop2.area_C
thm isop1_def
thm isop1_axioms_def

locale isop = isop1 i j s two_chain_typeI two_chain_typeII + isop2 i j s two_chain_typeI two_chain_typeII for s i j two_chain_typeI two_chain_typeII
begin
lemma shows area_from_line_integral: "integral s (\<lambda>x. 1) = (1/2) * (one_chain_line_integral (\<lambda>(x,y). (0,x)) {j} one_chain_typeI + one_chain_line_integral (\<lambda>(x,y). (-y,0)) {i} one_chain_typeI)"
proof -
  show ?thesis using local.isop2_axioms local.isop1_axioms isop1.area_C isop2.area_C by auto
qed
end

lemma func_square_sum :
  fixes w :: "real \<Rightarrow> real" and x :: "real \<Rightarrow> real" and y :: "real \<Rightarrow> real" and z :: "real \<Rightarrow> real"
  shows "\<forall> t. (x t * y t - z t * w t)\<^sup>2 \<le> ((x t)\<^sup>2 + (z t)\<^sup>2)*((w t)\<^sup>2 + (y t)\<^sup>2) \<and> ((x t * y t - z t * w t)\<^sup>2 = ((x t)\<^sup>2 + (z t)\<^sup>2)*((w t)\<^sup>2 + (y t)\<^sup>2) \<longleftrightarrow> x t* w t= - z t* y t)"
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

lemma geom_le_arith_mean:
  fixes a::real and b::real
  assumes a: "a\<ge>0" and b: "b\<ge>0"
  shows "root 2 (a*b) \<le> (a + b)/2 \<and> (root 2 (a*b) = (a + b)/2 \<longleftrightarrow> a = b)"
proof-
  have "(a-b)\<^sup>2 \<ge> 0" by auto
  hence "a * (b * 2) \<le> a\<^sup>2 + b\<^sup>2"
    by (auto simp add: Power.comm_ring_1_class.power2_diff)
  hence "a*b \<le> ((a+b)/2)\<^sup>2" using a b
    by (auto simp add: Power.comm_semiring_1_class.power2_sum Power.field_class.power_divide)
  hence 0: "root 2 (a*b) \<le> (a + b)/2" using a b
    apply(subst sym[OF Groups.ordered_ab_group_add_abs_class.abs_of_nonneg[of "(a + b)/2"]])
     apply(simp)
    apply(subst sym [OF NthRoot.root_abs_power[of 2]])
    by (auto simp add: NthRoot.real_root_abs)
  have "(a-b)\<^sup>2 = 0 \<longleftrightarrow> a = b" by auto
  hence "a * (b * 2) = a\<^sup>2 + b\<^sup>2 \<longleftrightarrow> a = b"
    by (auto simp add: Power.comm_ring_1_class.power2_diff)
  hence "a*b = ((a+b)/2)\<^sup>2 \<longleftrightarrow> a = b" using a b
    by (auto simp add: Power.comm_semiring_1_class.power2_sum Power.field_class.power_divide)
  hence 1: "root 2 (a*b) = (a + b)/2 \<longleftrightarrow> a = b" using a b
    apply(subst sym[OF Groups.ordered_ab_group_add_abs_class.abs_of_nonneg[of "(a + b)/2"]])
     apply(simp)
    apply(subst sym [OF NthRoot.root_abs_power[of 2]])
    by (auto simp add: NthRoot.real_root_abs)
  thus ?thesis using 0 1
    by auto
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

find_theorems name: Green.green_typeI_typeII_chain.GreenThm_typeI_typeII_divisible_region_boundary
find_theorems "_ \<Longrightarrow> green_typeI_typeII_chain _ _ _ _ _  _"


term lborel
term distr
term PiM
thm PiM_def
find_theorems "\<Prod> _"
thm lborel_def
term integral
thm integral_def

end