theory IsoperimetricInequality
  imports Intervals
begin
fun test::"nat \<Rightarrow> nat" where
"test _  = undefined"

lemma "test 0 = undefined" by auto

locale isop1 = R2 i j + G1: green_typeI_typeII_chain s i j "(\<lambda> (x,y). (-y , 0))" two_chain_typeI two_chain_typeII for i j s two_chain_typeI two_chain_typeII +
  assumes s_is_oneCube: "s = cubeImage C" and
    valid_cube_boundary: "\<forall>(k,\<gamma>)\<in>boundary C. valid_path \<gamma>" and
    vert_division: "only_vertical_division (boundary C) two_chain_typeI" and
    hori_division: "only_horizontal_division (boundary C) two_chain_typeII"
begin
lemma area_C:shows "integral (cubeImage C) (\<lambda>x. 1) = one_chain_line_integral (\<lambda>(x,y). (-y,0)) {i} (boundary C)"
proof - 
  let ?F = "(\<lambda> (x,y). (-y , 0))"
  have curl_f: "integral (cubeImage C) (\<lambda>x. partial_vector_derivative (\<lambda>x. (?F x) \<bullet> j) i x - partial_vector_derivative (\<lambda>x. (?F x) \<bullet> i) j x) = integral (cubeImage C) (\<lambda>x. 1)"
  proof -
    let ?F_b' = "partial_vector_derivative (\<lambda>a. ?F a \<bullet> i) j"
    let ?F_a' = "partial_vector_derivative (\<lambda>a. ?F a \<bullet> j) i"
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
  have area_from_F: "integral (cubeImage C) (\<lambda>x. 1) = one_chain_line_integral ?F {i, j} (boundary C)"
  proof -
    have "integral (cubeImage C) (\<lambda>x. partial_vector_derivative (\<lambda>x. ?F x \<bullet> j) i x - partial_vector_derivative (\<lambda>x. ?F x \<bullet> i) j x) =
                     one_chain_line_integral ?F {i, j} (boundary C)"
      apply(rule Green.green_typeI_typeII_chain.GreenThm_typeI_typeII_divisible_region_finite_holes)
          apply(rule local.G1.green_typeI_typeII_chain_axioms)
      by (auto simp add: valid_cube_boundary vert_division hori_division s_is_oneCube)
    thus ?thesis using curl_f by auto
  qed
  thus ?thesis using i_is_x_axis j_is_y_axis
    apply(simp add: area_from_F one_chain_line_integral_def line_integral_def)
    apply(rule Finite_Cartesian_Product.sum_cong_aux)
    by (auto split: prod.splits intro: Henstock_Kurzweil_Integration.integral_cong)
qed
end

locale isop2 = R2 i j + G1: green_typeI_typeII_chain s i j "(\<lambda> (x,y). (0 , x))" two_chain_typeI two_chain_typeII for i j s two_chain_typeI two_chain_typeII +
  assumes s_is_oneCube: "s = cubeImage C" and
    valid_cube_boundary: "\<forall>(k,\<gamma>)\<in>boundary C. valid_path \<gamma>" and
    vert_division: "only_vertical_division (boundary C) two_chain_typeI" and
    hori_division: "only_horizontal_division (boundary C) two_chain_typeII"
begin
lemma area_C: shows "integral (cubeImage C) (\<lambda>x. 1) = one_chain_line_integral (\<lambda>(x,y). (0,x)) {j} (boundary C)"
proof -
  let ?F = "(\<lambda> (x,y). (0 , x))"
  have  curl_f: "integral (cubeImage C) (\<lambda>x. partial_vector_derivative (\<lambda>x. (?F x) \<bullet> j) i x - partial_vector_derivative (\<lambda>x. (?F x) \<bullet> i) j x) = integral (cubeImage C) (\<lambda>x. 1)"
  proof -
    let ?F_b' = "partial_vector_derivative (\<lambda>a. ?F a \<bullet> i) j"
    let ?F_a' = "partial_vector_derivative (\<lambda>a. ?F a \<bullet> j) i"
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
  have area_from_F: "integral (cubeImage C) (\<lambda>x. 1) = one_chain_line_integral ?F {i, j} (boundary C)"
  proof -
    have "integral (cubeImage C) (\<lambda>x. partial_vector_derivative (\<lambda>x. ?F x \<bullet> j) i x - partial_vector_derivative (\<lambda>x. ?F x \<bullet> i) j x) =
                     one_chain_line_integral ?F {i, j} (boundary C)"
      apply(rule Green.green_typeI_typeII_chain.GreenThm_typeI_typeII_divisible_region_finite_holes)
          apply(rule local.G1.green_typeI_typeII_chain_axioms)
      by (auto simp add:valid_cube_boundary vert_division hori_division s_is_oneCube)
    thus ?thesis using curl_f by auto
  qed
  thus ?thesis using i_is_x_axis j_is_y_axis
    apply(simp add: area_from_F one_chain_line_integral_def line_integral_def)
    apply(rule Finite_Cartesian_Product.sum_cong_aux)
    by (auto split: prod.splits intro: Henstock_Kurzweil_Integration.integral_cong)
qed
end

thm isop1.area_C isop2.area_C

locale isop = isop1 i j s two_chain_typeI two_chain_typeII + isop2 i j s two_chain_typeI two_chain_typeII for s i j two_chain_typeI two_chain_typeII
begin
lemma shows area_from_line_integral: "integral (cubeImage C) (\<lambda>x. 1) = (1/2) * (one_chain_line_integral (\<lambda>(x,y). (0,x)) {j} (boundary C) + one_chain_line_integral (\<lambda>(x,y). (-y,0)) {i} (boundary C))"
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

Suppose b > a, and s(b) = s(a) (i.e s does not have a well-defined inverse),
then \<integral>\<^sub>a\<^sup>b sqrt((x')\<^sup>2 + (y')\<^sup>2) \<ge>  \<integral>\<^sub>a\<^sup>b \<alpha> = (b-a)\<alpha> > 0 , giving a contradiction.
So if we have an \<alpha> > 0, st.  sqrt((x' t)\<^sup>2 + (y' t)\<^sup>2) > \<alpha> at all points t \<in> I,
this will guarantee that s is increasing and injective, which will guarantee a well-defined inverse.

A regularly parametrised curve (RPC) is a smooth curve who's derivative never vanishes. We need our curve to be piecewise regularly parametrised.
*)

term "list_all"

end