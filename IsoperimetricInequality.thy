theory IsoperimetricInequality
  imports "$AFP/Green/Green"
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

typedef interval = "{S :: real set. is_interval S}"
proof-
  show ?thesis by blast
qed

setup_lifting type_definition_interval

find_theorems "Rep_interval"

(*Subinterval*)
lift_definition subinterval_eq :: "interval \<Rightarrow> interval \<Rightarrow> bool"
  is "(\<lambda> A B. A \<subseteq> B)"
  done

(*Interval intersection*)
lift_definition interval_inter :: "interval \<Rightarrow> interval \<Rightarrow> interval"
  is "(\<lambda> A B. A \<inter> B)"
  by (simp add: Topology_Euclidean_Space.is_interval_Int)

lift_definition interval_in :: "real \<Rightarrow> interval \<Rightarrow> bool"
  is "(\<lambda> t I. t \<in> I)"
  done
(*
notation
  interval_in  ("\<in>" 50)
*)
lift_definition interval_Max :: "interval \<Rightarrow> real"
  is "(\<lambda> I. Max I)"
  done

lift_definition interval_Min :: "interval \<Rightarrow> real"
  is "(\<lambda> I. Min I)"
  done

fun ordered_subintervals_of :: "interval list \<Rightarrow> interval \<Rightarrow> bool" (infix "(ordered'_subintervals'_of)" 50) where
"[] ordered_subintervals_of I = True"|
"(x#xs) ordered_subintervals_of I = (subinterval_eq x I \<and> xs ordered_subintervals_of (Abs_interval {(interval_Max x)..(interval_Max I)}))"


(*
(*Function can be split into finitely many C1 pieces that can be connected.
NOTE: Doesn't check that path starts and ends at the same point*)
fun C1_over_intervals :: "(real \<Rightarrow> (real \<times> real)) \<Rightarrow> interval list \<Rightarrow> bool" (infix "(C1'_over'_intervals)" 50) where
"f C1_over_intervals [] = True"|
"f C1_over_intervals [x] = (f C1_differentiable_on (Rep_interval x))"|
"(f C1_over_intervals (x#y#ys)) = ((f C1_differentiable_on (Rep_interval x)) \<and> (f(Max x) = f(Min y)) \<and> (f C1_over_intervals (y#ys)))"
(*Line above is messy because I couldn't figure out how to access the value of y neatly without writing the list as "Cons x (Cons y ys)"*)

definition C1_over_subintervals :: "(real \<Rightarrow> (real \<times> real)) \<Rightarrow> interval list \<Rightarrow> interval \<Rightarrow> bool" (infix "(C1'_over'_subintervals)" 50) where
"(f C1_over_subintervals S) I \<equiv> (f C1_over_intervals S \<and> S ordered_subintervals_of I)"

fun inj_over_intervals :: "(real \<Rightarrow> (real\<times>real)) \<Rightarrow> interval list \<Rightarrow>bool" (infix "(inj'_over'_intervals)" 50) where
"f inj_over_intervals [] = True"|
"f inj_over_intervals (x#xs) = (inj_on f (Rep_interval x) \<and> f inj_over_intervals xs)"

definition inj_over_subintervals :: "(real \<Rightarrow> (real \<times> real)) \<Rightarrow> interval list \<Rightarrow> interval \<Rightarrow> bool" (infix "(inj'_over'_subintervals)" 50) where
"(f inj_over_subintervals S) I = (f inj_over_intervals S \<and> S ordered_subintervals_of I)"

definition C1_inj_over_subintervals :: "(real \<Rightarrow> (real \<times> real)) \<Rightarrow> interval list \<Rightarrow> interval \<Rightarrow> bool" (infix "(C1'_inj'_over'_subintervals)" 50) where
"(f C1_inj_over_subintervals S) I = (f inj_over_intervals S \<and> f C1_over_intervals S \<and> S ordered_subintervals_of I)"
*)

thm has_vector_derivative_def
thm is_filter_def

value "Sup {f x}"
find_theorems "sup" name: "fun"
(*
(*Checks that a given list of real set are ordered subintervals of an interval I*)
fun ordered_subintervals_of :: "real set list \<Rightarrow> real set \<Rightarrow> bool" (infix "(ordered'_subintervals'_of)" 50) where
"[] ordered_subintervals_of I = is_interval I"|
"(x#xs) ordered_subintervals_of I = (is_interval I \<and> is_interval x \<and> x \<subseteq> I \<and> xs ordered_subintervals_of ({(Max  x)..(Max  I)}))"
*)
(*Checks if a function can be split into finitely many C1 pieces that can be connected by their endpoints.
NOTE: Doesn't check that path starts and ends at the same point*)
fun C1_over_list :: "(real \<Rightarrow> (real \<times> real)) \<Rightarrow> real set list \<Rightarrow> bool" (infix "(C1'_over'_list)" 50) where
"f C1_over_list [] = True"|
"f C1_over_list [x] = (f C1_differentiable_on x)"|
"(f C1_over_list (x#y#ys)) = (f C1_differentiable_on x \<and> (f(Max x) = f(Min y)) \<and> (f C1_over_list (y#ys)))"

value "{1::nat, 2, 3} - {1,3}"

definition closed_C1_over_list :: "(real \<Rightarrow> (real \<times> real)) \<Rightarrow> real set list \<Rightarrow> bool" (infix "(closed'_C1'_over'_list)" 50) where
"f closed_C1_over_list S \<equiv>  (f C1_over_list S \<and> (case S of [] \<Rightarrow> True | (x#xs) \<Rightarrow> f (Min x) = f (Max (last S))))"

fun inj_over_list :: "(real \<Rightarrow> (real\<times>real)) \<Rightarrow> real set list \<Rightarrow>bool" (infix "(inj'_over'_list)" 50) where
"f inj_over_list [] = True"|
"f inj_over_list (x#xs) = ((inj_on f x \<or> (inj_on f (x - {Max x}) \<and> f (Min x) = f (Max x))) \<and> f inj_over_list xs)"

definition closed_C1_inj_over_subintervals :: "(real \<Rightarrow> (real \<times> real)) \<Rightarrow> real set list \<Rightarrow> real set \<Rightarrow> bool" (infix "(closed'_C1'_inj'_over'_subintervals)" 50) where
"(f closed_C1_inj_over_subintervals S) I = (f inj_over_list S \<and> f closed_C1_over_list S \<and> S ordered_subintervals_of I)"

value "{1} \<inter> {1::rat}"

value "inv_into _"
value "reparam _"
find_theorems "inv _" "inj_on _ ?x"

(*Let p be a path, so p is a map from an interval I to the plane, p :  I \<rightarrow> \<real>\<^sup>2, and suppose it is injective on I (ignoring endpoints).
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

A regularly parametrised curve (RPC) is a curve who's derivative never vanishes. We need our curve to be piecewise regularly parametrised.
*)

(*We need lemma's relating the arc length parametrisation with a general parametrisation since a
oneCube is only define on the range {0..1}\<times>{0..1} so needn't be an arc length parametrisation*)

thm C1_differentiable_on_def
thm vector_derivative_def


(*A Regularly Parametrised Curve (RPC) is smooth map \<gamma> : I \<rightarrow> \<real> such that (\<gamma>' t) \<noteq> (0,0) at any point t\<in>I where I is an interval
Here I have only required f to be C1 as I believe this is all I need at this point.*)
definition is_RPC_on :: "(real \<Rightarrow> (real \<times> real)) \<Rightarrow> real set \<Rightarrow> bool"  (infix "(is'_RPC'_on)" 50) where
"f is_RPC_on I \<equiv> (is_interval I \<and> (\<exists>f'. (continuous_on I f' \<and> (\<forall>t\<in>I. (f has_vector_derivative (f' t)) (at t) \<and> f' t \<noteq> 0))))"

definition non_overlapping_intervals :: "(real set set) \<Rightarrow> bool" where
"non_overlapping_intervals S \<equiv> (\<forall>x\<in>S. is_interval x \<and> (\<forall>y\<in>S. x \<noteq> y \<longrightarrow> card (x \<inter> y) \<in> {0,1}))"
(*USE PAIRWISE NEGLIGIBLE*)
definition finitely_covers :: "(real set set) \<Rightarrow> real set \<Rightarrow> bool"  (infix "finitely'_covers" 50) where
"S finitely_covers I \<equiv> (\<exists>X. finite X \<and> I = \<Union>S \<union> X)"

definition valid_subintervals_of :: "real set set \<Rightarrow> real set \<Rightarrow> bool" (infix "(valid'_subintervals'_of)" 50) where
"S valid_subintervals_of I \<equiv> (S finitely_covers I \<and> non_overlapping_intervals S)"

(*A curve is piecewise RPC if it can be broken down into finitely many RPCs minus a finite number of points
OR
No need for finite number of points?*)

definition is_pieceise_RPC_on :: "(real \<Rightarrow> (real \<times> real)) \<Rightarrow> real set set \<Rightarrow> real set \<Rightarrow> bool" (infix "(is'_piecewise'_RPC'_on)" 50) where
"(f is_piecewise_RPC_on S) I \<equiv> ((\<forall>x\<in>S. f is_RPC_on x) \<and> (S valid_subintervals_of I))"

definition piecewise_RPC :: "(real \<Rightarrow> (real \<times> real)) \<Rightarrow> real set \<Rightarrow> bool" where
"piecewise_RPC f I \<equiv> (\<exists>S. (f is_piecewise_RPC_on S) I)"

(*For the isoperimetric theorem we need finite length, so our interval must be bounded: "bounded I"*)

definition speed :: "(real \<Rightarrow> (real \<times> real)) \<Rightarrow> (real \<Rightarrow> real)" where
"speed f = (\<lambda>t. norm (vector_derivative f (at t)))"

definition arclength_param_on :: "(real \<Rightarrow> (real \<times> real)) \<Rightarrow> real set \<Rightarrow> bool"
  where "arclength_param_on c I \<equiv> \<forall>t\<in>I. (speed c) t = 1"

definition arc_length_fun :: "(real \<Rightarrow> (real \<times> real)) \<Rightarrow> real \<Rightarrow> (real \<Rightarrow> real)" where
"arc_length_fun f start \<equiv> (\<lambda>t. integral {start..t} (speed f))"

find_theorems "inv _" name: "function"

thm onorm_componentwise_le
thm Derivative.inverse_function_theorem
find_theorems name: "inverse_function"
thm Deriv.DERIV_inverse_function
thm bounded_linear_def
thm inv_def
thm onorm_def
find_theorems "(THE x. _)"
thm bounded_linear_def
thm linear_def
find_theorems "linear ?f \<Longrightarrow> _"
find_theorems name: partially
(*Need to apply the inverse function theorem to ensure the arc length parametrisation exists*)
(*Can't get infix to work*)

definition reparam_of :: "(real \<Rightarrow> (real \<times> real)) \<Rightarrow> (real \<Rightarrow> (real \<times> real)) \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> (real set) \<Rightarrow> bool"  where
"reparam_of c\<^sub>1 c\<^sub>2 \<gamma> I \<equiv> (is_interval I \<and> continuous_on I \<gamma> \<and> (\<forall>t\<in>I. c\<^sub>1 t = (c\<^sub>2 \<circ> \<gamma>) t \<and> (\<exists>\<gamma>'. (\<gamma> has_vector_derivative (\<gamma>' t)) (at t))))"

(*What lemmas do I want to show?

\<rightarrow> For general f, speed f \<ge> 0 \<checkmark>

Assuming f is_RPC_on I, what lemmas do I want to show?

\<rightarrow> speed f \<noteq> 0 \<checkmark>
\<rightarrow> d = \<integral> speed f is injective and increasing
\<rightarrow> inv d is well-defined
\<rightarrow> inv d is continuous
\<rightarrow> f \<circ> (inv d) is arc length parametrisation
\<rightarrow> This can be transformed into constant speed function on {0..1}?

Assuming f is_piecewise_RPC_on S I, what lemmas do I want to show?

\<rightarrow> For each x in S, we have a reparametrisation which is arclenght
\<rightarrow> This results in a piecewise C1 arc length parametrisation of f
*)



lemma speed_ge_0 : fixes f :: "(real \<Rightarrow> real \<times> real)"
  shows "\<forall>t. speed f t \<ge> 0"
proof
  fix t
  show "speed f t \<ge> 0" using speed_def by auto
qed

lemma RPC_speed_gr_0 : fixes f :: "(real \<Rightarrow> real \<times> real)" and I :: "real set" and t :: real
  assumes "f is_RPC_on I" and "t \<in> I"
  shows "speed f t > 0"
proof -
  show ?thesis using assms
    unfolding speed_def is_RPC_on_def
    apply(simp)
    apply(erule conjE)
    apply(erule exE)
    apply(erule conjE)
    apply(drule Set.bspec)
    by (auto dest: Set.bspec Derivative.vector_derivative_at)
qed

find_theorems "mono _" name: integral

lemma fixes f :: "(real \<Rightarrow> real \<times> real)" and I :: "real set"
  assumes "f is_RPC_on I" and "d = (\<lambda>t. integral {Min I..t} (\<lambda>x. speed f x))"
  shows "strict_mono_on I d"
proof -

  
lemma fixes f :: "(real \<Rightarrow> real \<times> real)" and I :: "real set"
  assumes "is_interval I" and "f is_RPC_on I" and "s = arc_length_fun f (Min I)" and "\<gamma> = inv s"
  shows "reparam_of f (f \<circ> \<gamma>) \<gamma> I"
proof -
(*To prove this I need to show inv s is deifferentiable which requires the inverse function theorem*)

lemma fixes f :: "(real \<Rightarrow> real \<times> real)" and I :: "real set"
  assumes "is_interval I" and "f is_RPC I" and "inv_s = inv (arc_length_fun f (Min I))"
  shows "f is_RPC I \<Longrightarrow> (arclength_param_at (f \<circ> s) I)"



(*Is there a way to get around the wellsortedness error?*)

value [simp] "(norm 1::real)" (*Why does this return norm 1 and not 1?*)
value [simp] "norm (1::real, 2::real)"
thm Product_Vector.norm_prod_inst.norm_prod
value "bounded ({1..2::real})"
find_theorems name: smooth
find_theorems name: "vanish"

end