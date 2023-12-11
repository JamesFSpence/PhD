theory Intervals
  imports "$AFP/Green/Green"
begin

typedef interval = "{S :: real set. is_interval S}"
proof-
  show ?thesis by blast
qed
print_theorems

setup_lifting type_definition_interval

(*Subsets*)
lift_definition ivl_subseteq1 :: "interval \<Rightarrow> interval \<Rightarrow> bool"
  is "(\<lambda> I J. I \<subseteq> J)"
  done

lift_definition ivl_subseteq2 :: "interval \<Rightarrow> real set \<Rightarrow> bool"
  is "(\<lambda> I S. I \<subseteq> S)"
  done

lift_definition ivl_subseteq3 :: "real set \<Rightarrow> interval \<Rightarrow> bool"
  is "(\<lambda>S I. S \<subseteq> I)"
  done

lift_definition ivl_subset1 :: "interval \<Rightarrow> interval \<Rightarrow> bool"
  is "(\<lambda> I J. I \<subset> J)"
  done

lift_definition ivl_subset2 :: "interval \<Rightarrow> real set \<Rightarrow> bool"
  is "(\<lambda> I J. I \<subset> J)"
  done

lift_definition ivl_subset3 :: "real set \<Rightarrow> interval \<Rightarrow> bool"
  is "(\<lambda> I J. I \<subset> J)"
  done

(*Interval intersection/union*)
lift_definition ivl_inter :: "interval \<Rightarrow> interval \<Rightarrow> interval"
  is "(\<lambda> A B. A \<inter> B)"
  by (simp add: Topology_Euclidean_Space.is_interval_Int)

lift_definition ivl_Inter :: "interval set \<Rightarrow> interval"
  is "(\<lambda> Is. \<Inter> Is)"
proof -
  fix intervals :: "real set set"
  assume 0: "\<And>x. x\<in>intervals \<Longrightarrow> is_interval x"
  have 1: "\<forall>A. A \<in> intervals \<longrightarrow> x \<in> A \<Longrightarrow> B \<in> intervals \<Longrightarrow> x \<in> B" for B x by auto
  have 2: "is_interval I \<Longrightarrow> a \<in> I \<Longrightarrow> b \<in> I \<Longrightarrow> a \<le> c \<Longrightarrow> c \<le> b \<Longrightarrow> c \<in> I" for a::real and b::real and  c::real and I::"real set"
    using mem_is_interval_1_I by blast
  have 3: "\<forall>A. A \<in> intervals \<longrightarrow> a \<in> A \<Longrightarrow> \<forall>B. B \<in> intervals \<longrightarrow> b \<in> B \<Longrightarrow> a \<le> c \<Longrightarrow> c \<le> b \<Longrightarrow> D \<in> intervals \<Longrightarrow> c \<in> D" for a b c D
    apply(rule 2[of D a b c])
    by (auto simp add: 0)
  show "is_interval (\<Inter> intervals)"
    apply(subst Inter_eq)
    apply(subst is_interval_def)
    apply(subst Ball_def)+
    by (auto intro: 3)
qed

lift_definition ivl_union :: "interval \<Rightarrow> interval \<Rightarrow> real set"
  is "(\<lambda> A B. A\<union>B)"
  done

lift_definition ivl_Union :: "interval set \<Rightarrow> real set"
  is "(\<lambda> Is. \<Union>Is)"
  done

lift_definition ivl_in :: "real \<Rightarrow> interval \<Rightarrow> bool"
  is "(\<lambda> t I. t \<in> I)"
  done

lift_definition ivl_Max :: "interval \<Rightarrow> real"
  is "(\<lambda> I. Max I)"
  done

lift_definition ivl_Min :: "interval \<Rightarrow> real"
  is "(\<lambda> I. Min I)"
  done

lift_definition ivl_negligible :: "interval \<Rightarrow> bool"
  is "(\<lambda> I. negligible I)"
  done

lift_definition ivl_atLeastAtMost :: "real \<Rightarrow> real \<Rightarrow> interval"
  is "(\<lambda> a b. {a..b})"
  by (rule is_interval_cc)

lift_definition ivl_continuous_on :: "interval \<Rightarrow> (real \<Rightarrow> 'a::topological_space) \<Rightarrow> bool"
  is "(\<lambda> I f. continuous_on I f)"
  done

lift_definition ivl_integral :: "interval \<Rightarrow> (real \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'b"
  is "(\<lambda> I f. integral I f)"
done

fun ordered_subintervals_of :: "interval list \<Rightarrow> interval \<Rightarrow> bool" (infix "(ordered'_subintervals'_of)" 50) where
"[] ordered_subintervals_of I = True"|
"(x#xs) ordered_subintervals_of I = (ivl_subseteq1 x I \<and> xs ordered_subintervals_of (ivl_atLeastAtMost (ivl_Max x) (ivl_Max I)))"

definition ivls_to_real_set_set :: "interval set \<Rightarrow> real set set" where
"ivls_to_real_set_set S \<equiv> {y. \<exists>x. x\<in>S \<and> y = Rep_interval x}"

(*A Regularly Parametrised Curve (RPC) is smooth map \<gamma> : I \<rightarrow> \<real> such that (\<gamma>' t) \<noteq> (0,0) at any point t\<in>I where I is an interval
!WARNING! RPC means smooth, but below only calls for C1 so is_RPC_on is a bad name.
Here I have only required f to be C1 as I believe this is all I need at this point.*)
definition is_RPC_on :: "(real \<Rightarrow> (real \<times> real)) \<Rightarrow> interval \<Rightarrow> bool"  (infix "(is'_RPC'_on)" 50) where
"f is_RPC_on I \<equiv> (\<exists>f'. (ivl_continuous_on I f' \<and> (\<forall>t. ivl_in t I \<longrightarrow> (f has_vector_derivative (f' t)) (at t) \<and> f' t \<noteq> 0)))"

definition non_overlapping_ivls :: "interval set \<Rightarrow> bool" where
"non_overlapping_ivls S \<equiv> pairwise (\<lambda>x y. ivl_negligible (ivl_inter x y)) S"

definition finitely_covers :: "interval set \<Rightarrow> interval \<Rightarrow> bool"  (infix "finitely'_covers" 50) where
"S finitely_covers I \<equiv> (finite S \<and> ivl_subseteq2 I (ivl_Union S))"

definition valid_subivls_of :: "interval set \<Rightarrow> interval \<Rightarrow> bool" (infix "(valid'_subivls'_of)" 50) where
"S valid_subivls_of I \<equiv> (S finitely_covers I \<and> non_overlapping_ivls S)"

(*A curve is piecewise RPC if it can be broken down into finitely many RPCs minus a finite number of points
OR
No need for finite number of points?*)

definition is_pieceise_RPC_on :: "(real \<Rightarrow> (real \<times> real)) \<Rightarrow> interval set \<Rightarrow> interval \<Rightarrow> bool" (infix "(is'_piecewise'_RPC'_on)" 50) where
"(f is_piecewise_RPC_on S) I \<equiv> ((\<forall>x\<in>S. f is_RPC_on x) \<and> (S valid_subivls_of I))"

definition piecewise_RPC :: "(real \<Rightarrow> (real \<times> real)) \<Rightarrow> interval \<Rightarrow> bool" where
"piecewise_RPC f I \<equiv> (\<exists>S. (f is_piecewise_RPC_on S) I)"

(*For the isoperimetric theorem we need finite length, so our interval must be bounded: "bounded I"*)

definition speed :: "(real \<Rightarrow> (real \<times> real)) \<Rightarrow> (real \<Rightarrow> real)" where
"speed f = (\<lambda>t. norm (vector_derivative f (at t)))"

definition arclength_param_on :: "(real \<Rightarrow> (real \<times> real)) \<Rightarrow> real set \<Rightarrow> bool"
  where "arclength_param_on c I \<equiv> \<forall>t\<in>I. (speed c) t = 1"

definition arc_length_fun :: "(real \<Rightarrow> (real \<times> real)) \<Rightarrow> real \<Rightarrow> (real \<Rightarrow> real)" where
"arc_length_fun f start \<equiv> (\<lambda>t. integral {start..t} (speed f))"

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

\<rightarrow> For each x in S, we have a reparametrisation which is arclength
\<rightarrow> This results in a piecewise C1 arc length parametrisation of f
*)

lemma speed_ge_0 : fixes f :: "(real \<Rightarrow> real \<times> real)"
  shows "\<forall>t. speed f t \<ge> 0"
proof
  fix t
  show "speed f t \<ge> 0" using speed_def by auto
qed

lemma RPC_speed_gr_0 : fixes f :: "(real \<Rightarrow> real \<times> real)" and I :: "interval" and t :: real
  assumes "f is_RPC_on I" and "ivl_in t I"
  shows "speed f t > 0"
proof -
  show ?thesis using assms
    unfolding speed_def is_RPC_on_def ivl_in_def ivl_continuous_on_def
    apply(simp)
    apply(erule exE)
    apply(erule conjE)
    apply(drule HOL.spec)
    by (auto dest: Derivative.vector_derivative_at)
qed

lemma gr_less_ind:  fixes a::real and b::real
  shows "\<not> (indicat_real {a<..<b} has_integral 0) UNIV \<Longrightarrow> a < b"
  using negligible by force

lemma gr_le_ind:  fixes a::real and b::real
  shows "\<not> (indicat_real {a<..b} has_integral 0) UNIV \<Longrightarrow> a < b"
  using negligible by fastforce

lemma ge_less_ind:  fixes a::real and b::real
  shows "\<not> (indicat_real {a..<b} has_integral 0) UNIV \<Longrightarrow> a < b"
  using negligible by force

lemma ge_le_ind:  fixes a::real and b::real
  shows "\<not> (indicat_real {a..b} has_integral 0) UNIV \<Longrightarrow> a < b"
  using lmeasurable_iff_indicator_has_integral by fastforce

lemma add_interval_frac: fixes a::real and b::real
  assumes "a<b" and "0 < c" and "c < (b - a)"
  shows "a < a + c" "a + c < b"
proof-
  show "a < a + c" using assms by simp
  show "a + c < b" using assms by simp
qed

lemma closed_ivl_in_ge_le: "a<b \<Longrightarrow> \<exists>aa ba. aa < ba \<and> {aa..ba} \<subseteq> {a<..<b}" for a::real and b::real
  apply(rule exI[of _ "a + ((b-a)/4)"])
  apply(rule exI[of _ "a + ((b-a)/2)"])
  by (auto simp add: add_interval_frac atMostAtLeast_subset_convex[OF convex_real_interval(8)[of a b]])

lemma ge_le_in_ge:"I \<subseteq> {a<..<b} \<Longrightarrow> I \<subseteq> {a..}" for a::real and b::real by auto

lemma ge_le_in_le:"I \<subseteq> {a<..<b} \<Longrightarrow> I \<subseteq> {..b}" for a::real and b::real by auto

lemma ge_le_in_gt:"I \<subseteq> {a<..<b} \<Longrightarrow> I \<subseteq> {a<..}" for a::real and b::real by (simp add: subset_iff)

lemma ge_le_in_lt:"I \<subseteq> {a<..<b} \<Longrightarrow> I \<subseteq> {..<b}" for a::real and b::real by (simp add: subset_iff)

lemma ge_le_in_gt_le:"I \<subseteq> {a<..<b} \<Longrightarrow> I \<subseteq> {a<..b}" for a::real and b::real
  using interior_lessThanAtMost interior_subset by blast

lemma ge_le_in_ge_lt: "I \<subseteq> {a<..<b} \<Longrightarrow> I \<subseteq> {a..<b}" for a::real and b::real
  using interior_atLeastLessThan interior_subset by blast

lemma ge_le_in_ge_le: "I \<subseteq> {a<..<b} \<Longrightarrow> I \<subseteq> {a..b}" for a::real and b::real
  using interior_atLeastAtMost_real interior_subset by blast

lemma find_closed_subinterval: fixes I :: "real set"
  assumes "\<not> negligible I" "is_interval I"
  shows "\<exists>a b. a<b \<and> {a..b} \<subseteq> I"
proof -
  have 0: "indicat_real {} = (\<lambda>x. 0)" by auto
  have 1: "\<exists>(a::real) (b::real). (a < b)" using zero_less_one by blast
  have 2: "\<exists>(a::real) ba. a < ba \<and> {a..ba} \<subseteq> {..<b}" for b::real
    using ge_le_in_lt closed_ivl_in_ge_le lt_ex by meson
  have 3: "\<exists>a ba. a < ba \<and> (a \<le> ba \<longrightarrow> ba \<le> b)" for b::real
    using ge_le_in_ge closed_ivl_in_ge_le lt_ex[of b] by auto
  have 4: "\<exists>aa b. aa < b \<and> {aa..b} \<subseteq> {a<..}" for a::real
    using ge_le_in_gt closed_ivl_in_ge_le gt_ex by meson
  have 5: "\<exists>aa b. aa < b \<and> (aa \<le> b \<longrightarrow> a \<le> aa)" for a::real
    using ge_le_in_ge closed_ivl_in_ge_le gt_ex[of a] by auto
  have 6: "a<b \<Longrightarrow> \<exists>aa ba. aa < ba \<and> {aa..ba} \<subseteq> {a<..<b}" for a::real and b::real
    using closed_ivl_in_ge_le by auto
  have 7: "a<b \<Longrightarrow> \<exists>aa ba. aa < ba \<and> {aa..ba} \<subseteq> {a<..b}" for a::real and b::real
    using closed_ivl_in_ge_le ge_le_in_gt_le gt_ex by meson
  have 8: "a<b \<Longrightarrow> \<exists>aa ba. aa < ba \<and> {aa..ba} \<subseteq> {a..<b}" for a::real and b::real
    using closed_ivl_in_ge_le ge_le_in_ge_lt by meson
  have 9: "a<b \<Longrightarrow> \<exists>aa ba. aa < ba \<and> (aa \<le> ba \<longrightarrow> a \<le> aa \<and> ba \<le> b)" for a::real and b::real
    by blast
  show ?thesis using assms
    apply(simp add: Equivalence_Lebesgue_Henstock_Integration.negligible_UNIV)
    apply(drule Borel_Space.is_real_interval)
    thm disjI1
    by (auto simp add: 0 1 2 3 4 5 6 7 8 9 ge_le_ind ge_less_ind gr_le_ind gr_less_ind)
qed
(*Is there a way to avoid doing the same thing 4 times above? (lemmas 6, 7, 8, 9)*)

lemma bounds_in_interval: fixes a::real and b:: real
  assumes "{a..b} \<subseteq> I" and "is_interval I" and "a<b"
  shows "a\<in>I" "b\<in>I"
proof -
  show "a\<in>I" using assms by auto
  show "b\<in>I" using assms by auto
qed

lemma le_minus_less: "({..a} - {..<a}) = {a}" for a::real by auto

lemma ge_minus_grtr: "({a..} - {a<..}) = {a}" for a::real by auto

lemma closure_minus_gt_lt: "negligible (closure {a<..<b} - {a<..<b})" for a::real and b::real
proof cases
  assume 1: "a<b"
  hence "closure {a<..<b} = {a..b}" by auto
  hence "closure {a<..<b} - {a<..<b} = {a, b}" using 1 by auto
  thus ?thesis by auto
next
  assume 2: "\<not> a<b"
  hence "{a<..<b} = {}" by auto
  thus ?thesis by auto
qed

lemma closure_minus_gt_le: "negligible (closure {a<..b} - {a<..b})" for a::real and b::real
proof cases
  assume 1: "a<b"
  hence "closure {a<..b} = {a..b}" by auto
  hence "closure {a<..b} - {a<..b} = {a}" using 1 by auto
  thus ?thesis by auto
next
  assume 2: "\<not>a<b"
  thus ?thesis by auto
qed

lemma closure_minus_ge_lt: "negligible (closure {a..<b} - {a..<b})" for a::real and b::real
proof cases
  assume 1: "a<b"
  hence "closure {a..<b} = {a..b}" by auto
  hence "closure {a..<b} - {a..<b} = {b}" using 1 by auto
  thus ?thesis by auto
next
  assume 2: "\<not>a<b"
  thus ?thesis by auto
qed

lemma "(\<lambda>(x::real). (1::real)) integrable_on {a..b}"
  sledgehammer

lemma "\<nexists>b. {(a::real)..b} = {a..}"

lemma ivl_has_negligible_sym_diff: fixes I::"real set"
  assumes "is_interval I" 
  shows "negligible (sym_diff (I::real set) (closure I))"
  apply(simp add: negligible_setdiff[OF closure_subset])
  using is_real_interval[of I, OF assms]
  by (auto simp add: closure_minus_gt_lt closure_minus_gt_le closure_minus_ge_lt le_minus_less ge_minus_grtr)

lemma "\<not> bounded ({a..}::real set)" for a
proof (rule notI)
  assume "bounded {a..}"
  hence "\<forall>x\<in>{a..}. x \<le> Sup {a..}"
    by (rule bounded_has_Sup(1)[of "{a..}",OF _ not_sym[OF not_empty_eq_Ici_eq_empty]])
  hence "\<forall>x\<ge>a. x \<le> Sup {a..}" by (auto simp add: atLeast_iff[of _ a])
  hence ?thesis
    apply(auto simp add: le_sup_iff)
    sorry
    by (metis gt_ex le_sup_iff linorder_not_less order_less_imp_le)
  find_theorems "?a \<noteq> ?b \<Longrightarrow> ?b \<noteq> ?a"
  thm gt_ex[of a]
  thm le_sup_iff
  thm linorder_not_less order_less_imp_le
  by (metis atLeast_iff bounded_has_Sup(1) gt_ex le_sup_iff less_imp_le not_empty_eq_Ici_eq_empty not_less)

lemma fixes I::"real set"
  assumes "is_interval I" "bounded I"
  shows "\<exists>a b. I = {} \<or> I = {a<..<b} \<or> I = {a<..b} \<or> I = {a..<b} \<or> I = {a..b}"
proof-
  have "\<not> bounded {..<b}" for b::real
    sorry
  hence "\<not> bounded {..b}" for b::real
    sorry
  have "\<not> bounded {a<..}" for a::real
    sorry
  hence "\<not> bounded {a..}" for a::real
    sorry
  thus ?thesis using is_real_interval[of I, OF assms(1)] assms(2) Elementary_Normed_Spaces.not_bounded_UNIV
    apply(auto)
    
    

lemma fixes f :: "real \<Rightarrow> real" and I :: "real set"
  assumes "\<forall>t \<in> I. (f t > 0)" "\<not> negligible I" "is_interval I" "\<forall>x. x\<in> (closure I) \<longrightarrow> isCont f x" "bounded I"
  shows "integral I f > 0"
proof-
  have "\<exists>a b. a<b \<and> {a..b} \<subseteq> I"
    using assms by (simp add: find_closed_subinterval)
  then obtain a b where 0: "a<b \<and> {a..b} \<subseteq> I" by auto
  hence 1: "a \<le> x \<and> x \<le> b \<Longrightarrow> x \<in> I" for x by auto
  have cont_on_I: "\<forall>x. x\<in>I \<longrightarrow> isCont f x"
    using assms(4) closure_subset by auto
  hence "\<exists>L. (\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> L \<le> f x) \<and> (\<exists>x\<ge>a. x \<le> b \<and> f x = L)"
    using 0 1 by (auto simp add: isCont_eq_Lb)
  then obtain L where 2: "(\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> L \<le> f x) \<and> (\<exists>x\<ge>a. x \<le> b \<and> f x = L)" by auto
  hence "L > 0" using assms(1) 1 by auto
  have "(b-a)*L > 0"
    by (intro mult_pos_pos) (auto simp add: 0 \<open>L>0\<close>)
  have 3: "f integrable_on {a..b}"
    apply(rule integrable_continuous_interval)
    apply(rule continuous_at_imp_continuous_on)
    using 1 cont_on_I by auto
  have "f integrable_on (closure I)"
    find_theorems "_ integrable_on _" name:cont
    find_theorems "bounded" name: "interval"
    using is_real_interval[of I, OF assms(3)] assms(4)
    apply(auto)
    sorry
  hence "f integrable_on I"
    apply(subst integrable_spike_set_eq[of I "closure I"])
    apply(rule ivl_has_negligible_sym_diff)
    using assms(3) by auto
  hence f_has_int_I: "(f has_integral integral I f) I"
    by (simp add: has_integral_integral)
  have "integral {a..b} (\<lambda>x. L) \<le> integral {a..b} f"
    by (intro integral_le) (auto simp add: assms 2 3)
  hence 5: "integral {a..b} f \<ge> (b-a)*L" using 0 1 by auto
  hence ab_gr_0:"integral {a..b} f > 0" using \<open>(b-a)*L > 0\<close> by auto
  have 7: "f integrable_on (I-{a..b})"
    apply(rule integrable_setdiff)
      apply(rule f_has_int_I)
     apply(rule iffD1[OF has_integral_integral[of f "{a..b}"] 3])
    by (simp add: 0)
  hence "integral (I-{a..b}) f \<ge> 0"
    using assms(1) by (intro integral_nonneg) auto
  hence "0 < integral (I - {a..b}) f + integral {a..b} f"
    by (intro ab_gr_0 ordered_comm_monoid_add_class.add_nonneg_pos)
  hence "integral ({a..b} \<union> (I-{a..b})) f > 0"
    apply(subst integral_Un)
    by (auto simp add: 3 7 Int_commute)
  thus "integral I f > 0" using 0
    by (simp add: Un_absorb1)
qed


lemma fixes f :: "(real \<Rightarrow> real \<times> real)" and I :: "interval"
  assumes "f is_RPC_on I" and "d = (\<lambda>t. integral {interval_Min I..t} (speed f))"
  shows "strict_mono_on (Rep_interval I) d"
proof -
  have integ_on: "(speed f) integrable_on (Rep_interval I)"
    sorry
  fix t
  assume t_in_I: "interval_in t I"
  have "0 \<le> integral {interval_Min I..t} (speed f)" for t
  proof -
    show ?thesis
      apply(rule Henstock_Kurzweil_Integration.integral_nonneg)
       apply(rule Henstock_Kurzweil_Integration.integrable_on_subinterval)
      apply(rule integ_on)
      thm RPC_speed_gr_0
      thm t_in_I
     apply(auto simp add: speed_ge_0 integ_on t_in_I interval_Min_def) (*THIS IS MESSY AND NOT PRODUCTIVE*)
  have ?thesis using RPC_speed_gr_0 assms
    unfolding strict_mono_on_def interval_in_def
    apply(simp)
    apply(rule Henstock_Kurzweil_Integration.integral_nonneg)
    apply(auto)
    sorry
qed

term list_all

lemma fixes f :: "(real \<Rightarrow> real \<times> real)" and I :: "interval"
  assumes "f is_RPC_on I" and "s = arc_length_fun f (interval_Min I)" and "\<gamma> = inv s"
  shows "reparam_of f (f \<circ> \<gamma>) \<gamma> (Rep_interval I)"
proof -
    sorry
(*To prove this I need to show inv s is deifferentiable which requires the inverse function theorem*)

lemma fixes f :: "(real \<Rightarrow> real \<times> real)" and I :: "real set"
  assumes "is_interval I" and "f is_RPC I" and "inv_s = inv (arc_length_fun f (Min I))"
  shows "f is_RPC I \<Longrightarrow> (arclength_param_at (f \<circ> s) I)"

end