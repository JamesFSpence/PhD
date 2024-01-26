theory Intervals
  imports "HOL-Analysis.Analysis" "HOL-Probability.Probability_Mass_Function"
begin

typedef interval = "{S :: real set. is_interval S}"
proof-
  show ?thesis by blast
qed

term "s::real set"
term "Abs_interval s"
term "Abs_interval {a..b}"
print_theorems

setup_lifting type_definition_interval

print_theorems

(*Subsets*)
lift_definition ivl_subseteq :: "interval \<Rightarrow> interval \<Rightarrow> bool"
  is "(\<lambda> I J. I \<subseteq> J)"
  done

lift_definition ivl_subset :: "interval \<Rightarrow> interval \<Rightarrow> bool"
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
  have 2: "is_interval I \<Longrightarrow> a \<in> I \<Longrightarrow> b \<in> I \<Longrightarrow> a \<le> c \<Longrightarrow> c \<le> b \<Longrightarrow> c \<in> I" for a b c::real and I::"real set"
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

(*The input to instantiation 'semiring of sets' needs to be a class not a locale.
For locales, you can use interpretation.*)
instantiation interval :: (type) semiring_of_sets
begin

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
definition is_RPC_on :: "(real \<Rightarrow> (real \<times> real)) \<Rightarrow> real set \<Rightarrow> bool"  (infix "(is'_RPC'_on)" 50) where
"f is_RPC_on I \<equiv> (\<exists>f'. (continuous_on I f' \<and> (\<forall>t\<in>I. (f has_vector_derivative (f' t)) (at t) \<and> f' t \<noteq> 0)))"

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

find_theorems "interior {?a..?b}"
definition arclength_param_on :: "(real \<Rightarrow> (real \<times> real)) \<Rightarrow> real set \<Rightarrow> bool"
  where "arclength_param_on c I \<equiv> \<forall>t\<in>(interior I). (speed c) t = 1"

definition arc_length_fun :: "(real \<Rightarrow> (real \<times> real)) \<Rightarrow> real \<Rightarrow> (real \<Rightarrow> real)" where
"arc_length_fun f start \<equiv> (\<lambda>t. integral {start..t} (speed f))"

definition reparam_of :: "(real \<Rightarrow> (real \<times> real)) \<Rightarrow> (real \<Rightarrow> (real \<times> real)) \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> (real set) \<Rightarrow> bool"  where
"reparam_of c\<^sub>1 c\<^sub>2 \<gamma> I \<equiv> (is_interval I \<and> continuous_on I \<gamma> \<and> inj_on \<gamma> I \<and> (\<forall>t\<in>I. c\<^sub>1 t = (c\<^sub>2 \<circ> \<gamma>) t \<and> (\<exists>\<gamma>'. (\<gamma> has_vector_derivative (\<gamma>' t)) (at t))))"

(*What lemmas do I want to show?

\<rightarrow> For general f, speed f \<ge> 0 \<checkmark>

Assuming f is_RPC_on I, what lemmas do I want to show?

\<rightarrow> speed f \<noteq> 0 \<checkmark>
\<rightarrow> d = \<integral> speed f is increasing \<checkmark>
\<rightarrow> inv d is well-defined \<checkmark>
\<rightarrow> inv d is differentiable \<checkmark>
\<rightarrow> f \<circ> (inv d) is arc length parametrisation \<checkmark>
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

lemma RPC_speed_gr_0 : fixes f :: "(real \<Rightarrow> real \<times> real)" and I :: "real set" and t :: real
  assumes "f is_RPC_on I" and "t \<in> I"
  shows "speed f t > 0"
proof -
  show ?thesis using assms
    unfolding speed_def is_RPC_on_def
    apply(simp)
    apply(erule exE)
    apply(erule conjE)
    using vector_derivative_at by fastforce
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
    by (auto simp add: 0 1 2 3 4 5 6 7 8 9 ge_le_ind ge_less_ind gr_le_ind gr_less_ind)
qed
(*Is there a way to avoid doing the same thing 4 times above? (lemmas 6, 7, 8, 9)*)

lemma find_closed_subinterval_short: fixes I :: "real set"
  assumes "\<not> negligible I" "is_interval I"
  shows "\<exists>a b. a<b \<and> {a..b} \<subseteq> I"
proof -
  have "\<exists>a b. a<b \<and>(I = {} \<or> I = UNIV \<or>
          I = {..<b} \<or> I = {..b} \<or> I = {a<..} \<or> I = {a..} \<or> I = {a<..<b} \<or> I = {a<..b} \<or> I = {a..<b} \<or> I = {a..b})"
    using assms(2)
    by (metis assms(1) atLeastLessThan_empty_iff2 greaterThanAtMost_empty_iff greaterThanLessThan_empty_iff2 gt_ex is_real_interval linorder_not_less lt_ex negligible_atLeastAtMostI)
  then obtain a b where 0: "a<b \<and>(I = {} \<or> I = UNIV \<or>
          I = {..<b} \<or> I = {..b} \<or> I = {a<..} \<or> I = {a..} \<or> I = {a<..<b} \<or> I = {a<..b} \<or> I = {a..<b} \<or> I = {a..b})"
    by auto
  then obtain a' b' where 1: "a' < b'" "{a' .. b'} \<subseteq> {a<..<b}"
    using closed_ivl_in_ge_le[of a b] by auto
  hence "b'\<le>b"
    by (meson Icc_subset_Iic_iff dual_order.strict_iff_not ge_le_in_le)
  have "a\<le>a'" using 1
    by (meson Icc_subset_Ici_iff dual_order.strict_iff_not ge_le_in_ge)
  have cases: "I = {} \<or> I = UNIV \<or>
          I = {..<b} \<or> I = {..b} \<or> I = {a<..} \<or> I = {a..} \<or> I = {a<..<b} \<or> I = {a<..b} \<or> I = {a..<b} \<or> I = {a..b}"
    using 0 by auto
  from cases show ?thesis 
    apply -
    apply(rule exI[where x = a'])
    apply(rule exI[where x = b'])
    apply(elim disjE)
    subgoal using assms(1) by auto
    using `a' < b'`
    by (auto intro!: subset_trans[OF \<open>{a' .. b'} \<subseteq> {a<..<b}\<close>] \<open>b' \<le> b\<close> \<open>a \<le> a'\<close>)
qed

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

lemma ivl_has_negligible_sym_diff: fixes I::"real set"
  assumes "is_interval I" 
  shows "negligible (sym_diff (I::real set) (closure I))"
  apply(simp add: negligible_setdiff[OF closure_subset])
  using is_real_interval[of I, OF assms]
  by (auto simp add: closure_minus_gt_lt closure_minus_gt_le closure_minus_ge_lt le_minus_less ge_minus_grtr)

lemma ge_not_bounded: "\<not> bounded {a..}" for a::real
proof -
  have "\<nexists>M. \<forall>x\<ge>a. x\<le>M"
  proof (rule notI)
    assume "\<exists>M. \<forall>x\<ge>a. x\<le>M"
    then obtain M where 2: "\<forall>x\<ge>a. x\<le>M" by auto
    moreover have "sup (a+1) (M+1) \<ge> a" by (simp add: sup.coboundedI1)
    ultimately show False by auto
  qed
  thus "\<not> bounded {a..}"
    using bounded_has_Sup(1) by auto
qed

lemma gt_not_bounded: "\<not> bounded {a<..}" for a::real
proof-
  have "\<not> bounded {(a+1)..}" using ge_not_bounded by auto
  moreover have "{(a+1)..} \<subseteq> {a<..}" by auto
  ultimately show ?thesis using bounded_subset by blast
qed

lemma le_not_bounded: "\<not> bounded {..a}" for a::real
proof -
  have "\<nexists>M. \<forall>x\<le>a. x\<ge>M"
  proof (rule notI)
    assume "\<exists>M. \<forall>x\<le>a. x\<ge>M"
    then obtain M where "\<forall>x\<le>a. x\<ge>M" by auto
    moreover have "inf (a-1) (M-1) \<le> a" by (simp add: le_infI1)
    ultimately show False by auto
  qed
  thus ?thesis using bounded_has_Inf(1) by auto
qed

lemma lt_not_bounded: "\<not> bounded {..<a}" for a::real
proof -
have "\<not> bounded {..(a-1)}" using le_not_bounded by auto
  moreover have "{..(a-1)} \<subseteq> {..<a}" by auto
  ultimately show ?thesis using bounded_subset by blast
qed

lemma is_real_bounded_interval: fixes I::"real set"
  assumes "is_interval I" "bounded I"
  shows "\<exists>a b. I = {} \<or> I = {a<..<b} \<or> I = {a<..b} \<or> I = {a..<b} \<or> I = {a..b}"
proof-
  show ?thesis using is_real_interval[of I, OF assms(1)] assms(2) Elementary_Normed_Spaces.not_bounded_UNIV
    by (auto simp add: ge_not_bounded gt_not_bounded le_not_bounded lt_not_bounded)
qed

lemma real_singelton_is_ivl: "{a} = {a..a}" for a::real by simp

lemma closure_of_bdd_ivl: fixes I::"real set"
  assumes "is_interval I" "bounded I"
  shows "\<exists>a b. closure I = {a..b}"
proof -
  show ?thesis using connected_imp_connected_closure[of I,OF iffD1[OF is_interval_connected_1[of I] assms(1)]] iffD2[OF compact_closure[of I] assms(2)] connected_compact_interval_1[of "closure I"]
    by (simp)
qed

lemma integral_non_zero_f_gr_0: fixes f :: "real \<Rightarrow> real" and I :: "real set"
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
  then obtain L where L_def: "(\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> L \<le> f x) \<and> (\<exists>x\<ge>a. x \<le> b \<and> f x = L)" by auto
  hence "L > 0" using assms(1) 1 by auto
  hence "(b-a)*L > 0"
    by (intro mult_pos_pos) (auto simp add: 0)
  have 2: "f integrable_on {a..b}"
    apply(rule integrable_continuous_interval)
    apply(rule continuous_at_imp_continuous_on)
    using 1 cont_on_I by auto
  have "\<exists>x y. closure I = {x..y}" using assms(3,5) closure_of_bdd_ivl[of I] by simp
  then obtain x y where clos_I:"closure I = {x..y}" by auto
  have "f integrable_on (closure I)"
    apply(subst clos_I)
    apply(rule Henstock_Kurzweil_Integration.integrable_continuous_interval)
    using assms(4) clos_I continuous_at_imp_continuous_on[of "{x..y}" f] by auto
  hence "f integrable_on I"
    apply(subst integrable_spike_set_eq[of I "closure I"])
    apply(rule ivl_has_negligible_sym_diff)
    using assms(3) by auto
  hence f_has_int_I: "(f has_integral integral I f) I"
    by (simp add: has_integral_integral)
  have "integral {a..b} (\<lambda>x. L) \<le> integral {a..b} f"
    apply(rule integral_le)
    by (auto simp add: 2 L_def)
  hence "integral {a..b} f \<ge> (b-a)*L" using 0 1 by auto
  hence ab_gr_0:"integral {a..b} f > 0" using \<open>(b-a)*L > 0\<close> by auto
  have 3: "f integrable_on (I-{a..b})"
    apply(rule integrable_setdiff)
      apply(rule f_has_int_I)
     apply(rule iffD1[OF has_integral_integral[of f "{a..b}"]])
    by (auto simp add: 0 2)
  hence "integral (I-{a..b}) f \<ge> 0"
    using assms(1) by (intro integral_nonneg) auto
  hence "0 < integral (I - {a..b}) f + integral {a..b} f"
    by (intro ab_gr_0 ordered_comm_monoid_add_class.add_nonneg_pos)
  hence "integral ({a..b} \<union> (I-{a..b})) f > 0"
    apply(subst integral_Un)
    by (auto simp add: Int_commute 2 3)
  thus "integral I f > 0" using 0
    by (simp add: Un_absorb1)
qed

lemma fixes f :: "(real \<Rightarrow> real \<times> real)" and a :: real and b::real
  assumes "f is_RPC_on (cbox a b)" and "d = (\<lambda>t. integral (cbox a t) (speed f))"
(*Not sure if I have to assume continuity of speed f. continuity holds if f is continuous and has continuous derivative on the closure of I. So maybe require that I be closed...*)
  shows "strict_mono_on {a..b} d"
proof -
  have 0:"t \<in> {a<..b} \<Longrightarrow> \<forall>t\<in>{a..t}. 0 < speed f t" for t
    sorry
  have 1: "t\<in>{a<..b} \<Longrightarrow> \<not>negligible{a..t}" for t by (simp add: negligible_iff_measure)
  hence 2: "continuous_on (cbox a b) (speed f)"
    sorry
  find_theorems "isCont" "continuous_on"
  have "t\<in>{a<..b} \<Longrightarrow> integral ({a..t}) (speed f) > 0" for t
    apply(rule integral_non_zero_f_gr_0)
        apply(auto simp add: 0 1 2 Elementary_Topology.continuous_on_interior)
    sorry
  thm RPC_speed_gr_0[OF assms(1)]
  show ?thesis using RPC_speed_gr_0 assms
    unfolding strict_mono_on_def
    apply(simp)
    sorry
qed

term list_all

lemma fixes f :: "(real \<Rightarrow> real \<times> real)" and I :: "interval"
  assumes "f is_RPC_on I" and "s = arc_length_fun f (interval_Min I)" and "\<gamma> = inv s"
  shows "reparam_of f (f \<circ> \<gamma>) \<gamma> (Rep_interval I)"
    sorry
(*To prove this I need to show inv s is differentiable which requires the inverse function theorem*)

lemma fixes f :: "(real \<Rightarrow> real \<times> real)" and I :: "real set"
  assumes "is_interval I" and "f is_RPC I" and "inv_s = inv (arc_length_fun f (Min I))"
  shows "f is_RPC I \<Longrightarrow> (arclength_param_at (f \<circ> s) I)"

lemma minus_interval_covering:
  fixes A B ::"real set"
  assumes "is_interval A" "(\<exists>C\<subseteq>{S. is_interval S}. finite C \<and> disjoint C \<and> UNIV - B = \<Union> C)"
  shows "\<exists>D\<subseteq>{S. is_interval S}. finite D \<and> disjoint D \<and> A - B = \<Union> D"
proof -
  obtain C where C_def: "C\<subseteq>{S. is_interval S} \<and> finite C \<and> disjoint C \<and> UNIV - B = \<Union> C" using assms by auto
  let ?D = "(\<lambda>x. A \<inter> x) ` C"
  have "finite ?D" using C_def by auto
  moreover have "disjoint ?D" using C_def
    by (simp add: disjoint_image_subset)
  moreover have "A - B = \<Union> ?D" using C_def by auto
  moreover have "is_interval A \<Longrightarrow> ?D \<subseteq> {S. is_interval S}" using C_def
    using is_interval_Int by blast
  ultimately show ?thesis using assms by auto
qed

interpretation intervals: semiring_of_sets "UNIV" "{S :: real set. is_interval S}"
proof
  show "{S. is_interval S} \<subseteq> Pow UNIV" by auto
  show "{} \<in> {S. is_interval S}" by auto
  show "\<And>a b. a \<in> {S. is_interval S} \<Longrightarrow> b \<in> {S. is_interval S} \<Longrightarrow> a \<inter> b \<in> {S. is_interval S}" 
    by (simp add: is_interval_Int)
  have "B = {} \<or> B = UNIV \<or> B = {..<a} \<or> B = {..a} \<or> B = {a<..} \<or> B = {a..} \<Longrightarrow> is_interval (UNIV - B) " for a ::real and B
    apply(subst sym[OF Compl_eq_Diff_UNIV])
    by(auto)
  hence 0:"B = {} \<or> B = UNIV \<or> B = {..<a} \<or> B = {..a} \<or> B = {a<..} \<or> B = {a..} \<Longrightarrow> \<exists>C\<subseteq>{S. is_interval S}. finite C \<and> disjoint C \<and> UNIV - B = \<Union> C" for a::real and B
    apply -
    apply(rule exI[of _ "{UNIV - B}"])
    by(simp)
  hence 1: "is_interval A \<Longrightarrow> B = {} \<or> B = UNIV \<or> B = {..<a} \<or> B = {..a} \<or> B = {a<..} \<or> B = {a..} \<Longrightarrow> \<exists>C\<subseteq>{S. is_interval S}. finite C \<and> disjoint C \<and> A - B = \<Union> C" for a::real and A B
    using minus_interval_covering by auto
  have "B = {a<..<b} \<or> B = {a<..b} \<or> B = {a..<b} \<or> B = {a..b} \<Longrightarrow>  \<exists>C\<subseteq>{S. is_interval S}. finite C \<and> disjoint C \<and> UNIV - B = \<Union> C" for a b :: real and B
  proof cases
    assume "a\<ge>b"
    hence B_bounded_cases: "B = {a<..<b} \<or> B = {a<..b} \<or> B = {a..<b} \<or> B = {a..b} \<Longrightarrow> B = {} \<or> B = {a}" by auto
    have "disjoint {{..<a}, {a<..}}"
      by(auto simp add: Int_commute disjoint_def)
    hence "B = {a} \<Longrightarrow> \<exists>C\<subseteq>{S. is_interval S}. finite C \<and> disjoint C \<and> UNIV - B = \<Union> C"
      apply -
      apply(rule exI[of _ "{{..<a},{a<..}}"])
      by(auto)
    thus "B = {a<..<b} \<or> B = {a<..b} \<or> B = {a..<b} \<or> B = {a..b} \<Longrightarrow>  \<exists>C\<subseteq>{S. is_interval S}. finite C \<and> disjoint C \<and> UNIV - B = \<Union> C"
      using 0 B_bounded_cases by presburger
  next
    assume "\<not>a\<ge>b"
    hence "a<b" by auto
    have a1: "B = {a<..<b} \<Longrightarrow> UNIV - B = \<Union> {{..a},{b..}}" by auto
    have a2: "B = {a<..b} \<Longrightarrow> UNIV - B = \<Union> {{..a},{b<..}}" by auto
    have a3: "B = {a..<b} \<Longrightarrow> UNIV - B = \<Union> {{..<a},{b..}}" by auto
    have a4: "B = {a..b} \<Longrightarrow> UNIV - B = \<Union> {{..<a},{b<..}}" by auto
    have "disjoint {{..a},{b..}}" "disjoint {{..<a},{b..}}" "disjoint {{..a},{b<..}}" "disjoint {{..<a},{b<..}}" using \<open>a<b\<close>
      by (auto simp add: Int_commute disjoint_def)
    thus "B = {a<..<b} \<or> B = {a<..b} \<or> B = {a..<b} \<or> B = {a..b} \<Longrightarrow>  \<exists>C\<subseteq>{S. is_interval S}. finite C \<and> disjoint C \<and> UNIV - B = \<Union> C"
      apply -
      apply(erule disjE)
       apply(drule a1)
      apply(rule exI[of _ "{{..a},{b..}}"])
       apply(simp)
      apply(erule disjE)
       apply(drule a2)
      apply(rule exI[of _ "{{..a},{b<..}}"])
       apply(simp)
       apply(erule disjE)
       apply(drule a3)
      apply(rule exI[of _ "{{..<a},{b..}}"])
       apply(simp)
       apply(drule a4)
      apply(rule exI[of _ "{{..<a},{b<..}}"])
      apply(simp)
      done
        (*WHICH IS PREFERRED - SIMPLE BUT LONG APPLY SCRIPT, OR LONG METIS CALL?*)
      (*by (metis a1 a2 a3 a4 empty_subsetI finite.emptyI finite.insertI insert_subsetI is_interval_ci is_interval_ic is_interval_io is_interval_oi mem_Collect_eq)*)
  qed
  hence 2: "is_interval A \<Longrightarrow> B = {a<..<b} \<or> B = {a<..b} \<or> B = {a..<b} \<or> B = {a..b} \<Longrightarrow>  \<exists>C\<subseteq>{S. is_interval S}. finite C \<and> disjoint C \<and> A - B = \<Union> C" for a b ::real and A B
    using minus_interval_covering by auto
  have real_interval_disj: "is_interval B \<Longrightarrow> \<exists>a b. (B = {} \<or> B = UNIV \<or> B = {..<a} \<or> B = {..a} \<or> B = {a<..} \<or> B = {a..}) \<or> (B = {a<..<b} \<or> B = {a<..b} \<or> B = {a..<b} \<or> B = {a..b})" for B ::"real set"
    using is_real_interval by auto
  thm disjI1
  find_theorems "(?A \<Longrightarrow> ?C)" "?A\<or>?B \<Longrightarrow> ?C"
  thm 1 2 disjE
  show "a \<in> {S. is_interval S} \<Longrightarrow> b \<in> {S. is_interval S} \<Longrightarrow> \<exists>C\<subseteq>{S. is_interval S}. finite C \<and> disjoint C \<and> a - b = \<Union> C" for a b :: "real set"
    apply(rule disjE)
    apply(simp)
    apply(drule real_interval_disj[of b])
    apply(erule exE)+
    apply(erule disjE)
    by(auto simp add: 1 2)
qed


find_theorems name: ring

print_theorems

term extend_measure
term interval_measure
term PiM
term PiE
term Pi
term measure_of
term distr
term lborel
term borel
term prod_emb
term sigma_algebra
term algebra
term almost_everywhere
term ae_filter
term principal
term Abs_filter
term uniform_measure
term density
term " \<integral>\<^sup>+ x. f x * indicator A x \<partial>M"



end