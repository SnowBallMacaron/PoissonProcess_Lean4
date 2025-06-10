import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Poisson
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure


open MeasureTheory Set ProbabilityTheory Asymptotics Filter NNReal ENNReal Topology


section PoissonProcess


-- Variable definitions for a counting process on (Ω, μ)
variable {Ω: Type*} [MeasurableSpace Ω] {μ : ProbabilityMeasure Ω}
variable (r : ℝ≥0)
variable (u : ℝ≥0 → Ω → ℕ)


-- 0. basic properties of counting process
@[class] structure CountingProcess
(u : ℝ≥0 → Ω → ℕ) : Prop where
  measurable_value : ∀ t : ℝ≥0, Measurable (u t)
  monotone : ∀ (ω : Ω) (s t : ℝ≥0), s < t → u s ω ≤ u t ω

-- Independent increments property
structure IndependentIncrements (μ : ProbabilityMeasure Ω)
(u : ℝ≥0 → Ω → ℕ) : Prop where
 indepInc : ∀ (n : ℕ) (t : Fin (n+1) → ℝ≥0),
   (∀ i : Fin n, t i < t i.succ) →
   iIndepFun (fun i => fun ω => u (t i.succ) ω - u (t i) ω) μ

-- Stationary increments property
structure StationaryIncrements (μ : ProbabilityMeasure Ω)
(u : ℝ≥0 → Ω → ℕ) : Prop where
  stationInc : ∀ t₁ t₂ s : ℝ≥0, t₁ ≤ t₂ →
    ∀ n : ℕ, μ {ω | u t₂ ω - u t₁ ω = n} = μ {ω | u (t₂ + s) ω - u (t₁ + s) ω = n}


-- PoissonProcessPmf: PMF-based definition of a Poisson process
@[class] structure PoissonProcessPmf (μ : ProbabilityMeasure Ω) (u : ℝ≥0 → Ω → ℕ)
[CountingProcess u]: Prop extends IndependentIncrements μ u where
  rate_pos : r > 0
  init_zero: u 0 = 0
  dist: ∀ t₁ t₂ : ℝ≥0, t₁ ≤ t₂ →
    ∀ n : ℕ, μ {ω | u t₂ ω - u t₁ ω = n} = poissonPMFReal (r * (t₂ - t₁)) n


-- PoissonProcessLittleo: Little-o based definition of a Poisson process
@[class] structure PoissonProcessLittleo (μ : ProbabilityMeasure Ω) (u : ℝ≥0 → Ω → ℕ)
[CountingProcess u]:
Prop extends StationaryIncrements μ u, IndependentIncrements μ u where
  rate_pos   : r > 0
  init_zero   : u 0 = 0
  single_jump : ∃ f : ℝ → ℝ, (f =o[𝓝[>] 0] id) ∧
    (∀ h : ℝ≥0, μ {ω | u h ω = 1} = (r * h : ℝ) + f h)
  multi_jump  : ∃ f : ℝ → ℝ, (f =o[𝓝[>] 0] id) ∧
    (∀ h : ℝ≥0, μ {ω | u h ω ≥ 2} = (f h))

--1 The following section proves that pmf definition implies littlo definition

-- 1.1 Show PoissonProcessPmf ⇒ stationary increments property
theorem poisson_process_pmf_has_stationary_increments {μ : ProbabilityMeasure Ω}
{u : ℝ≥0 → Ω → ℕ} [CountingProcess u]
  (h1 : PoissonProcessPmf r μ u) : StationaryIncrements μ u := by
  constructor
  intro t₁ t₂ s t1_le_t2 n
  have h_t1_t2 := h1.dist t₁ t₂ t1_le_t2 n
  have h_t1s_t2s :=
    h1.dist (t₁ + s) (t₂ + s) (by simp only [add_le_add_iff_right, t1_le_t2]) n
  have : t₂ + s - (t₁ + s) = t₂ - t₁ := add_tsub_add_eq_tsub_right t₂ s t₁
  apply NNReal.eq
  rw [h_t1_t2, h_t1s_t2s, this]

--1.2 This section is to write the closed form of the probability density function of
--  the Poisson process pmf to be used in the proof littlo of definition littleo

-- Zero jumps: P(u(h)=0) = e^{-r h}
lemma poisson_process_pmf_zero_jump {μ : ProbabilityMeasure Ω} {u : ℝ≥0 → Ω → ℕ}
[CountingProcess u] (h1 : PoissonProcessPmf r μ u) :
  ∀ h : ℝ≥0, μ {ω | u h ω = 0} = Real.exp (- (r * h)) := by
  intro h
  have : { ω | u h ω = 0 } = { ω | u h ω - u 0 ω = 0 } := by
    simp only [h1.init_zero, Pi.zero_apply, tsub_zero]
  rw [this, h1.dist 0 h (zero_le h) 0]
  simp [poissonPMFReal]


-- Single jump: P(u(h)=1) = e^{-r h} * (r h)
lemma poisson_process_pmf_single_jump {μ : ProbabilityMeasure Ω} {u : ℝ≥0 → Ω → ℕ}
  [CountingProcess u] (h1 : PoissonProcessPmf r μ u) :
  ∀ h : ℝ≥0, μ {ω | u h ω = 1} = Real.exp (-r * h) * (r * h) := by
  intro h
  have : { ω | u h ω = 1 } = { ω | u h ω - u 0 ω = 1 } := by
    simp only [h1.init_zero, Pi.zero_apply, tsub_zero]
  rw [this, h1.dist 0 h (zero_le h) 1]
  simp [poissonPMFReal]


-- helper theorem for probability measure used in the proof of
--  poisson_process_pmf_multiple_jump
theorem probability_measure_union {μ : ProbabilityMeasure Ω} {A B : Set Ω}
  (hB : MeasurableSet B) (hAB : Disjoint A B) :
  μ (A ∪ B) = μ A + μ B := by
  refine ENNReal.coe_inj.mp ?_
  simpa using measure_union hAB hB

-- Multiple jumps: P(u(h)≥2) = 1 - e^{-r h}(1 + r h)
lemma poisson_process_pmf_multiple_jump {μ : ProbabilityMeasure Ω} {u : ℝ≥0 → Ω → ℕ}
  [CountingProcess u] (h1 : PoissonProcessPmf r μ u):
  ∀ h : ℝ≥0, μ {ω | u h ω ≥ 2} =
  (1:ℝ) - Real.exp (-(r * h)) * (r * h : ℝ) - Real.exp (-(r*h)) := by
  intro h
  have complement : (μ {ω | u h ω ≥ 2} :ℝ) =
    1 - μ {ω | u h ω = 0} - μ {ω | u h ω = 1} := by
    have partition : univ = {ω | u h ω = 0} ∪ {ω | u h ω = 1} ∪ {ω | u h ω ≥ 2} := by
      ext ω
      simp only [mem_univ, ge_iff_le, mem_union, mem_setOf_eq, true_iff]
      cases Nat.eq_or_lt_of_le (zero_le (u h ω)) with
      | inl h_eq => left; exact Or.symm (Or.inr (id (Eq.symm h_eq)))
      | inr h_gt => cases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt h_gt) with
        | inl h_eq => left; right; exact id (Eq.symm h_eq)
        | inr h_ge => right; exact h_ge

    have disjoint1 : Disjoint {ω | u h ω = 0} {ω | u h ω = 1} := by
      rw [disjoint_iff_inter_eq_empty]
      ext ω
      simp only [mem_inter_iff, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
      intro h_eq0 h_eq1
      linarith

    have disjoint2 : Disjoint {ω | u h ω = 0} {ω | u h ω ≥ 2} := by
      rw [disjoint_iff_inter_eq_empty]
      ext ω
      simp only [ge_iff_le, mem_inter_iff, mem_setOf_eq,
        mem_empty_iff_false,iff_false, not_and, not_le]
      intro h_eq0
      linarith

    have disjoint3 : Disjoint {ω | u h ω = 1} {ω | u h ω ≥ 2} := by
      rw [disjoint_iff_inter_eq_empty]
      ext ω
      simp only [ge_iff_le, mem_inter_iff, mem_setOf_eq,
        mem_empty_iff_false, iff_false, not_and, not_le]
      intro h_eq1
      linarith

    have meas_add : μ univ =
      μ {ω | u h ω = 0} + μ {ω | u h ω = 1} + μ {ω | u h ω ≥ 2} := by
      rw [partition, probability_measure_union, probability_measure_union]
      refine measurableSet_eq_fun' ?_.hf ?_.hg
      . exact ‹CountingProcess u›.measurable_value h
      . exact measurable_const
      . exact disjoint1
      . refine measurableSet_le ?hB.hf ?hB.hg
        . exact measurable_const
        . exact ‹CountingProcess u›.measurable_value h
      . exact Disjoint.union_left disjoint2 disjoint3
    simp only [ProbabilityMeasure.coeFn_univ, ge_iff_le] at meas_add
    have: (1 :ℝ) = ↑(μ {ω | u h ω = 0} + μ {ω | u h ω = 1} + μ {ω | 2 ≤ u h ω}) := by
      rw [← NNReal.coe_one, meas_add]
    rw [this, NNReal.coe_add, NNReal.coe_add]
    ring
  rw [complement, poisson_process_pmf_zero_jump r h1 h, poisson_process_pmf_single_jump r h1 h]
  ring_nf

-- 1.3 This section is to actually prove that poisson process definition pmf implies poisson
--  process definition littleo for the little o conditions

-- Error term for single jump little-o condition
noncomputable def single_jump_error (r : ℝ≥0) (h : ℝ) : ℝ :=
  Real.exp (-r * h) * (r * h) - r * h

-- single_jump_error = o(h) as h → 0
lemma single_jump_error_is_littleo (r : ℝ≥0) (hr: r > 0):
  (fun h : ℝ  => single_jump_error r h) =o[𝓝[>] 0] id := by
  have outer_isLittleO :
    (fun x : ℝ => Real.exp (-x) * x - x) =o[𝓝[>] 0] (fun x:ℝ => x) := by
    rw [isLittleO_iff]
    intro c hc
    rw [eventually_nhdsWithin_iff]
    simp only [mem_Ioi, Real.norm_eq_abs]
    conv =>
      lhs
      ext x hx
      rw (occs := .pos [3]) [← one_mul x]
      rw [← mul_sub_right_distrib, abs_mul, @abs_of_nonneg _ _ _ x _ (le_of_lt hx),
        abs_of_neg (sub_neg_of_lt (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hx)))]
      simp
    rw [Metric.eventually_nhds_iff_ball]
    by_cases h1c : 1-c ≤ 0
    . use 1
      constructor
      . exact Real.zero_lt_one
      . intro y hy ypos
        simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hy
        have : 1 - Real.exp (-y) ≤ c := by
          simpa [add_comm] using le_trans h1c (Real.exp_nonneg (-y))
        exact mul_le_mul_of_nonneg_right this (le_of_lt ypos)
    . use Real.log (1/(1-c))
      push_neg at h1c
      -- simp at h1c
      constructor
      . exact Real.log_pos ((one_lt_div h1c).mpr
          (by simp_all only [gt_iff_lt, sub_lt_self_iff]))
      . intro y hy ypos
        simp only [one_div, Real.log_inv, Metric.mem_ball,
          dist_zero_right, Real.norm_eq_abs] at hy
        have : 1 - Real.exp (-y) ≤ c := by
          simpa [Real.exp_log h1c, add_comm] using le_of_lt
            (Real.exp_lt_exp_of_lt (lt_neg_of_lt_neg (lt_of_abs_lt hy)))
        exact mul_le_mul_of_nonneg_right this (le_of_lt ypos)

  have inner_tendsto : Tendsto (fun h : ℝ => r * h) (𝓝[>] 0) (𝓝[>] 0) := by
    let r:= (r : ℝ)
    have hr : 0 < r := NNReal.coe_pos.mp hr
    have id_tendsto : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝[>] 0) := tendsto_id
    simpa using TendstoNhdsWithinIoi.const_mul hr id_tendsto

  have div_rh_isLittleO : (fun h : ℝ  => Real.exp (-↑r * h) * (↑r * h) - ↑r * h) =o[𝓝[>]0]
    (fun x:ℝ => r * id x) := by
    convert IsLittleO.comp_tendsto outer_isLittleO inner_tendsto using 1
    funext x
    simp

  exact (isLittleO_const_mul_right_iff (ne_of_gt hr)).mp
    div_rh_isLittleO


-- actually proves that poisson process definition pmf implies poisson process
--  definition littleo for the single jump condition
theorem poisson_process_pmf_implies_process_littleo_single_jump {μ : ProbabilityMeasure Ω}
{u : ℝ≥0 → Ω → ℕ} [CountingProcess u] (h1 : PoissonProcessPmf r μ u) :
  ∃ f : ℝ → ℝ, (f =o[𝓝[>] 0] id) ∧
    (∀ h : ℝ≥0, μ {ω | u h ω = 1} = (r * h : ℝ) + f h) := by
  use (fun h : ℝ  => single_jump_error r h)
  constructor
  . exact single_jump_error_is_littleo r h1.rate_pos
  . unfold single_jump_error
    intro h
    rw [poisson_process_pmf_single_jump r h1 h]
    simp

-- helper theorem to be used in proof of latter
theorem sum_eq : ∀ x:ℝ, ∑ i ∈ Finset.range (1 + 1), x ^ i / ↑i.factorial = 1+x := by
  simp [Finset.sum_range_succ]

-- Error term for multiple jumps little-o condition
noncomputable def zero_jump_error (r : ℝ≥0) (h : ℝ) : ℝ :=
  Real.exp (-(r * h)) - (1 - r * h)

-- zero_jump_error = o(h) as h → 0
lemma zero_jump_error_is_littleo (hr: r > 0):
  (fun h : ℝ  => zero_jump_error r h) =o[𝓝[>] 0] id := by
  have rh_tendsto : Tendsto (fun h : ℝ => -r * h) (𝓝 0) (𝓝 0) := by
    simpa using (@tendsto_id ℝ (𝓝 0)).const_mul (-r : ℝ)

  have exp_pos_isLittleO : (fun h : ℝ => Real.exp (h) - (1 + h)) =o[𝓝 0] (fun h => h) := by
    simpa [←sum_eq] using Real.exp_sub_sum_range_succ_isLittleO_pow 1

  have exp_neg_rh_isLittleO : (fun h : ℝ => Real.exp (-r * h) - (1 - r * h)) =o[𝓝 0]
  (fun h => h) := by
    have: (fun h : ℝ => Real.exp (-r * h) - (1 - r * h)) =
              ((fun x ↦ Real.exp x - (1 + x)) ∘ (fun h ↦ -r * h)) := by
      ext h
      simp only [Function.comp_apply]
      ring_nf
    rw [this]
    simpa using (isLittleO_const_mul_right_iff (neg_ne_zero.mpr (ne_of_gt hr))).mp
      (exp_pos_isLittleO.comp_tendsto rh_tendsto)

  unfold zero_jump_error
  simpa using exp_neg_rh_isLittleO.mono (nhdsWithin_le_nhds)


-- actually proves that poisson process definition pmf implies poisson process littleo
theorem poisson_process_pmf_implies_process_littleo_multi_jump {μ : ProbabilityMeasure Ω} {u : ℝ≥0 → Ω → ℕ}
  [CountingProcess u] (h1 : PoissonProcessPmf r μ u) :
  ∃ f : ℝ → ℝ, (f =o[𝓝[>] 0] id) ∧ ( ∀ h : ℝ≥0, μ {ω | u h ω ≥ 2} = f h) := by
  use (fun h : ℝ => -1 * (zero_jump_error r h + single_jump_error r h))
  constructor
  . exact ((zero_jump_error_is_littleo r h1.rate_pos).add
      (single_jump_error_is_littleo r h1.rate_pos)).const_mul_left (-1)
  . intro h
    rw [poisson_process_pmf_multiple_jump r h1 h]
    unfold zero_jump_error single_jump_error
    simp only [neg_mul, one_mul, neg_add_rev, neg_sub]
    ring_nf


-- Main equivalence theorem
theorem poisson_process_equiv {μ : ProbabilityMeasure Ω} {u : ℝ≥0 → Ω → ℕ}
  [CountingProcess u]:
  PoissonProcessPmf r μ u ↔ PoissonProcessLittleo r μ u := by
  apply Iff.intro
  . intro h1
    constructor
    . exact poisson_process_pmf_has_stationary_increments r h1
    . exact h1.toIndependentIncrements
    . exact h1.rate_pos
    . exact h1.init_zero
    . exact poisson_process_pmf_implies_process_littleo_single_jump r h1
    . exact poisson_process_pmf_implies_process_littleo_multi_jump r h1
  . sorry  -- reverse direction


@[class] structure IsPoissonProcess {μ : ProbabilityMeasure Ω}
  (u : ℝ≥0 → Ω → ℕ) [CountingProcess u] : Prop where
  to_def1 : PoissonProcessPmf r μ u
  to_def2 : PoissonProcessLittleo r μ u
