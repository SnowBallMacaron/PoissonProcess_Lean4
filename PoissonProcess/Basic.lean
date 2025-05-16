import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Poisson
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.Calculus.LHopital

open MeasureTheory Set ProbabilityTheory Asymptotics Filter NNReal ENNReal Topology

section PoissonProcess

variable {Ω: Type*} [MeasurableSpace Ω] {μ : ProbabilityMeasure Ω}
variable {l: Filter ℝ}
variable (u : ℝ≥0 → Ω → ℕ) (f: ℝ → ℝ)


@[class] structure IsCountingProcess (u : ℝ≥0 → Ω → ℕ) : Prop where
  -- Measurable
  measurable_process : Measurable u
  measurable_value : ∀ t : ℝ≥0, Measurable (u t)
  -- u(t) ≥ 0
  nonneg : ∀ (t : ℝ≥0) (ω : Ω), u t ω ≥ 0
  -- -- u(t) is integer valued
  -- integer : ∀ (t : ℝ≥0) (ω : Ω), ∃ (n : ℕ), u t ω = n
  -- Monotonicity
  monotone : ∀ (ω : Ω) (s t : ℝ≥0), s < t → u s ω ≤ u t ω


structure HasIndpendentIncrements (μ : ProbabilityMeasure Ω) (u : ℝ≥0 → Ω → ℕ) : Prop where
 indepInc : ∀ (n : ℕ) (t : Fin (n+1) → ℝ≥0),
   (∀ i : Fin n, t i < t i.succ) →
   iIndepFun (fun _ => inferInstance) (fun i => fun ω => u (t i.succ) ω - u (t i) ω) μ


structure HasStationaryIncrements (μ : ProbabilityMeasure Ω) (u : ℝ≥0 → Ω → ℕ) : Prop where
  stationInc : ∀ t₁ t₂ s : ℝ≥0, t₁ ≤ t₂ →
    ∀ n : ℕ, μ {ω | u t₂ ω - u t₁ ω = n} = μ {ω | u (t₂ + s) ω - u (t₁ + s) ω = n}


@[class] structure IsPoissonProcess1 (μ : ProbabilityMeasure Ω) (u : ℝ≥0 → Ω → ℕ) [IsCountingProcess u] (r : ℝ≥0) : Prop where
  i: u 0 = 0
  ii: HasIndpendentIncrements μ u
  iii: ∀ t₁ t₂ : ℝ≥0, t₁ ≤ t₂ →
    ∀ n : ℕ, μ {ω | u t₂ ω - u t₁ ω = n} = poissonPMFReal (r * (t₂ - t₁)) n


-- noncomputable def pfiii (μ : ProbabilityMeasure Ω) (u : ℝ≥0 → Ω → ℕ) (r : ℝ≥0)
--   (h : ℝ≥0): ℝ :=
--   if h = 0 then 0 else (μ {ω | u h ω = 1} :ℝ) - ((r * h) :ℝ) / (h :ℝ)


@[class] structure IsPoissonProcess2 (μ : ProbabilityMeasure Ω) (u : ℝ≥0 → Ω → ℕ) [IsCountingProcess u] (r : ℝ≥0): Prop where
  i   : u 0 = 0
  ii  : HasIndpendentIncrements μ u ∧ HasStationaryIncrements μ u
  iii : ∃ f : ℝ → ℝ, (f =o[𝓝[>] 0] id) ∧ (∀ h : ℝ≥0, μ {ω | u h ω = 1} = (r * h : ℝ) + f h)
  iv  : ∃ f : ℝ → ℝ, (f =o[𝓝[>] 0] id) ∧ (∀ h : ℝ≥0, μ {ω | u h ω ≥ 2} = (f h))


example (y : ℝ) (h1: ∀ x:ℝ, if x≥0 then x=y else x>y) :  ∀x:ℝ≥0, x=y:= by
  intro x
  simpa using h1 x

-- Poisson Process satisfies stationary increments
theorem poisson_process1_has_stationary_increments {μ : ProbabilityMeasure Ω} {u : ℝ≥0 → Ω → ℕ} [IsCountingProcess u] {r : ℝ≥0}
  (h1 : IsPoissonProcess1 μ u r) : HasStationaryIncrements μ u := by
  constructor
  intro t₁ t₂ s t1_le_t2 n
  have h_t1_t2 := h1.iii t₁ t₂ t1_le_t2 n
  have h_t1s_t2s := h1.iii (t₁ + s) (t₂ + s) (by simp only [add_le_add_iff_right, t1_le_t2]) n
  have : t₂ + s - (t₁ + s) = t₂ - t₁ := add_tsub_add_eq_tsub_right t₂ s t₁
  apply NNReal.eq
  rw [h_t1_t2, h_t1s_t2s, this]


theorem poisson_process1_zero_jump {μ : ProbabilityMeasure Ω} {u : ℝ≥0 → Ω → ℕ} [IsCountingProcess u] {r : ℝ≥0}
  (h1 : IsPoissonProcess1 μ u r) :
  ∀ h : ℝ≥0, μ {ω | u h ω = 0} = Real.exp (- (r * h)) := by
  intro h
  have : { ω | u h ω = 0 } = { ω | u h ω - u 0 ω = 0 } := by simp only [h1.i, Pi.zero_apply, tsub_zero]
  rw [this, h1.iii 0 h (zero_le h) 0]
  simp [poissonPMFReal]


-- Poisson Process 1 has the single jump probability property
theorem poisson_process1_single_jump {μ : ProbabilityMeasure Ω} {u : ℝ≥0 → Ω → ℕ} [IsCountingProcess u] {r : ℝ≥0}
  (h1 : IsPoissonProcess1 μ u r) :
  ∀ h : ℝ≥0, μ {ω | u h ω = 1} = Real.exp (-r * h) * (r * h) := by
  intro h
  have : { ω | u h ω = 1 } = { ω | u h ω - u 0 ω = 1 } := by simp only [h1.i, Pi.zero_apply, tsub_zero]
  rw [this, h1.iii 0 h (zero_le h) 1]
  simp [poissonPMFReal]


example (a b c: NNReal) (h : 1 = a + b + c): (1:ℝ) = a + b + c := by
  have h_real : (1 : ℝ) = ↑(a + b + c) := by
    rw [← NNReal.coe_one, h]
  rw [h_real, NNReal.coe_add, NNReal.coe_add]


theorem probability_measure_union {μ : ProbabilityMeasure Ω} {A B : Set Ω} (hB : MeasurableSet B) (hAB : Disjoint A B) :
  μ (A ∪ B) = μ A + μ B := by
  refine ENNReal.coe_inj.mp ?_
  simpa using measure_union hAB hB


theorem poisson_process1_multiple_jump {μ : ProbabilityMeasure Ω} {u : ℝ≥0 → Ω → ℕ} [IsCountingProcess u] {r : ℝ≥0}
  (h1 : IsPoissonProcess1 μ u r):
   ∀ h : ℝ≥0, μ {ω | u h ω ≥ 2} = (1:ℝ) - Real.exp (-(r * h)) * (r * h : ℝ) - Real.exp (-(r*h)) := by
  intro h
  have complement : (μ {ω | u h ω ≥ 2} :ℝ) = 1 - μ {ω | u h ω = 0} - μ {ω | u h ω = 1} := by
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
      simp only [ge_iff_le, mem_inter_iff, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_le]
      intro h_eq0
      linarith

    have disjoint3 : Disjoint {ω | u h ω = 1} {ω | u h ω ≥ 2} := by
      rw [disjoint_iff_inter_eq_empty]
      ext ω
      simp only [ge_iff_le, mem_inter_iff, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_le]
      intro h_eq1
      linarith

    have meas_add : μ univ = μ {ω | u h ω = 0} + μ {ω | u h ω = 1} + μ {ω | u h ω ≥ 2} := by
      rw [partition, probability_measure_union, probability_measure_union]
      refine measurableSet_eq_fun' ?_.hf ?_.hg
      . exact ‹IsCountingProcess u›.measurable_value h
      . exact measurable_const
      . exact disjoint1
      . refine measurableSet_le ?hB.hf ?hB.hg
        . exact measurable_const
        . exact ‹IsCountingProcess u›.measurable_value h
      . exact Disjoint.union_left disjoint2 disjoint3
    simp only [ProbabilityMeasure.coeFn_univ, ge_iff_le] at meas_add
    -- have eq1_le_1_sub_eq0: μ {ω | u h ω = 1} ≤ 1 - μ {ω | u h ω = 0} := by
    --   rw [meas_add, add_comm, add_comm (μ {ω | u h ω = 0}), ←add_assoc]
    --   simp
    -- simp
    have: (1 :ℝ) = ↑(μ {ω | u h ω = 0} + μ {ω | u h ω = 1} + μ {ω | 2 ≤ u h ω}) := by
      rw [← NNReal.coe_one, meas_add]
    rw [this, NNReal.coe_add, NNReal.coe_add]
    ring
  rw [complement, poisson_process1_zero_jump h1 h, poisson_process1_single_jump h1 h]
  ring_nf



noncomputable def f2iii (r : ℝ≥0) (h : ℝ) : ℝ :=
  Real.exp (-r * h) * (r * h) - r * h

theorem f2iii_is_little_O (r : ℝ≥0) (hr: r > 0): (fun h : ℝ  => f2iii r h) =o[𝓝[>] 0] id := by
  have outer_isLittleO : (fun x : ℝ => Real.exp (-x) * x - x) =o[𝓝[>] 0] (fun x:ℝ => x) := by
    rw [isLittleO_iff]
    intro c hc
    rw [eventually_nhdsWithin_iff]
    simp only [mem_Ioi, Real.norm_eq_abs]
    conv =>
      lhs
      ext x hx
      rw (occs := .pos [3]) [← one_mul x]
      rw [← mul_sub_right_distrib, abs_mul, @abs_of_nonneg _ _ _ x _ (le_of_lt hx), abs_of_neg (sub_neg_of_lt (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hx)))]
      simp
    rw [Metric.eventually_nhds_iff_ball]
    by_cases h1c : 1-c ≤ 0
    . use 1
      constructor
      . exact Real.zero_lt_one
      . intro y hy ypos
        simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hy
        have : 1 - Real.exp (-y) ≤ c := by simpa [add_comm] using le_trans h1c (Real.exp_nonneg (-y))
        exact mul_le_mul_of_nonneg_right this (le_of_lt ypos)
    . use Real.log (1/(1-c))
      push_neg at h1c
      -- simp at h1c
      constructor
      . exact Real.log_pos ((one_lt_div h1c).mpr (by simp_all only [gt_iff_lt, sub_lt_self_iff]))
      . intro y hy ypos
        simp only [one_div, Real.log_inv, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hy
        have : 1 - Real.exp (-y) ≤ c := by
          simpa [Real.exp_log h1c, add_comm] using le_of_lt (Real.exp_lt_exp_of_lt (lt_neg_of_lt_neg (lt_of_abs_lt hy)))
        exact mul_le_mul_of_nonneg_right this (le_of_lt ypos)

  have inner_tendsto : Tendsto (fun h : ℝ => r * h) (𝓝[>] 0) (𝓝[>] 0) := by
    let r:= (r : ℝ)
    have hr : 0 < r := NNReal.coe_pos.mp hr
    have id_tendsto : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝[>] 0) := tendsto_id
    simpa using TendstoNhdsWithinIoi.const_mul hr id_tendsto

  have div_rh_isLittleO : (fun h : ℝ  => Real.exp (-↑r * h) * (↑r * h) - ↑r * h) =o[𝓝[>] 0] (fun x:ℝ => r * id x) := by
    convert IsLittleO.comp_tendsto outer_isLittleO inner_tendsto using 1
    funext x
    simp

  exact (isLittleO_const_mul_right_iff' (IsUnit.mk0 r.toReal (by positivity))).mp div_rh_isLittleO


theorem poisson_process1_implies_process2iii {μ : ProbabilityMeasure Ω} {u : ℝ≥0 → Ω → ℕ} [IsCountingProcess u] (r : ℝ≥0) (hr: r > 0)
  (h1 : IsPoissonProcess1 μ u r) :
  ∃ f : ℝ → ℝ, (f =o[𝓝[>] 0] id) ∧ (∀ h : ℝ≥0, μ {ω | u h ω = 1} = (r * h : ℝ) + f h) := by
  -- have h_single_jump := poisson_process1_single_jump h1
  -- have h_asymp := f2iii_is_little_O r hr
  use (fun h : ℝ  => f2iii r h)
  constructor
  . exact f2iii_is_little_O r hr
  . unfold f2iii
    intro h
    rw [poisson_process1_single_jump h1 h]
    simp

theorem sum_eq : ∀ x:ℝ, ∑ i ∈ Finset.range (1 + 1), x ^ i / ↑i.factorial = 1+x := by
  simp [Finset.sum_range_succ]

example : (fun x : ℝ => Real.exp x - (1 + x)) =o[nhds 0] fun x => x := by
  simpa [←sum_eq] using Real.exp_sub_sum_range_succ_isLittleO_pow 1


-- noncomputable def f2iv (r : ℝ≥0) (h : ℝ≥0) : ℝ :=
--   1 - poissonPMFReal (r * h) 0 - poissonPMFReal (r * h) 1

noncomputable def f_zero (r : ℝ≥0) (h : ℝ) : ℝ :=
  Real.exp (-(r * h)) - (1 - r * h)

theorem f_zero_is_little_O (r : ℝ≥0) (hr: r > 0): (fun h : ℝ  => f_zero r h) =o[𝓝[>] 0] id := by
  have neg_id_tendsto : Tendsto (fun h : ℝ => -1 * h) (𝓝 0) (𝓝 0) := by
    simpa using (@tendsto_id ℝ (𝓝 0)).const_mul (-1 : ℝ)

  have inner_tendsto : Tendsto (fun h : ℝ => r * h) (𝓝 0) (𝓝 0) := by
    let r:= (r : ℝ)
    have hr : 0 < r := NNReal.coe_pos.mp hr
    have id_tendsto : Tendsto (fun h : ℝ => h) (𝓝 0) (𝓝 0) := tendsto_id
    simpa using id_tendsto.const_mul r

  have exp_pos_isLittleO : (fun x : ℝ => Real.exp (x) - (1 + x))=o[𝓝 0] (fun x => x) := by
    simpa [←sum_eq] using Real.exp_sub_sum_range_succ_isLittleO_pow 1

  have exp_neg_isLittleO : (fun x : ℝ => Real.exp (-x) - (1 - x))=o[𝓝 0] (fun x => x) := by
    have h1 : (fun x : ℝ => Real.exp (-x) - (1 - x)) = ((fun x ↦ Real.exp x - (1 + x)) ∘ fun h ↦ -h) := by
      ext x
      simp only [Function.comp_apply, _root_.sub_right_inj]
      ring_nf

    have h2 : (fun x : ℝ => x) = ((fun x ↦ -x) ∘ fun h ↦ -h) := by
      ext x
      simp
    rw [h1, h2]

    simpa using (isLittleO_const_mul_right_iff' (IsUnit.mk0 (-1 : ℝ) (by positivity))).mp (exp_pos_isLittleO.comp_tendsto neg_id_tendsto)

  have div_rh_isLittleO : (fun h : ℝ  => Real.exp (-↑r * h) - (1 - ↑r * h)) =o[𝓝 0] (fun x:ℝ => r * id x) := by
    convert IsLittleO.comp_tendsto exp_neg_isLittleO inner_tendsto using 1
    funext x
    simp
  unfold f_zero
  simpa using ((isLittleO_const_mul_right_iff' (IsUnit.mk0 r.toReal (by positivity))).mp div_rh_isLittleO).mono (nhdsWithin_le_nhds)


theorem zero_jump_littleO {μ : ProbabilityMeasure Ω} {u : ℝ≥0 → Ω → ℕ} [IsCountingProcess u] (r : ℝ≥0) (hr: r > 0)
  (h1 : IsPoissonProcess1 μ u r) :
  ∃ f : ℝ → ℝ, (f =o[𝓝[>] 0] id) ∧ ( ∀ h : ℝ≥0, μ {ω | u h ω =0} = 1 - r * h + (f h)) := by
  use (fun h : ℝ => Real.exp (- (r * h)) - (1 - r*h))
  constructor
  . exact f_zero_is_little_O r hr
  . simpa using poisson_process1_zero_jump h1

theorem poisson_process1_implies_process2iv {μ : ProbabilityMeasure Ω} {u : ℝ≥0 → Ω → ℕ} [IsCountingProcess u] (r : ℝ≥0) (hr: r > 0)
  (h1 : IsPoissonProcess1 μ u r) :
  ∃ f : ℝ → ℝ, (f =o[𝓝[>] 0] id) ∧ ( ∀ h : ℝ≥0, μ {ω | u h ω ≥ 2} = f h) := by
  -- have h_multiple_jump := poisson_process1_multiple_jump h1
  use (fun h : ℝ => -1 * (f_zero r h + f2iii r h))
  constructor
  . exact ((f_zero_is_little_O r hr).add (f2iii_is_little_O r hr)).const_mul_left (-1)
  . intro h
    rw [poisson_process1_multiple_jump h1 h]
    unfold f_zero f2iii
    simp only [neg_mul, one_mul, neg_add_rev, neg_sub]
    ring_nf

-- Main equivalence theorem
theorem poisson_process_equiv {μ : ProbabilityMeasure Ω} {u : ℝ≥0 → Ω → ℕ} [IsCountingProcess u] {r : ℝ≥0} {hr: r > 0}:
  IsPoissonProcess1 μ u r ↔ IsPoissonProcess2 μ u r := by
  apply Iff.intro
  . intro h1
    constructor
    . exact h1.i  -- part i
    . constructor  -- part ii Independent and stationary increments
      . exact h1.ii  -- Independent increments
      . exact poisson_process1_has_stationary_increments h1  -- Stationary increments

    . exact poisson_process1_implies_process2iii r hr h1 -- part iii
    . exact poisson_process1_implies_process2iv r hr h1 -- part iv

  . sorry  -- reverse direction


@[class] structure IsPoissonProcess {μ : ProbabilityMeasure Ω}
  (u : ℝ≥0 → Ω → ℕ) [IsCountingProcess u] (r : ℝ≥0) : Prop where
  to_def1 : IsPoissonProcess1 μ u r
  to_def2 : IsPoissonProcess2 μ u r
