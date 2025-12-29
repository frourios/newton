import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.MetricSpace.Holder
import Newton.MeasureTheory.Integral.Tonelli

open MeasureTheory Complex NNReal
open scoped ENNReal Topology ContDiff ComplexConjugate

namespace Newton

variable {n : ℕ}

lemma lintegral_mul_mul_le_three_holder
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g h : α → ℝ≥0∞}
    {p q r : ℝ≥0∞}
    (hpqr : 1 / p + 1 / q + 1 / r = 1)
    (hp_top : p ≠ ⊤) (hq_top : q ≠ ⊤) (hr_top : r ≠ ⊤)
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (hh : AEMeasurable h μ) :
    ∫⁻ x, f x * g x * h x ∂μ ≤
      (∫⁻ x, f x ^ p.toReal ∂μ) ^ (1/p.toReal) *
      (∫⁻ x, g x ^ q.toReal ∂μ) ^ (1/q.toReal) *
      (∫⁻ x, h x ^ r.toReal ∂μ) ^ (1/r.toReal) := by
  have hp_pos : 0 < p := by
    by_contra h_neg
    push_neg at h_neg
    have : p = 0 := le_antisymm h_neg (zero_le p)
    simp [this] at hpqr
  have hq_pos : 0 < q := by
    by_contra h_neg
    push_neg at h_neg
    have : q = 0 := le_antisymm h_neg (zero_le q)
    simp [this] at hpqr
  have hr_pos : 0 < r := by
    by_contra h_neg
    push_neg at h_neg
    have : r = 0 := le_antisymm h_neg (zero_le r)
    simp [this] at hpqr
  -- Convert to real numbers
  have hp_real_pos : 0 < p.toReal := ENNReal.toReal_pos hp_pos.ne' hp_top
  have hq_real_pos : 0 < q.toReal := ENNReal.toReal_pos hq_pos.ne' hq_top
  have hr_real_pos : 0 < r.toReal := ENNReal.toReal_pos hr_pos.ne' hr_top
  -- Finiteness lemmas
  have h_finite_p : 1/p ≠ ⊤ := ENNReal.div_ne_top ENNReal.one_ne_top hp_pos.ne'
  have h_finite_q : 1/q ≠ ⊤ := ENNReal.div_ne_top ENNReal.one_ne_top hq_pos.ne'
  have h_finite_r : 1/r ≠ ⊤ := ENNReal.div_ne_top ENNReal.one_ne_top hr_pos.ne'
  -- Convert exponent condition to real numbers
  have hpqr_real : 1/p.toReal + 1/q.toReal + 1/r.toReal = 1 := by
    have h1 : (1/p).toReal = 1/p.toReal := ENNReal.toReal_div 1 p
    have h2 : (1/q).toReal = 1/q.toReal := ENNReal.toReal_div 1 q
    have h3 : (1/r).toReal = 1/r.toReal := ENNReal.toReal_div 1 r
    have h_pq_ne_top : 1/p + 1/q ≠ ⊤ := ENNReal.add_ne_top.2 ⟨h_finite_p, h_finite_q⟩
    have h_sum : (1/p + 1/q + 1/r).toReal = 1 := by
      have : 1/p + 1/q + 1/r = 1 := hpqr
      rw [this, ENNReal.toReal_one]
    calc 1/p.toReal + 1/q.toReal + 1/r.toReal
        = (1/p).toReal + (1/q).toReal + (1/r).toReal := by rw [h1, h2, h3]
      _ = ((1/p) + (1/q)).toReal + (1/r).toReal := by
          rw [ENNReal.toReal_add h_finite_p h_finite_q]
      _ = ((1/p + 1/q) + (1/r)).toReal := by
          rw [ENNReal.toReal_add h_pq_ne_top h_finite_r]
      _ = 1 := h_sum
  let F : α → ℝ≥0∞ := fun x => (f x) ^ p.toReal
  let G : α → ℝ≥0∞ := fun x => (g x) ^ q.toReal
  let H : α → ℝ≥0∞ := fun x => (h x) ^ r.toReal
  have hF : AEMeasurable F μ := hf.pow_const p.toReal
  have hG : AEMeasurable G μ := hg.pow_const q.toReal
  have hH : AEMeasurable H μ := hh.pow_const r.toReal
  -- Lemma showing (f^p)^(1/p) = f
  have rpow_inv_cancel : ∀ (a : ℝ≥0∞) (t : ℝ), 0 < t → (a ^ t) ^ (1/t) = a := by
    intro a t ht
    rw [← ENNReal.rpow_mul, one_div, mul_inv_cancel₀ ht.ne', ENNReal.rpow_one]
  -- Show f * g * h = F^(1/p) * G^(1/q) * H^(1/r)
  have h_eq : ∀ x, f x * g x * h x =
      F x ^ (1/p.toReal) * G x ^ (1/q.toReal) * H x ^ (1/r.toReal) := by
    intro x
    simp only [F, G, H]
    rw [rpow_inv_cancel (f x) p.toReal hp_real_pos,
        rpow_inv_cancel (g x) q.toReal hq_real_pos,
        rpow_inv_cancel (h x) r.toReal hr_real_pos]
  -- Apply lintegral_prod_norm_pow_le using Finset.univ (Fin 3)
  let s : Finset (Fin 3) := Finset.univ
  let funcs : Fin 3 → α → ℝ≥0∞ := ![F, G, H]
  let exps : Fin 3 → ℝ := ![1/p.toReal, 1/q.toReal, 1/r.toReal]
  have h_meas : ∀ i ∈ s, AEMeasurable (funcs i) μ := by
    intro i _
    fin_cases i
    · exact hF
    · exact hG
    · exact hH
  have h_sum_exp : ∑ i ∈ s, exps i = 1 := by
    simp only [s, exps]
    rw [Fin.sum_univ_three]
    exact hpqr_real
  have h_nonneg : ∀ i ∈ s, 0 ≤ exps i := by
    intro i _
    fin_cases i
    · exact (one_div_pos.2 hp_real_pos).le
    · exact (one_div_pos.2 hq_real_pos).le
    · exact (one_div_pos.2 hr_real_pos).le
  have h_prod := ENNReal.lintegral_prod_norm_pow_le s h_meas h_sum_exp h_nonneg
  -- Transform to get the conclusion
  have h_lhs_eq : ∀ x, ∏ i ∈ s, funcs i x ^ exps i =
      F x ^ (1/p.toReal) * G x ^ (1/q.toReal) * H x ^ (1/r.toReal) := by
    intro x
    simp only [s, funcs, exps]
    rw [Fin.prod_univ_three]
    rfl
  have h_rhs_eq : ∏ i ∈ s, (∫⁻ x, funcs i x ∂μ) ^ exps i =
      (∫⁻ x, F x ∂μ) ^ (1/p.toReal) * (∫⁻ x, G x ∂μ) ^ (1/q.toReal) *
      (∫⁻ x, H x ∂μ) ^ (1/r.toReal) := by
    simp only [s, funcs, exps]
    rw [Fin.prod_univ_three]
    rfl
  calc ∫⁻ x, f x * g x * h x ∂μ
      = ∫⁻ x, F x ^ (1/p.toReal) * G x ^ (1/q.toReal) * H x ^ (1/r.toReal) ∂μ := by
        congr 1; ext x; exact h_eq x
    _ = ∫⁻ x, ∏ i ∈ s, funcs i x ^ exps i ∂μ := by
        congr 1; ext x; exact (h_lhs_eq x).symm
    _ ≤ ∏ i ∈ s, (∫⁻ x, funcs i x ∂μ) ^ exps i := h_prod
    _ = (∫⁻ x, F x ∂μ) ^ (1/p.toReal) * (∫⁻ x, G x ∂μ) ^ (1/q.toReal) *
        (∫⁻ x, H x ∂μ) ^ (1/r.toReal) := h_rhs_eq
    _ = (∫⁻ x, f x ^ p.toReal ∂μ) ^ (1/p.toReal) * (∫⁻ x, g x ^ q.toReal ∂μ) ^ (1/q.toReal) *
        (∫⁻ x, h x ^ r.toReal ∂μ) ^ (1/r.toReal) := by rfl

lemma young_exponent_p_le_r
    {p q r : ℝ≥0∞} (hq : 1 ≤ q) (hpqr : 1 / p + 1 / q = 1 + 1 / r) :
    p ≤ r := by
  -- From 1/p + 1/q = 1 + 1/r, we have 1/p ≤ 1 + 1/r
  -- Since q ≥ 1, we have 1/q ≤ 1, so 1/p ≥ 1/r
  -- Therefore p ≤ r
  by_contra h_neg
  push_neg at h_neg
  have h_inv : 1/p < 1/r := by
    rw [one_div, one_div]
    exact ENNReal.inv_lt_inv.mpr h_neg
  have hq_inv : 1/q ≤ 1 := by
    rw [one_div, ENNReal.inv_le_one]
    exact hq
  -- 1/p + 1/q < 1/r + 1 = 1 + 1/r
  have hq_pos : q ≠ 0 := (one_pos.trans_le hq).ne'
  have h_one_div_q_ne_top : 1/q ≠ ⊤ := by simp [hq_pos]
  have h_sum : 1/p + 1/q < 1/r + 1 := by
    calc 1/p + 1/q < 1/r + 1/q := ENNReal.add_lt_add_right h_one_div_q_ne_top h_inv
      _ ≤ 1/r + 1 := add_le_add_right hq_inv (1/r)
  rw [add_comm (1/r) 1] at h_sum
  rw [hpqr] at h_sum
  exact lt_irrefl _ h_sum

/-- Auxiliary lemma to derive q ≤ r from Young exponent condition -/
lemma young_exponent_q_le_r
    {p q r : ℝ≥0∞} (hp : 1 ≤ p) (hpqr : 1 / p + 1 / q = 1 + 1 / r) :
    q ≤ r := by
  have hpqr' : 1/q + 1/p = 1 + 1/r := by rw [add_comm]; exact hpqr
  exact young_exponent_p_le_r hp hpqr'

/-- Auxiliary lemma to derive r ≥ 1 from Young exponent condition -/
lemma young_exponent_r_ge_one
    {p q r : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q) (hpqr : 1 / p + 1 / q = 1 + 1 / r) :
    1 ≤ r := by
  have hp_inv : 1/p ≤ 1 := by rw [one_div, ENNReal.inv_le_one]; exact hp
  have hq_inv : 1/q ≤ 1 := by rw [one_div, ENNReal.inv_le_one]; exact hq
  have h_sum_le : 1/p + 1/q ≤ 2 := by
    calc 1/p + 1/q ≤ 1 + 1 := add_le_add hp_inv hq_inv
      _ = 2 := by norm_num
  rw [hpqr] at h_sum_le
  -- 1 + 1/r ≤ 2 → 1/r ≤ 1 → r ≥ 1
  have h_inv_r : 1/r ≤ 1 := by
    have h2 : (2 : ℝ≥0∞) = 1 + 1 := by norm_num
    rw [h2] at h_sum_le
    exact (ENNReal.add_le_add_iff_left (by simp : (1 : ℝ≥0∞) ≠ ⊤)).mp h_sum_le
  rw [one_div, ENNReal.inv_le_one] at h_inv_r
  exact h_inv_r

/-- Auxiliary lemma showing r / (p * r) = 1/p in ENNReal -/
lemma ennreal_div_mul_right {p r : ℝ≥0∞}
    (hp_pos : p ≠ 0) (hp_ne_top : p ≠ ⊤) (hr_pos : r ≠ 0) (hr_ne_top : r ≠ ⊤) :
    r / (p * r) = 1 / p := by
  rw [one_div, ENNReal.div_eq_inv_mul]
  rw [ENNReal.mul_inv (Or.inl hp_pos) (Or.inl hp_ne_top)]
  rw [mul_assoc, ENNReal.inv_mul_cancel hr_pos hr_ne_top, mul_one]

/-- Auxiliary lemma showing p / (p * r) = 1/r in ENNReal -/
lemma ennreal_div_mul_left {p r : ℝ≥0∞}
    (hp_pos : p ≠ 0) (hp_ne_top : p ≠ ⊤) (hr_pos : r ≠ 0) (hr_ne_top : r ≠ ⊤) :
    p / (p * r) = 1 / r := by
  rw [mul_comm p r]
  exact ennreal_div_mul_right hr_pos hr_ne_top hp_pos hp_ne_top

/-- Auxiliary lemma showing (r - p) / (p * r) = 1/p - 1/r in ENNReal (when p ≤ r) -/
lemma ennreal_sub_div_mul {p r : ℝ≥0∞}
    (hp_pos : p ≠ 0) (hp_ne_top : p ≠ ⊤) (hr_pos : r ≠ 0) (hr_ne_top : r ≠ ⊤) :
    (r - p) / (p * r) = 1/p - 1/r := by
  have hpr_pos : p * r ≠ 0 := mul_ne_zero hp_pos hr_pos
  have h1 : r / (p * r) = 1 / p := ennreal_div_mul_right hp_pos hp_ne_top hr_pos hr_ne_top
  have h2 : p / (p * r) = 1 / r := ennreal_div_mul_left hp_pos hp_ne_top hr_pos hr_ne_top
  have h_sub : (r - p) / (p * r) = r / (p * r) - p / (p * r) := by
    apply ENNReal.sub_div
    intro _ _
    exact hpr_pos
  rw [h_sub, h1, h2]

/-- Derive three-function Hölder exponent condition from Young exponent condition
    Note: p, q, r ≠ ⊤ is required (because ⊤/⊤ = 0 in ENNReal) -/
lemma young_exponent_to_three_holder
    {p q r : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hp_ne_top : p ≠ ⊤) (hq_ne_top : q ≠ ⊤) (hr_ne_top : r ≠ ⊤)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r) :
    1/r + (r-p)/(p*r) + (r-q)/(q*r) = 1 := by
  -- p, q, r are positive and finite
  have hp_pos : p ≠ 0 := (one_pos.trans_le hp).ne'
  have hq_pos : q ≠ 0 := (one_pos.trans_le hq).ne'
  have hr_pos : r ≠ 0 := (one_pos.trans_le hr).ne'
  -- From the Young exponent condition we know p ≤ r and q ≤ r
  have h_p_le_r : p ≤ r := young_exponent_p_le_r hq hpqr
  have h_q_le_r : q ≤ r := young_exponent_q_le_r hp hpqr
  -- Rewrite the auxiliary exponents (r-p)/(p*r) and (r-q)/(q*r)
  -- using the identities (r-p)/(p*r) = 1/p - 1/r and (r-q)/(q*r) = 1/q - 1/r.
  have h1 : (r - p) / (p * r) = 1/p - 1/r :=
    ennreal_sub_div_mul hp_pos hp_ne_top hr_pos hr_ne_top
  have h2 : (r - q) / (q * r) = 1/q - 1/r :=
    ennreal_sub_div_mul hq_pos hq_ne_top hr_pos hr_ne_top
  -- The fractions 1/p, 1/q, 1/r are all finite.
  have h_one_div_p_ne_top : 1/p ≠ ⊤ := ENNReal.div_ne_top ENNReal.one_ne_top hp_pos
  have h_one_div_q_ne_top : 1/q ≠ ⊤ := ENNReal.div_ne_top ENNReal.one_ne_top hq_pos
  have h_one_div_r_ne_top : 1/r ≠ ⊤ := ENNReal.div_ne_top ENNReal.one_ne_top hr_pos
  -- From p ≤ r and q ≤ r we also have 1/r ≤ 1/p and 1/r ≤ 1/q.
  have h_one_div_r_le_one_div_p : 1/r ≤ 1/p := by
    rw [one_div, one_div, ENNReal.inv_le_inv]
    exact h_p_le_r
  have h_one_div_r_le_one_div_q : 1/r ≤ 1/q := by
    rw [one_div, one_div, ENNReal.inv_le_inv]
    exact h_q_le_r
  -- First simplify 1/r + (1/p - 1/r).
  have step1 : 1/r + (1/p - 1/r) = 1/p :=
    add_tsub_cancel_of_le h_one_div_r_le_one_div_p
  -- Next, rewrite 1/p + (1/q - 1/r) as 1/p + 1/q - 1/r using cancellability
  -- of addition by the finite element 1/r.
  have hc : AddLECancellable (1/r : ℝ≥0∞) :=
    ENNReal.cancel_of_ne h_one_div_r_ne_top
  have step2' : 1/p + 1/q - 1/r = 1/p + (1/q - 1/r) :=
    hc.add_tsub_assoc_of_le h_one_div_r_le_one_div_q (1/p)
  have step2 : 1/p + (1/q - 1/r) = 1/p + 1/q - 1/r :=
    step2'.symm
  -- Finally, use the Young exponent condition to evaluate 1/p + 1/q - 1/r.
  have step3 : 1/p + 1/q - 1/r = 1 := by
    -- From 1/p + 1/q = 1 + 1/r and finiteness of 1/r.
    have := ENNReal.sub_eq_of_eq_add (a := 1/p + 1/q)
        (b := 1/r) (c := (1 : ℝ≥0∞)) h_one_div_r_ne_top hpqr
    simpa using this
  -- Intermediate simplification of the left-hand side.
  have step0 :
      1/r + (r-p)/(p*r) + (r-q)/(q*r) =
        1/r + (1/p - 1/r) + (1/q - 1/r) := by
    simp [h1, h2]
  have step_mid :
      1/r + (1/p - 1/r) + (1/q - 1/r) =
        1/p + (1/q - 1/r) := by
    -- add (1/q - 1/r) to both sides of step1
    have h := congrArg (fun x : ℝ≥0∞ => x + (1/q - 1/r)) step1
    -- rewrite using associativity and commutativity of addition
    simpa [add_comm, add_left_comm, add_assoc] using h
  -- Put everything together.
  calc
    1/r + (r-p)/(p*r) + (r-q)/(q*r)
        = 1/r + (1/p - 1/r) + (1/q - 1/r) := step0
    _   = 1/p + (1/q - 1/r) := step_mid
    _   = 1/p + 1/q - 1/r := step2
    _   = 1 := step3

/-- Verify that exponents used in decomposition are non-negative (can be 0 at boundary) -/
lemma decomposition_exponents_pos
    {p q r : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr_ne_top : r ≠ ⊤) :
    0 < p/r ∧ 0 < q/r ∧ 0 ≤ 1 - p/r ∧ 0 ≤ 1 - q/r := by
  -- Positivity of p, q, r
  have hp_pos : p ≠ 0 := (one_pos.trans_le hp).ne'
  have hq_pos : q ≠ 0 := (one_pos.trans_le hq).ne'
  -- 0 < p/r and 0 < q/r since numerators are positive and denominator is finite
  have hp_div_pos : 0 < p / r := ENNReal.div_pos hp_pos hr_ne_top
  have hq_div_pos : 0 < q / r := ENNReal.div_pos hq_pos hr_ne_top
  -- 1 - p/r and 1 - q/r are automatically ≥ 0 in ℝ≥0∞
  have h_one_sub_p : (0 : ℝ≥0∞) ≤ 1 - p / r := zero_le _
  have h_one_sub_q : (0 : ℝ≥0∞) ≤ 1 - q / r := zero_le _
  exact ⟨hp_div_pos, hq_div_pos, h_one_sub_p, h_one_sub_q⟩

/-- For a nonzero constant `c`, the integral of `c` over the whole space is infinite
when the dimension `n` is positive. -/
lemma lintegral_const_top_of_volume_univ (c : ℝ≥0∞) (hc : c ≠ 0) (hn : 0 < n) :
    ∫⁻ (_ : Fin n → ℝ), c ∂(volume) = ⊤ := by
  have h_vol : volume (Set.univ : Set (Fin n → ℝ)) = (∞ : ℝ≥0∞) := by
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    simp
  -- Replace the volume of the whole space by `∞` and use `ENNReal.mul_top`.
  simp [h_vol, ENNReal.mul_top, hc]

/-- Characterization of vanishing `lintegral` in terms of a.e. vanishing (ℝ≥0∞-valued). -/
lemma lintegral_eq_zero_iff_ae_eq_zero
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    (∫⁻ x, f x ∂μ = 0) ↔ f =ᵐ[μ] 0 := by
  exact MeasureTheory.lintegral_eq_zero_iff' hf

/-- If the product `f * g` has zero integral and `g` is strictly positive a.e.,
then `f` vanishes a.e. (ℝ≥0∞-valued version). -/
lemma ae_eq_zero_of_lintegral_mul_eq_zero_left
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ≥0∞}
    (hg_pos : ∀ᵐ x ∂μ, 0 < g x)
    (hf_meas : AEMeasurable f μ) (hg_meas : AEMeasurable g μ)
    (h_int : ∫⁻ x, f x * g x ∂μ = 0) :
    f =ᵐ[μ] 0 := by
  -- First show that `f * g` vanishes a.e. from the vanishing of its integral.
  have h_fg_meas : AEMeasurable (fun x => f x * g x) μ := hf_meas.mul hg_meas
  have h_fg_zero : (fun x => f x * g x) =ᵐ[μ] 0 :=
    (lintegral_eq_zero_iff_ae_eq_zero (α := α) (μ := μ)
        (f := fun x => f x * g x) h_fg_meas).1 h_int
  -- Use the positivity of `g` to deduce that `f` itself vanishes a.e.
  refine (hg_pos.and h_fg_zero).mono ?_
  intro x hx
  rcases hx with ⟨hg_pos_x, hfg_zero_x⟩
  -- Pointwise lemma: if `0 < g x` and `f x * g x = 0`, then `f x = 0`.
  have hg_ne_zero : g x ≠ 0 := (ne_of_gt hg_pos_x)
  -- We split according to whether `g x` is infinite or finite.
  by_cases hxg_top : g x = ⊤
  · -- Case `g x = ∞`.
    -- Then `f x * ∞ = 0`, which forces `f x = 0`.
    have h' : f x * (∞ : ℝ≥0∞) = 0 := by simpa [hxg_top] using hfg_zero_x
    -- Analyze using `ENNReal.mul_top'`.
    by_contra hfx_ne
    have h_if : (if f x = 0 then 0 else (∞ : ℝ≥0∞)) = (0 : ℝ≥0∞) := by
      simpa [ENNReal.mul_top'] using h'
    have h_fx_zero : f x = 0 := by simpa [hfx_ne] using h_if
    exact hfx_ne h_fx_zero
  · -- Case `g x` is finite (not `∞`).
    have hg_ne_top : g x ≠ (∞ : ℝ≥0∞) := hxg_top
    -- Multiply the equality `f x * g x = 0` by `(g x)⁻¹` on the right.
    have h' : f x * g x = 0 := hfg_zero_x
    have h_mul := congrArg (fun y => y * (g x)⁻¹) h'
    -- Simplify using associativity and `mul_inv_cancel`.
    have : f x = 0 := by
      simpa [mul_assoc, ENNReal.mul_inv_cancel hg_ne_zero hg_ne_top] using h_mul
    exact this

/-- Symmetric version of `ae_eq_zero_of_lintegral_mul_eq_zero_left`. -/
lemma ae_eq_zero_of_lintegral_mul_eq_zero_right
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ≥0∞}
    (hf_pos : ∀ᵐ x ∂μ, 0 < f x)
    (hf_meas : AEMeasurable f μ) (hg_meas : AEMeasurable g μ)
    (h_int : ∫⁻ x, f x * g x ∂μ = 0) :
    g =ᵐ[μ] 0 := by
  -- Apply the left version with the roles of `f` and `g` swapped.
  have h_int' : ∫⁻ x, g x * f x ∂μ = 0 := by
    simpa [mul_comm] using h_int
  simpa [mul_comm] using
    (ae_eq_zero_of_lintegral_mul_eq_zero_left
      (μ := μ) (f := g) (g := f) hf_pos hg_meas hf_meas h_int')

lemma eLpNorm_translate_right
    {G : Type*} [AddCommGroup G] [MeasurableSpace G] [TopologicalSpace G]
    [MeasurableAdd₂ G]
    {μ : Measure G} [μ.IsAddHaarMeasure]
    (f : G → ℂ) (p : ℝ≥0∞) (a : G)
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm (fun x => f (x - a)) p μ = eLpNorm f p μ := by
  -- Use the general lemma `eLpNorm_comp_measurePreserving` with the translation map.
  have hmp : MeasurePreserving (fun x : G => x - a) μ μ := by
    -- `fun x => x - a` is right addition by `-a`.
    simpa [sub_eq_add_neg] using
      measurePreserving_add_right (μ := μ) (-a)
  -- Apply the composition lemma.
  simpa [Function.comp, sub_eq_add_neg] using
    (MeasureTheory.eLpNorm_comp_measurePreserving (μ := μ) (ν := μ)
      (g := f) (p := p) hf hmp)

lemma convolution_integrand_decomposition
    (f g : (Fin n → ℝ) → ℂ)
    (p q r : ℝ≥0∞)
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hp_ne_top : p ≠ ⊤) (hq_ne_top : q ≠ ⊤) (hr_ne_top : r ≠ ⊤)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    (x y : Fin n → ℝ) :
    ‖f y‖ * ‖g (x - y)‖ =
      (‖f y‖^(p/r).toReal * ‖g (x - y)‖^(q/r).toReal) *
      ‖f y‖^(1 - p/r).toReal *
      ‖g (x - y)‖^(1 - q/r).toReal := by
  -- Notation for the two nonnegative numbers we decompose.
  set a : ℝ := ‖f y‖ with ha_def
  set b : ℝ := ‖g (x - y)‖ with hb_def
  have ha_nonneg : 0 ≤ a := by simp [ha_def]
  have hb_nonneg : 0 ≤ b := by simp [hb_def]
  -- Positivity of p, q, r and finiteness of 1/p, 1/q.
  have hp_pos' : 0 < p := one_pos.trans_le hp
  have hq_pos' : 0 < q := one_pos.trans_le hq
  have hp_pos : p ≠ 0 := hp_pos'.ne'
  have hq_pos : q ≠ 0 := hq_pos'.ne'
  have h_one_div_p_ne_top : 1/p ≠ ⊤ :=
    ENNReal.div_ne_top ENNReal.one_ne_top hp_pos
  have h_one_div_q_ne_top : 1/q ≠ ⊤ :=
    ENNReal.div_ne_top ENNReal.one_ne_top hq_pos
  -- Show that r is positive: otherwise 1/p + 1/q would be infinite.
  have hr_ne_zero : r ≠ 0 := by
    by_contra hr0
    have h1 : (1 : ℝ≥0∞) / r = ⊤ := by simp [hr0]
    have h2 : 1 + (1 : ℝ≥0∞) / r = ⊤ := by simp [h1]
    have h3 : 1/p + 1/q = ⊤ := by
      calc 1/p + 1/q = 1 + 1/r := hpqr
        _ = ⊤ := h2
    have h_fin : 1/p + 1/q ≠ (⊤ : ℝ≥0∞) :=
      ENNReal.add_ne_top.mpr ⟨h_one_div_p_ne_top, h_one_div_q_ne_top⟩
    exact h_fin h3
  -- From the Young exponent condition we know p ≤ r and q ≤ r.
  have h_p_le_r : p ≤ r := young_exponent_p_le_r hq hpqr
  have h_q_le_r : q ≤ r := young_exponent_q_le_r hp hpqr
  -- Hence p/r ≤ 1 and q/r ≤ 1.
  have hp_div_le_one : p / r ≤ 1 := by
    have := (ENNReal.div_le_iff_le_mul (a := p) (b := r) (c := 1)
        (hb0 := Or.inl hr_ne_zero) (hbt := Or.inl hr_ne_top))
    -- `this` is an iff; use the → direction.
    exact this.mpr (by simpa [one_mul] using h_p_le_r)
  have hq_div_le_one : q / r ≤ 1 := by
    have := (ENNReal.div_le_iff_le_mul (a := q) (b := r) (c := 1)
        (hb0 := Or.inl hr_ne_zero) (hbt := Or.inl hr_ne_top))
    exact this.mpr (by simpa [one_mul] using h_q_le_r)
  -- In ℝ≥0∞ we have p/r + (1 - p/r) = 1 and similarly for q.
  have h_p_decomp : p / r + (1 - p / r) = 1 :=
    add_tsub_cancel_of_le hp_div_le_one
  have h_q_decomp : q / r + (1 - q / r) = 1 :=
    add_tsub_cancel_of_le hq_div_le_one
  -- The fractions p/r, q/r, 1 - p/r, 1 - q/r are all finite.
  have hp_div_ne_top : p / r ≠ ⊤ :=
    ENNReal.div_ne_top hp_ne_top hr_ne_zero
  have hq_div_ne_top : q / r ≠ ⊤ :=
    ENNReal.div_ne_top hq_ne_top hr_ne_zero
  have h_one_sub_p_ne_top : 1 - p / r ≠ ⊤ := by
    -- It is bounded by 1.
    have : 1 - p / r ≤ (1 : ℝ≥0∞) := by
      exact tsub_le_self
    exact ne_of_lt (lt_of_le_of_lt this (by simp))
  have h_one_sub_q_ne_top : 1 - q / r ≠ ⊤ := by
    have : 1 - q / r ≤ (1 : ℝ≥0∞) := by
      exact tsub_le_self
    exact ne_of_lt (lt_of_le_of_lt this (by simp))
  -- Convert the ENNReal equalities to equalities of real exponents.
  have h_sum_p :
      (p/r).toReal + (1 - p/r).toReal = 1 := by
    have h := (ENNReal.toReal_add (a := p / r) (b := 1 - p / r)
        hp_div_ne_top h_one_sub_p_ne_top).symm
    -- h : (p/r).toReal + (1 - p/r).toReal = (p/r + (1 - p/r)).toReal
    simpa [h_p_decomp, ENNReal.toReal_one] using h
  have h_sum_q :
      (q/r).toReal + (1 - q/r).toReal = 1 := by
    have h := (ENNReal.toReal_add (a := q / r) (b := 1 - q / r)
        hq_div_ne_top h_one_sub_q_ne_top).symm
    simpa [h_q_decomp, ENNReal.toReal_one] using h
  -- Now work purely in ℝ with the nonnegative numbers `a` and `b`.
  -- Convert (p/r).toReal to p.toReal / r.toReal
  have h_p_div_toReal : (p/r).toReal = p.toReal / r.toReal :=
    ENNReal.toReal_div p r
  have h_q_div_toReal : (q/r).toReal = q.toReal / r.toReal :=
    ENNReal.toReal_div q r
  have h_a :
      a ^ (p/r).toReal * a ^ (1 - p/r).toReal = a := by
    have h_rpow :=
      Real.rpow_add_of_nonneg ha_nonneg (ENNReal.toReal_nonneg (a := p/r))
        (ENNReal.toReal_nonneg (a := 1 - p/r))
    -- h_rpow : a ^ ((p/r).toReal + (1 - p/r).toReal)
    --            = a ^ (p/r).toReal * a ^ (1 - p/r).toReal
    have : a ^ (p/r).toReal * a ^ (1 - p/r).toReal =
        a ^ ((p/r).toReal + (1 - p/r).toReal) := by
      simpa [mul_comm] using h_rpow.symm
    -- Replace the exponent by 1.
    simp only [this, h_sum_p, Real.rpow_one]
  have h_b :
      b ^ (q/r).toReal * b ^ (1 - q/r).toReal = b := by
    have h_rpow :=
      Real.rpow_add_of_nonneg hb_nonneg (ENNReal.toReal_nonneg (a := q/r))
        (ENNReal.toReal_nonneg (a := 1 - q/r))
    have : b ^ (q/r).toReal * b ^ (1 - q/r).toReal =
        b ^ ((q/r).toReal + (1 - q/r).toReal) := by
      simpa [mul_comm] using h_rpow.symm
    simp only [this, h_sum_q, Real.rpow_one]
  -- Put everything together.
  -- First rewrite both sides in terms of `a` and `b`.
  have hab : ‖f y‖ * ‖g (x - y)‖ = a * b := by
    simp [ha_def, hb_def]
  -- Rewrite `h_a` and `h_b` in terms of `p.toReal / r.toReal`.
  have h_a' : a ^ (p.toReal / r.toReal) * a ^ (1 - p/r).toReal = a := by
    rw [← h_p_div_toReal]; exact h_a
  have h_b' : b ^ (q.toReal / r.toReal) * b ^ (1 - q/r).toReal = b := by
    rw [← h_q_div_toReal]; exact h_b
  -- Rewrite the right-hand side.
  have hrhs : a * b =
      (a^(p.toReal / r.toReal) * b^(q.toReal / r.toReal)) *
      a^(1 - p/r).toReal * b^(1 - q/r).toReal := by
    -- Rearrange the factors and use the identities `h_a'` and `h_b'`.
    calc
      a * b = (a ^ (p.toReal / r.toReal) * a ^ (1 - p/r).toReal) *
              (b ^ (q.toReal / r.toReal) * b ^ (1 - q/r).toReal) := by
                simp [h_a', h_b']
      _ = (a^(p.toReal / r.toReal) * b^(q.toReal / r.toReal)) *
          a^(1 - p/r).toReal * b^(1 - q/r).toReal := by
                ring_nf
  -- Conclude, rewriting back in terms of norms.
  simp only [ha_def, hb_def] at hrhs
  rw [h_p_div_toReal, h_q_div_toReal]
  exact hrhs

end Newton
