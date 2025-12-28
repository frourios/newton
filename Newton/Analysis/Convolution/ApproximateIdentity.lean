import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Newton.Analysis.Convolution.Basic
import Newton.MeasureTheory.Integral.Holder
import Newton.MeasureTheory.Function.LpSpace.ContinuousDense

/-!
# Approximate Identity and Mollifier Convergence

This file establishes the convergence properties of convolution with
approximate identities (mollifiers), which are crucial for the Schwartz
density theorem.
-/

open MeasureTheory Complex NNReal SchwartzMap
open scoped ENNReal ContDiff Topology Pointwise

namespace Newton

variable {n : ℕ}

/--
**Approximate identity (mollifier) structure.**

A function ψ is a mollifier if it is smooth, compactly supported,
normalized, and non-negative.
-/
structure IsApproximateIdentity (ψ : (Fin n → ℝ) → ℝ) : Prop where
  smooth : ContDiff ℝ (∞ : WithTop ℕ∞) ψ
  compact_support : HasCompactSupport ψ
  normalized : ∫ x, ψ x = 1
  nonneg : ∀ x, 0 ≤ ψ x
  support_subset : tsupport ψ ⊆ Metric.closedBall (0 : Fin n → ℝ) 1

/--
**Scaled mollifier ψ_η.**

ψ_η(x) = η^(-n) ψ(x/η)
-/
noncomputable def scaledMollifier (ψ : (Fin n → ℝ) → ℝ) (η : ℝ) : (Fin n → ℝ) → ℝ :=
  fun x => η^(-(n : ℝ)) * ψ (fun i => x i / η)

section ScaledMollifierFacts

variable {ψ : (Fin n → ℝ) → ℝ}

/-- Nonnegativity of the scaled mollifier when `ψ ≥ 0` and `η ≥ 0`. -/
lemma scaledMollifier_nonneg
    (hψ_nonneg : ∀ x, 0 ≤ ψ x) {η : ℝ} (hη_nonneg : 0 ≤ η) :
    ∀ x, 0 ≤ scaledMollifier ψ η x := by
  intro x
  have h_const_nonneg : 0 ≤ η ^ (-(n : ℝ)) :=
    Real.rpow_nonneg hη_nonneg _
  have h_inner_nonneg : 0 ≤ ψ (fun i => x i / η) := hψ_nonneg _
  simpa [scaledMollifier] using mul_nonneg h_const_nonneg h_inner_nonneg

/-- Compact support of the scaled mollifier under `η > 0`. -/
lemma hasCompactSupport_scaledMollifier
    (hψ : HasCompactSupport ψ) {η : ℝ} (hη_pos : 0 < η) :
    HasCompactSupport (scaledMollifier ψ η) := by
  -- Define the scaling maps s and its inverse image description on sets.
  set s : (Fin n → ℝ) → (Fin n → ℝ) := fun x => fun i => x i / η with hs_def
  have hs_eq_smul : s = fun x : (Fin n → ℝ) => (η⁻¹ : ℝ) • x := by
    funext x i; simp [s, hs_def, div_eq_mul_inv, mul_comm]
  have hs_cont : Continuous s := by
    simpa [hs_eq_smul] using (continuous_const_smul (η⁻¹ : ℝ))
  -- Support inclusion: support(scaledMollifier) ⊆ preimage of tsupport ψ under s.
  have h_support_subset :
      Function.support (scaledMollifier ψ η)
        ⊆ s ⁻¹' tsupport ψ := by
    intro x hx
    -- If the scaled mollifier is nonzero at x, then ψ (s x) ≠ 0.
    have hx_ne : scaledMollifier ψ η x ≠ 0 := hx
    have hψ_ne : ψ (s x) ≠ 0 := by
      -- If ψ (s x) = 0 then the product is 0, contradiction.
      intro hzero
      have : scaledMollifier ψ η x = 0 := by
        simp [scaledMollifier, hzero, s, hs_def]
      exact hx_ne this
    -- Hence s x ∈ support ψ ⊆ tsupport ψ.
    have : s x ∈ Function.support ψ := by simpa [Function.support] using hψ_ne
    have : s x ∈ tsupport ψ := subset_tsupport _ this
    simpa [Set.mem_preimage]
      using this
  -- `tsupport` is the closure of `support`; close the inclusion using closedness.
  have h_tsupport_subset :
      tsupport (scaledMollifier ψ η) ⊆ s ⁻¹' tsupport ψ := by
    -- Preimage of a closed set under a continuous map is closed.
    have h_closed : IsClosed (s ⁻¹' tsupport ψ) :=
      (isClosed_tsupport ψ).preimage hs_cont
    -- Use the minimality of closure with respect to closed supersets.
    simpa [tsupport, Function.support]
      using closure_minimal h_support_subset h_closed
  -- Identify the preimage as the image of tsupport ψ under scaling by η.
  have h_preimage_eq :
      s ⁻¹' tsupport ψ
        = (fun z : (Fin n → ℝ) => η • z) '' tsupport ψ := by
    -- Preimage under s = image under its inverse (scaling by η).
    ext x; constructor
    · intro hx
      refine ⟨s x, ?_, ?_⟩
      · simpa [Set.mem_preimage] using hx
      · have hη_ne : (η : ℝ) ≠ 0 := ne_of_gt hη_pos
        simp [hs_eq_smul, smul_smul, hη_ne]
    · intro hx
      rcases hx with ⟨z, hz, rfl⟩
      -- s (η • z) = z ∈ tsupport ψ
      have hη_ne : (η : ℝ) ≠ 0 := ne_of_gt hη_pos
      simpa [hs_eq_smul, smul_smul, hη_ne] using hz
  -- The right-hand side is compact as an image of a compact set under a continuous map.
  have h_image_compact :
      IsCompact ((fun z : (Fin n → ℝ) => η • z) '' tsupport ψ) := by
    have h_compact_tsupport : IsCompact (tsupport ψ) := hψ
    have h_cont_scale : Continuous fun z : (Fin n → ℝ) => η • z :=
      continuous_const_smul η
    exact h_compact_tsupport.image h_cont_scale
  have h_compact : IsCompact (tsupport (scaledMollifier ψ η)) := by
    have : tsupport (scaledMollifier ψ η)
        ⊆ (fun z : (Fin n → ℝ) => η • z) '' tsupport ψ := by
      simpa [h_preimage_eq] using h_tsupport_subset
    exact IsCompact.of_isClosed_subset h_image_compact (isClosed_tsupport _) this
  simpa [HasCompactSupport] using h_compact

/-- T-support inclusion for the scaled mollifier: it is contained in the ball of radius `η`. -/
lemma tsupport_scaledMollifier_subset
    (hψ : IsApproximateIdentity ψ) {η : ℝ} (hη_pos : 0 < η) :
    tsupport (scaledMollifier ψ η)
      ⊆ Metric.closedBall (0 : Fin n → ℝ) η := by
  -- Scaling map s(x) = x / η
  set s : (Fin n → ℝ) → (Fin n → ℝ) := fun x => fun i => x i / η with hs_def
  have hs_eq_smul : s = fun x : (Fin n → ℝ) => (η⁻¹ : ℝ) • x := by
    funext x i; simp [s, hs_def, div_eq_mul_inv, mul_comm]
  have hs_cont : Continuous s := by
    simpa [hs_eq_smul] using (continuous_const_smul (η⁻¹ : ℝ))
  -- support(scaled) ⊆ preimage of tsupport ψ under s, hence tsupport(scaled) ⊆ that preimage
  have h_support_subset :
      Function.support (scaledMollifier ψ η) ⊆ s ⁻¹' tsupport ψ := by
    intro x hx
    have hx_ne : scaledMollifier ψ η x ≠ 0 := hx
    have hψ_ne : ψ (s x) ≠ 0 := by
      intro hzero
      have : scaledMollifier ψ η x = 0 := by
        simp [scaledMollifier, hzero, s, hs_def]
      exact hx_ne this
    have : s x ∈ Function.support ψ := by simpa [Function.support] using hψ_ne
    have : s x ∈ tsupport ψ := subset_tsupport _ this
    simpa [Set.mem_preimage] using this
  have h_tsupport_subset :
      tsupport (scaledMollifier ψ η) ⊆ s ⁻¹' tsupport ψ := by
    have h_closed : IsClosed (s ⁻¹' tsupport ψ) := (isClosed_tsupport _).preimage hs_cont
    simpa [tsupport, Function.support] using closure_minimal h_support_subset h_closed
  -- Push forward the inclusion along tsupport ψ ⊆ closedBall(0,1)
  have h_preimage_subset :
      s ⁻¹' tsupport ψ ⊆ s ⁻¹' Metric.closedBall (0 : Fin n → ℝ) 1 := by
    exact Set.preimage_mono hψ.support_subset
  -- Preimage of the unit ball under s equals the ball of radius η.
  have h_preimage_ball :
      s ⁻¹' Metric.closedBall (0 : Fin n → ℝ) 1
        ⊆ Metric.closedBall (0 : Fin n → ℝ) η := by
    intro x hx
    have hx' : ‖s x‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hnorm_smul : ‖(η⁻¹ : ℝ)‖ = η⁻¹ := by
      have : 0 < (η : ℝ) := hη_pos
      simp [Real.norm_eq_abs, abs_inv, abs_of_pos this]
    have hx'' : (η⁻¹ : ℝ) * ‖x‖ ≤ 1 := by
      simpa [hs_eq_smul, norm_smul, hnorm_smul] using hx'
    have hx_le : ‖x‖ ≤ η := by
      have h_nonneg : 0 ≤ (η : ℝ) := le_of_lt hη_pos
      have h := mul_le_mul_of_nonneg_left hx'' h_nonneg
      -- Rewrite the left-hand side exactly to ‖x‖ using η ≠ 0.
      have hη_ne : (η : ℝ) ≠ 0 := ne_of_gt hη_pos
      have h_left_eq : η * (η⁻¹ * ‖x‖) = ‖x‖ := by
        rw [← mul_assoc, mul_inv_cancel₀ hη_ne, one_mul]
      -- Conclude ‖x‖ ≤ η.
      simpa [h_left_eq, mul_one] using h
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx_le
  exact (h_tsupport_subset.trans h_preimage_subset).trans h_preimage_ball

/-- The total mass of the scaled mollifier is 1. -/
lemma integral_scaledMollifier_eq_one
    (hψ : IsApproximateIdentity ψ) {η : ℝ} (hη_pos : 0 < η) :
    ∫ x, scaledMollifier ψ η x = (1 : ℝ) := by
  -- Scaling map g(x) = (1/η) • x
  set g : (Fin n → ℝ) → (Fin n → ℝ) := fun x => (1 / η) • x with hg
  have hη_ne_zero : (η : ℝ) ≠ 0 := ne_of_gt hη_pos
  -- ψ is integrable as it is continuous with compact support
  have hψ_int : Integrable ψ volume :=
    (hψ.smooth.continuous.integrable_of_hasCompactSupport hψ.compact_support)

  -- Describe the pushforward of volume under the linear map g
  have h_map_scale :
      Measure.map g (volume : Measure (Fin n → ℝ))
        = ENNReal.ofReal ((|η|) ^ n) • (volume : Measure (Fin n → ℝ)) := by
    have h_det_ne :
        LinearMap.det ((η⁻¹ : ℝ) •
            (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) ≠ 0 := by
      have hdet :
          LinearMap.det ((η⁻¹ : ℝ) •
              (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
            = (η⁻¹ : ℝ) ^ (Module.finrank ℝ (Fin n → ℝ)) := by
        simp
      have hpow_ne : (η⁻¹ : ℝ) ^ (Module.finrank ℝ (Fin n → ℝ)) ≠ 0 :=
        pow_ne_zero _ (inv_ne_zero hη_ne_zero)
      simpa [hdet] using hpow_ne
    have hg_lin :
        (fun x : (Fin n → ℝ) =>
          (((η⁻¹ : ℝ) •
            (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) :
              (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) x)
          = g := by
      funext x; simp [g, hg, one_div]
    simpa [hg_lin]
      using
        Real.map_linearMap_volume_pi_eq_smul_volume_pi
          (f := ((η⁻¹ : ℝ) •
            (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))) h_det_ne

  -- Transfer integrability under the pushforward measure
  have hg_meas : Measurable g := by
    -- Use continuity of the linear map x ↦ (1/η) • x
    simpa [g, hg]
      using ((continuous_const_smul (1 / η : ℝ)).measurable)
  have hg_aemeas : AEMeasurable g volume := hg_meas.aemeasurable
  have hψ_int_map : Integrable ψ (Measure.map g volume) := by
    have hc_ne_top : ENNReal.ofReal ((|η|) ^ n) ≠ ∞ := by simp
    have hψ_memLp : MemLp ψ 1 volume :=
      (memLp_one_iff_integrable (μ := volume)).2 hψ_int
    have hψ_memLp_map : MemLp ψ 1 (Measure.map g volume) := by
      simpa [h_map_scale]
        using hψ_memLp.smul_measure hc_ne_top
    exact (memLp_one_iff_integrable (μ := Measure.map g volume)).1 hψ_memLp_map

  -- Evaluate ∫ ψ ∘ g via mapping and smul of measure
  have h_integral_comp :
      ∫ x, ψ (g x)
        = (ENNReal.ofReal ((|η|) ^ n)).toReal * ∫ y, ψ y := by
    have h_map :
        ∫ y, ψ y ∂(Measure.map g volume) = ∫ x, ψ (g x) ∂volume := by
      simpa using
        (MeasureTheory.integral_map (μ := volume)
          hg_aemeas (hψ_int_map.aestronglyMeasurable))
    have h_smul :
        ∫ y, ψ y ∂(Measure.map g volume)
          = (ENNReal.ofReal ((|η|) ^ n)).toReal * ∫ y, ψ y := by
      simp [h_map_scale, integral_smul_measure, mul_comm, mul_left_comm, mul_assoc]
    exact h_map.symm.trans h_smul

  -- Compute the determinant factor: for g = (1/η)•id, toReal equals η^n
  have h_det_toReal :
      (ENNReal.ofReal ((|η|) ^ n)).toReal = η ^ (n : ℝ) := by
    have h_pos : 0 < η := hη_pos
    have h_abs : |η| = η := by simp [abs_of_pos h_pos]
    -- Rewrite to ofReal/toReal and use nonnegativity of η^n
    have h_nonneg : 0 ≤ η ^ n := pow_nonneg (le_of_lt h_pos) _
    simp [h_abs, Real.rpow_natCast, h_nonneg]

  -- Now compute the integral of the scaled mollifier
  have h_mη_as_comp :
      (fun y => scaledMollifier ψ η y)
        = fun y => (η ^ (-(n : ℝ))) * ψ (g y) := by
    funext y
    have hg_apply : g y = (fun i => y i / η) := by
      funext i
      -- ((1/η) • y) i = (1/η) * y i = y i * η⁻¹ = y i / η
      simp [g, hg, one_div, div_eq_mul_inv, mul_comm]
    simp [scaledMollifier, hg_apply]

  calc
    ∫ x, scaledMollifier ψ η x
        = (η ^ (-(n : ℝ))) * ∫ x, ψ (g x) := by
          simp [h_mη_as_comp, integral_const_mul]
    _   = (η ^ (-(n : ℝ))) *
            ((ENNReal.ofReal ((|η|) ^ n)).toReal * ∫ y, ψ y) := by
          simp [h_integral_comp]
    _   = ((η ^ (-(n : ℝ))) * (η ^ (n : ℝ))) * ∫ y, ψ y := by
          simp [h_det_toReal, mul_comm, mul_left_comm, mul_assoc]
    _   = (1 : ℝ) * ∫ y, ψ y := by
      -- Simplify (η^(-n)) * (η^n) = 1, then multiply both sides by ∫ ψ
      have hpow_ne_zero : η ^ (n : ℝ) ≠ 0 := by
        have hpos : 0 < η ^ (n : ℝ) := Real.rpow_pos_of_pos hη_pos _
        exact ne_of_gt hpos
      have hEq : (η ^ (-(n : ℝ))) * η ^ (n : ℝ) = (1 : ℝ) := by
        have h' : (η ^ (n : ℝ))⁻¹ * η ^ (n : ℝ) = (1 : ℝ) :=
          inv_mul_cancel₀ hpow_ne_zero
        simpa [Real.rpow_neg (le_of_lt hη_pos)] using h'
      have := congrArg (fun t : ℝ => t * ∫ y, ψ y) hEq
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    _   = (1 : ℝ) := by simp [hψ.normalized]

end ScaledMollifierFacts

lemma core_indicator_eLpNorm_bound
    {p : ℝ≥0∞} {coreSet : Set (Fin n → ℝ)}
    (h_core_meas : MeasurableSet coreSet)
    {g : (Fin n → ℝ) → ℂ} {δ : ℝ}
    (h_bound :
      ∀ᵐ x ∂volume.restrict coreSet, ‖g x‖ ≤ δ) :
  eLpNorm (fun x => Set.indicator coreSet g x) p volume
    ≤ (volume coreSet) ^ (1 / p.toReal) * ENNReal.ofReal δ := by
  -- Move to the restricted measure on `coreSet` via the indicator equivalence.
  have h_indicator_eq :
      eLpNorm (fun x => Set.indicator coreSet g x) p volume
        = eLpNorm g p (volume.restrict coreSet) := by
    simpa using
      (eLpNorm_indicator_eq_eLpNorm_restrict
        (μ := volume) (p := p) (s := coreSet) (f := g) h_core_meas)
  -- Apply the general bound under an a.e. pointwise bound on the restricted measure.
  have h_le_restrict :
      eLpNorm g p (volume.restrict coreSet)
        ≤ (volume.restrict coreSet Set.univ) ^ (1 / p.toReal) * ENNReal.ofReal δ := by
    simpa using
      (eLpNorm_le_of_ae_bound (μ := volume.restrict coreSet) (p := p) (f := g) h_bound)
  -- Evaluate the total mass of the restricted measure on `univ`.
  have h_measure_univ : (volume.restrict coreSet) Set.univ = volume coreSet := by
    simp [Measure.restrict_apply, h_core_meas]
  simpa [h_indicator_eq, h_measure_univ] using h_le_restrict

/--
**Mollifier convergence for continuous functions.**

For f continuous with compact support and ψ an approximate identity:
  ‖f - f * ψ_η‖_∞ → 0 as η → 0
-/
theorem mollifier_converges_continuous
    (f : (Fin n → ℝ) → ℂ)
    (ψ : (Fin n → ℝ) → ℝ)
    (hf_cont : Continuous f)
    (hf_compact : HasCompactSupport f)
    (hψ : IsApproximateIdentity ψ) :
    ∀ ε > 0, ∃ δ > 0, ∀ η : ℝ, 0 < η → η < δ →
      ∀ x, ‖f x - ∫ y, f (x - y) * (scaledMollifier ψ η y)‖ < ε := by
  -- Use uniform continuity of a compactly supported continuous function.
  intro ε hε
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ :=
    (Metric.uniformContinuous_iff.mp
      (hf_compact.uniformContinuous_of_continuous hf_cont)) (ε / 2)
      (by linarith)
  have hδ₀' : ∀ x y, ‖x - y‖ < δ₀ → ‖f x - f y‖ < ε / 2 := by
    intro x y hxy
    have hxy' : dist x y < δ₀ := by simpa [dist_eq_norm] using hxy
    have hε' : dist (f x) (f y) < ε / 2 := hδ₀ hxy'
    simpa [dist_eq_norm] using hε'
  -- We will choose δ ≤ δ₀ so that ‖y‖ < δ ⇒ ‖f x - f (x - y)‖ < ε/2.
  refine ⟨δ₀, hδ₀_pos, ?_⟩
  intro η hη_pos hη_lt
  -- Abbreviations for the scaled mollifier and its scaling map.
  set mη : (Fin n → ℝ) → ℝ := fun y => scaledMollifier ψ η y with hmη
  set g : (Fin n → ℝ) → (Fin n → ℝ) := fun x => (1 / η) • x with hg
  have hη_ne_zero : (η : ℝ) ≠ 0 := ne_of_gt hη_pos

  -- Change of variables: compute ∫ mη = 1 using hψ.normalized.
  have hψ_int : Integrable ψ volume :=
    (hψ.smooth.continuous.integrable_of_hasCompactSupport hψ.compact_support)
  -- Describe map (1/η)•id on volume.
  have h_map_scale :
      Measure.map g (volume : Measure (Fin n → ℝ))
        = ENNReal.ofReal ((|η|) ^ n) • (volume : Measure (Fin n → ℝ)) := by
    have h_det_ne :
        LinearMap.det ((η⁻¹ : ℝ) •
            (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) ≠ 0 := by
      have hdet :
          LinearMap.det ((η⁻¹ : ℝ) •
              (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
            = (η⁻¹ : ℝ) ^ (Module.finrank ℝ (Fin n → ℝ)) := by
        simp
      have hpow_ne : (η⁻¹ : ℝ) ^ (Module.finrank ℝ (Fin n → ℝ)) ≠ 0 :=
        pow_ne_zero _ (inv_ne_zero hη_ne_zero)
      simpa [hdet] using hpow_ne
    have hg_lin :
        (fun x : (Fin n → ℝ) =>
          (((η⁻¹ : ℝ) •
            (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) :
              (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) x)
          = g := by
      funext x; simp [g, hg, one_div]
    simpa [hg_lin]
      using
        Real.map_linearMap_volume_pi_eq_smul_volume_pi
          (f := ((η⁻¹ : ℝ) •
            (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))) h_det_ne

  -- Evaluate ∫ ψ ∘ g by mapping along `g` and then using `integral_smul_measure`.
  have hg_meas : Measurable g := by
    -- g is linear, hence measurable
    simpa [g, hg]
      using ((continuous_const_smul (1 / η : ℝ)).measurable)
  have hg_aemeas : AEMeasurable g volume := hg_meas.aemeasurable
  have hψ_int_map : Integrable ψ (Measure.map g volume) := by
    -- Transfer integrability along the smul measure identity.
    have hc_ne_top : ENNReal.ofReal ((|η|) ^ n) ≠ ∞ := by simp
    have hψ_memLp : MemLp ψ 1 volume :=
      (memLp_one_iff_integrable (μ := volume)).2 hψ_int
    have hψ_memLp_map : MemLp ψ 1 (Measure.map g volume) := by
      simpa [h_map_scale]
        using hψ_memLp.smul_measure hc_ne_top
    exact (memLp_one_iff_integrable (μ := Measure.map g volume)).1 hψ_memLp_map

  have h_integral_comp :
      ∫ x, ψ (g x) =
        (ENNReal.ofReal ((|η|) ^ n)).toReal * ∫ y, ψ y := by
    -- integral over the pushforward = integral of the composition
    have h_map :
        ∫ y, ψ y ∂(Measure.map g volume) = ∫ x, ψ (g x) ∂volume := by
      simpa using
        (MeasureTheory.integral_map (μ := volume)
          hg_aemeas (hψ_int_map.aestronglyMeasurable))
    -- Evaluate integral with smul measure
    have h_smul :
        ∫ y, ψ y ∂(Measure.map g volume)
          = (ENNReal.ofReal ((|η|) ^ n)).toReal * ∫ y, ψ y := by
      simp [h_map_scale, integral_smul_measure, mul_comm, mul_left_comm, mul_assoc]
    exact h_map.symm.trans h_smul

  -- Compute the determinant factor: for g = (1/η)•id, toReal equals η^n.
  have h_det_toReal :
      (ENNReal.ofReal ((|η|) ^ n)).toReal = η ^ (n : ℝ) := by
    have h_pos : 0 < η := hη_pos
    have h_abs : |η| = η := by simp [abs_of_pos h_pos]
    have h_nonneg : 0 ≤ η ^ n := pow_nonneg (le_of_lt h_pos) _
    simp [h_abs, Real.rpow_natCast, h_nonneg]

  -- From the above, obtain ∫ mη = 1.
  have h_mη_integral_one : (∫ y, mη y) = (1 : ℝ) := by
    have h_eq : (∫ y, mη y)
        = (η ^ (-(n : ℝ))) * (∫ x, ψ (g x)) := by
      -- mη = η^{-n} · (ψ ∘ g)
      have : (fun y => mη y) = fun y => (η ^ (-(n : ℝ))) * ψ (g y) := by
        funext y
        have hg_apply : g y = (fun i => y i / η) := by
          funext i
          -- ((1/η) • y) i = (1/η) * y i = y i * η⁻¹ = y i / η
          simp [g, hg, one_div, div_eq_mul_inv, mul_comm]
        simp [mη, hmη, scaledMollifier, hg_apply]
      simp [this, integral_const_mul]
    have h_norm := hψ.normalized
    have h_intψ : ∫ y, ψ y = 1 := h_norm
    -- Expand h_eq and use h_integral_comp followed by h_det_toReal
    have : (∫ y, mη y)
        = (η ^ (-(n : ℝ))) * ((ENNReal.ofReal ((|η|) ^ n)).toReal * ∫ y, ψ y) := by
      simp [h_eq, h_integral_comp]
    -- Simplify (η^(-n)) * (η^n) = 1 and conclude using h_intψ
    have h_mul_one : (η ^ (-(n : ℝ))) * (η ^ (n : ℝ)) = (1 : ℝ) := by
      have h' : (η ^ (n : ℝ))⁻¹ * η ^ (n : ℝ) = (1 : ℝ) :=
        inv_mul_cancel₀ (by
          have hpos : 0 < η ^ (n : ℝ) := Real.rpow_pos_of_pos hη_pos _
          exact ne_of_gt hpos)
      simpa [Real.rpow_neg (le_of_lt hη_pos)] using h'
    -- Combine the equalities
    have : (∫ y, mη y)
        = ((η ^ (-(n : ℝ))) * (η ^ (n : ℝ))) * ∫ y, ψ y := by
      simpa [h_det_toReal, mul_comm, mul_left_comm, mul_assoc] using this
    -- Replace the scalar product with 1 * ∫ ψ using inv_mul_cancel₀ on η^n
    have h_pow_ne_zero_nat : η ^ n ≠ 0 := pow_ne_zero _ hη_ne_zero
    have : (∫ y, mη y) = (1 : ℝ) * ∫ y, ψ y := by
      calc ∫ y, mη y
          = (η ^ (-(n : ℝ))) * (η ^ (n : ℝ)) * ∫ y, ψ y := this
        _ = (η ^ (n : ℝ))⁻¹ * (η ^ (n : ℝ)) * ∫ y, ψ y := by
            rw [Real.rpow_neg (le_of_lt hη_pos)]
        _ = (η ^ n)⁻¹ * (η ^ n) * ∫ y, ψ y := by
            simp only [Real.rpow_natCast]
        _ = 1 * ∫ y, ψ y := by
            rw [inv_mul_cancel₀ h_pow_ne_zero_nat]
    simpa [h_intψ]

  -- Main estimate: bound the difference by ε using uniform continuity and support of mη.
  intro x
  -- Rewrite the difference using ∫ mη = 1 then apply norm-integral ≤ integral-norm
  have h_const_integral :
      (∫ y, (f x) * (mη y)) = f x := by
    rw [integral_const_mul]
    have : (∫ (a : Fin n → ℝ), ((mη a) : ℂ)) = ↑(∫ (y : Fin n → ℝ), mη y) :=
      integral_ofReal
    rw [this, h_mη_integral_one, ofReal_one, mul_one]
  -- Define complex-valued version of the mollifier
  let mηC : (Fin n → ℝ) → ℂ := fun y => (mη y : ℝ)
  have h_mηC_compact : HasCompactSupport mηC := by
    have h_mη_compact := hasCompactSupport_scaledMollifier hψ.compact_support hη_pos
    -- Upgrade real-valued compact support to complex-valued via eventual equality
    rw [hasCompactSupport_iff_eventuallyEq] at h_mη_compact ⊢
    exact h_mη_compact.mono (by
      intro y hy
      simp only [mηC]
      have : mη y = scaledMollifier ψ η y := rfl
      rw [this, hy]
      simp)

  -- Continuity facts for the integrand pieces
  have h_div_cont : Continuous (fun y : (Fin n → ℝ) => fun i => y i / η) := by
    have :
        (fun y : (Fin n → ℝ) => fun i => y i / η)
          = fun y : (Fin n → ℝ) => (η⁻¹ : ℝ) • y := by
      funext y i; simp [div_eq_mul_inv, mul_comm]
    simpa [this] using (continuous_const_smul (η⁻¹ : ℝ))
  have h_mη_cont : Continuous mη := by
    simpa [mη, hmη, scaledMollifier]
      using (continuous_const.mul (hψ.smooth.continuous.comp h_div_cont))
  have h_mηC_cont : Continuous mηC := by
    simpa [mηC] using (continuous_ofReal.comp h_mη_cont)
  have h_transl_cont : Continuous (fun y : (Fin n → ℝ) => f (x - y)) := by
    have h_sub : Continuous (fun y : (Fin n → ℝ) => x - y) :=
      continuous_const.sub continuous_id
    exact hf_cont.comp h_sub

  -- Integrability of the convolution integrand via compact support
  have h_prod_cont :
      Continuous (fun y : (Fin n → ℝ) => f (x - y) * mηC y) := by
    simpa [mηC, mul_comm, mul_left_comm, mul_assoc]
      using h_transl_cont.mul h_mηC_cont
  have h_prod_compact :
      HasCompactSupport (fun y : (Fin n → ℝ) => f (x - y) * mηC y) := by
    -- Product has compact support since mηC has compact support
    simpa [mηC, mul_comm, mul_left_comm, mul_assoc]
      using
        (HasCompactSupport.mul_right
          (f := mηC) (f' := fun y : (Fin n → ℝ) => f (x - y)) h_mηC_compact)
  have h_prod_integrable :
      Integrable (fun y : (Fin n → ℝ) => f (x - y) * mηC y) volume :=
    h_prod_cont.integrable_of_hasCompactSupport h_prod_compact

  -- Also record integrability of the constant×mη term
  have h_const_mul_integrable :
      Integrable (fun y : (Fin n → ℝ) => (f x) * mηC y) volume := by
    -- (f x) • mηC is integrable since mηC has compact support
    have h_cont : Continuous (fun y : (Fin n → ℝ) => (f x) * mηC y) :=
      (continuous_const.mul h_mηC_cont)
    have h_compact :
        HasCompactSupport (fun y : (Fin n → ℝ) => (f x) * mηC y) := by
      simpa [mηC, mul_comm, mul_left_comm, mul_assoc]
        using
          (HasCompactSupport.mul_right
            (f := mηC) (f' := fun _y : (Fin n → ℝ) => (f x)) h_mηC_compact)
    exact h_cont.integrable_of_hasCompactSupport h_compact

  -- Convert the difference to a single integral and bound it
  have h_diff_eq_integral :
      f x - ∫ y, f (x - y) * (mη y) =
        ∫ y, ((f x) * (mηC y) - (f (x - y) * mηC y)) := by
    -- Use h_const_integral and integral_sub
    have h_sub :=
      integral_sub h_const_mul_integrable h_prod_integrable
    -- Rearrange to obtain the desired equality
    simpa [mηC, h_const_integral, sub_eq_add_neg]
      using h_sub.symm

  have h_to_single :
      ∫ y, ((f x) * (mηC y) - (f (x - y) * mηC y))
        = ∫ y, ((f x - f (x - y)) * mηC y) := by
    refine integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro y; ring

  have h_nonneg_mη : ∀ y, 0 ≤ mη y :=
    scaledMollifier_nonneg hψ.nonneg (le_of_lt hη_pos)

  -- Pointwise bound: ‖(f x - f (x - y)) * mηC y‖ ≤ (ε/2) * mη y
  have h_pointwise_bound :
      ∀ᵐ y ∂volume,
        ‖(f x - f (x - y)) * mηC y‖ ≤ (ε / 2) * mη y := by
    refine Filter.Eventually.of_forall ?_
    intro y
    by_cases hy0 : mη y = 0
    · -- Both sides are zero
      simp [mηC, hy0]
    · -- On the (topological) support we have ‖y‖ ≤ η < δ₀, hence the UC bound
      have hy_support : y ∈ tsupport mη := by
        have : y ∈ Function.support mη := by
          simpa [Function.support] using hy0
        exact subset_tsupport _ this
      have hy_ball : y ∈ Metric.closedBall (0 : Fin n → ℝ) η :=
        tsupport_scaledMollifier_subset hψ hη_pos hy_support
      have hy_norm_le : ‖y‖ ≤ η := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hy_ball
      have hy_norm_lt : ‖y‖ < δ₀ := lt_of_le_of_lt hy_norm_le hη_lt
      have hxy_norm : ‖x - (x - y)‖ < δ₀ := by
        -- ‖x - (x - y)‖ = ‖y‖
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
          using hy_norm_lt
      have h_uc := hδ₀' x (x - y) hxy_norm
      have h_uc_le : ‖f x - f (x - y)‖ ≤ ε / 2 := le_of_lt h_uc
      have h_norm_mηC : ‖mηC y‖ = mη y := by
        have hnn := h_nonneg_mη y
        simp [mηC, Real.norm_eq_abs, abs_of_nonneg hnn]
      have h_rhs_nonneg : 0 ≤ (ε / 2) * mη y :=
        mul_nonneg (by have := half_pos hε; exact (le_of_lt this))
          (h_nonneg_mη y)
      -- Now multiply the UC bound by ‖mηC y‖ = mη y
      have :
          ‖(f x - f (x - y)) * mηC y‖
            = ‖f x - f (x - y)‖ * ‖mηC y‖ := by
        simp
      have :
          ‖(f x - f (x - y)) * mηC y‖ ≤ (ε / 2) * ‖mηC y‖ := by
        simpa [this, mul_comm]
          using mul_le_mul_of_nonneg_right h_uc_le (by simp)
      simpa [h_norm_mηC]
        using this.trans_eq (by simp [h_norm_mηC, mul_comm, mul_left_comm, mul_assoc])

  -- Convert to an integral bound
  have h_diff_mul_cont :
      Continuous (fun y : (Fin n → ℝ) => (f x - f (x - y)) * mηC y) := by
    have h_diff_cont : Continuous (fun y : (Fin n → ℝ) => f x - f (x - y)) :=
      (continuous_const.sub h_transl_cont)
    exact h_diff_cont.mul h_mηC_cont
  have h_diff_mul_compact :
      HasCompactSupport (fun y : (Fin n → ℝ) => (f x - f (x - y)) * mηC y) := by
    simpa [mηC, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc]
      using
        (HasCompactSupport.mul_right
          (f := mηC) (f' := fun y : (Fin n → ℝ) => f x - f (x - y)) h_mηC_compact)
  have h_integrable_left :
      Integrable (fun y => ‖(f x - f (x - y)) * mηC y‖) volume := by
    have h_int : Integrable (fun y : (Fin n → ℝ) => (f x - f (x - y)) * mηC y) volume :=
      h_diff_mul_cont.integrable_of_hasCompactSupport h_diff_mul_compact
    simpa using h_int.norm
  have h_integrable_right :
      Integrable (fun y => (ε / 2) * mη y) volume := by
    -- mη is integrable (real), hence so is scaling by ε/2
    have h_div_cont :
        Continuous (fun x : (Fin n → ℝ) => fun i => x i / η) := by
      have :
          (fun x : (Fin n → ℝ) => fun i => x i / η)
            = fun x : (Fin n → ℝ) => (η⁻¹ : ℝ) • x := by
        funext x i; simp [div_eq_mul_inv, mul_comm]
      simpa [this] using (continuous_const_smul (η⁻¹ : ℝ))
    have h_cont : Continuous (scaledMollifier ψ η) := by
      simpa [scaledMollifier]
        using (continuous_const.mul (hψ.smooth.continuous.comp h_div_cont))
    have h_compact := hasCompactSupport_scaledMollifier hψ.compact_support hη_pos
    have h_mη_int : Integrable (fun x => scaledMollifier ψ η x) volume :=
      h_cont.integrable_of_hasCompactSupport h_compact
    simpa [mul_comm, mul_left_comm, mul_assoc]
      using h_mη_int.mul_const (ε / 2)

  have h_int_norm_le :
      ∫ y, ‖(f x - f (x - y)) * mηC y‖
        ≤ ∫ y, (ε / 2) * mη y := by
    refine MeasureTheory.integral_mono_ae
        h_integrable_left h_integrable_right ?_
    exact h_pointwise_bound

  -- Combine everything
  have h_main_bound :
      ‖f x - ∫ y, f (x - y) * (mη y)‖ ≤ ε / 2 := by
    have h1 :
        ‖f x - ∫ y, f (x - y) * (mη y)‖
          = ‖∫ y, (f x - f (x - y)) * mηC y‖ := by
      simp [h_diff_eq_integral, h_to_single]
    have h2 :
        ‖∫ y, (f x - f (x - y)) * mηC y‖
          ≤ ∫ y, ‖(f x - f (x - y)) * mηC y‖ :=
      norm_integral_le_integral_norm _
    have h3 :
        ∫ y, (ε / 2) * mη y = (ε / 2) * ∫ y, mη y := by
      -- move the constant outside the integral
      simpa [mul_comm, mul_left_comm, mul_assoc]
        using (integral_const_mul (μ := volume) (f := fun y => mη y) (ε / 2))
    have h4 : (ε / 2) * ∫ y, mη y = ε / 2 := by
      simp [h_mη_integral_one]
    have : ∫ y, ‖(f x - f (x - y)) * mηC y‖ ≤ ε / 2 := by
      simpa [h3, h4] using h_int_norm_le
    exact (h1 ▸ (le_trans h2 this))

  -- Conclude strict inequality using ε/2 < ε
  have hhalf_lt : ε / 2 < ε := by have := half_lt_self hε; simpa using this
  exact lt_of_le_of_lt h_main_bound hhalf_lt

/--
**Triangle inequality for Lp norm.**

‖f - h‖_p ≤ ‖f - g‖_p + ‖g - h‖_p
-/
lemma eLpNorm_triangle_inequality
    (f g h : (Fin n → ℝ) → ℂ)
    (p : ℝ≥0∞)
    (hp : 1 ≤ p)
    (hfg : AEStronglyMeasurable (fun x => f x - g x) volume)
    (hgh : AEStronglyMeasurable (fun x => g x - h x) volume) :
    eLpNorm (fun x => f x - h x) p volume ≤
    eLpNorm (fun x => f x - g x) p volume +
    eLpNorm (fun x => g x - h x) p volume := by
  have h_decomp :
      (fun x => f x - h x) =
        (fun x => f x - g x) + fun x => g x - h x := by
    funext x
    simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  simpa [h_decomp] using
    (eLpNorm_add_le (μ := volume) (p := p)
      (f := fun x => f x - g x)
      (g := fun x => g x - h x)
      hfg hgh hp)

/--
**Three-way triangle inequality (used in proof steps).**

‖f - φ‖_p ≤ ‖f - g‖_p + ‖g - ψ‖_p + ‖ψ - φ‖_p

This is used in the paper's Section 4.2 for the error analysis.
-/
lemma eLpNorm_triangle_three
    (f g ψ φ : (Fin n → ℝ) → ℂ)
    (p : ℝ≥0∞)
    (hp : 1 ≤ p)
    (hfg : AEStronglyMeasurable (fun x => f x - g x) volume)
    (hgψ : AEStronglyMeasurable (fun x => g x - ψ x) volume)
    (hψφ : AEStronglyMeasurable (fun x => ψ x - φ x) volume) :
    eLpNorm (fun x => f x - φ x) p volume ≤
    eLpNorm (fun x => f x - g x) p volume +
    eLpNorm (fun x => g x - ψ x) p volume +
    eLpNorm (fun x => ψ x - φ x) p volume := by
  have hgφ : AEStronglyMeasurable (fun x => g x - φ x) volume := by
    have h_sum := hgψ.add hψφ
    have h_eq :
        (fun x => g x - φ x) =
          (fun x => g x - ψ x) + fun x => ψ x - φ x := by
      funext x
      simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    simpa [h_eq] using h_sum
  have h_triangle₁ :=
    eLpNorm_triangle_inequality (f := f) (g := g) (h := φ) (p := p) hp hfg hgφ
  have h_triangle₂ :=
    eLpNorm_triangle_inequality (f := g) (g := ψ) (h := φ) (p := p) hp hgψ hψφ
  refine h_triangle₁.trans ?_
  have h_add := add_le_add_left h_triangle₂ (eLpNorm (fun x => f x - g x) p volume)
  simpa [add_comm, add_left_comm, add_assoc] using h_add

/--
**Explicit support bound for convolution.**

If supp(f) ⊆ B_R and supp(g) ⊆ B_δ, then supp(f * g) ⊆ B_{R+δ}.
-/
lemma convolution_support_ball_subset
    (f g : (Fin n → ℝ) → ℂ)
    (R δ : ℝ)
    (hf_supp : tsupport f ⊆ Metric.closedBall (0 : Fin n → ℝ) R)
    (hg_supp : tsupport g ⊆ Metric.closedBall (0 : Fin n → ℝ) δ) :
    tsupport (fun x => ∫ y, f (x - y) * g y) ⊆
      Metric.closedBall (0 : Fin n → ℝ) (R + δ) := by
  set h := fun x => ∫ y, f (x - y) * g y
  have h_support_subset :
      Function.support h ⊆ Metric.closedBall (0 : Fin n → ℝ) (R + δ) := by
    have h_conv_subset :
        Function.support h ⊆ Function.support g + Function.support f := by
      simpa [h, convolution, MeasureTheory.convolution, mul_comm] using
        (support_convolution_subset
          (μ := MeasureSpace.volume)
          (L := ContinuousLinearMap.mul ℝ ℂ)
          (f := g) (g := f))
    refine h_conv_subset.trans ?_
    have h_support_tsupp :
        Function.support g + Function.support f ⊆
          tsupport g + tsupport f :=
      Set.add_subset_add (subset_tsupport _) (subset_tsupport _)
    refine h_support_tsupp.trans ?_
    intro x hx
    rcases hx with ⟨u, hu, v, hv, rfl⟩
    have hu_norm : ‖u‖ ≤ δ := by
      simpa [dist_eq_norm] using Metric.mem_closedBall.mp (hg_supp hu)
    have hv_norm : ‖v‖ ≤ R := by
      simpa [dist_eq_norm] using Metric.mem_closedBall.mp (hf_supp hv)
    have h_norm : ‖u + v‖ ≤ R + δ := by
      have h_add : ‖u + v‖ ≤ ‖u‖ + ‖v‖ := norm_add_le _ _
      exact h_add.trans <| by
        simpa [add_comm] using add_le_add hu_norm hv_norm
    refine Metric.mem_closedBall.mpr ?_
    simpa [dist_eq_norm, add_comm] using h_norm
  have h_closed : IsClosed (Metric.closedBall (0 : Fin n → ℝ) (R + δ)) :=
    Metric.isClosed_closedBall
  have h_closure_subset :
      closure (Function.support h) ⊆ Metric.closedBall (0 : Fin n → ℝ) (R + δ) :=
    closure_minimal h_support_subset h_closed
  simpa [tsupport, h] using h_closure_subset

/--
**Mollifier convergence in Lp (general result).**

For f ∈ Lp with 1 ≤ p < ∞ and ψ an approximate identity:
  ‖f - f * ψ_η‖_p → 0 as η → 0
-/
theorem mollifier_converges_Lp
    (f : (Fin n → ℝ) → ℂ)
    (ψ : (Fin n → ℝ) → ℝ)
    (p : ℝ≥0∞)
    (hp : 1 ≤ p) (hp_ne_top : p ≠ ∞)
    (hf : MemLp f p volume)
    (hψ : IsApproximateIdentity ψ) :
    ∀ ε > 0, ∃ δ > 0, ∀ η : ℝ, 0 < η → η < δ →
      eLpNorm (fun x => f x - ∫ y, f (x - y) * (scaledMollifier ψ η y)) p volume <
        ENNReal.ofReal ε := by
  intro ε hε
  -- Approximate f in Lᵖ by a continuous compactly supported g
  obtain ⟨g, hg_cont, hg_compact, hg_memLp, hfg_small⟩ :=
    continuous_compactSupport_dense_Lp (p := p) (hp_ne_top := hp_ne_top)
      f hf (ε := ε / 4) (by positivity)

  -- A convenient symmetric form: ‖g - f‖ₚ = ‖f - g‖ₚ
  have hgf_small : eLpNorm (fun x => g x - f x) p volume < ENNReal.ofReal (ε / 4) := by
    have : eLpNorm (fun x => g x - f x) p volume = eLpNorm (g - f) p volume := rfl
    rw [this, eLpNorm_sub_comm]
    exact hfg_small

  -- Choose a finite-measure core set covering the supports uniformly in small η
  obtain ⟨R, hR_subset, hR_ge_one⟩ := tsupport_subset_closedBall g hg_compact
  set S : Set (Fin n → ℝ) := Metric.closedBall (0 : Fin n → ℝ) (R + 1) with hS_def
  have hS_meas : MeasurableSet S := by
    simpa [hS_def] using
      (Metric.isClosed_closedBall
        : IsClosed (Metric.closedBall (0 : Fin n → ℝ) (R + 1))).measurableSet
  have hμS_lt_top : volume S < ⊤ := by
    simpa [hS_def]
      using (MeasureTheory.measure_closedBall_lt_top (x := (0 : Fin n → ℝ)) (r := R + 1))
  have hμS_ne_top : volume S ≠ ∞ := ne_of_lt hμS_lt_top
  have hμS_pos : 0 < volume S := by
    have hR_pos : 0 < R + 1 := by linarith [hR_ge_one]
    calc 0 < volume (Metric.ball (0 : Fin n → ℝ) (R + 1)) := Metric.measure_ball_pos volume 0 hR_pos
      _ ≤ volume S := by
        rw [hS_def]
        exact measure_mono Metric.ball_subset_closedBall

  -- Uniform (sup-norm) control for g − g * ψ_η from continuity + compact support
  -- Pick a small target on S so that its Lᵖ bound is ≤ ε/2.
  have h_exponent_nonneg : 0 ≤ 1 / p.toReal := by
    have hp_toReal_nonneg : 0 ≤ p.toReal := ENNReal.toReal_nonneg
    exact div_nonneg zero_le_one hp_toReal_nonneg
  have h_powS_ne_top : (volume S) ^ (1 / p.toReal) ≠ (∞ : ℝ≥0∞) :=
    ENNReal.rpow_ne_top_of_nonneg h_exponent_nonneg hμS_ne_top
  -- Choose δ₀ from the uniform convergence theorem for g with a small target on S.
  -- Let target δg satisfy: (μ S)^{1/p} * δg ≤ ε/2.
  -- We can simply ask the sup-norm error be ≤ ε / (2 * ((μ S)^{1/p}).toReal).
  set δg : ℝ := ε / (2 * ((volume S) ^ (1 / p.toReal)).toReal) with hδg_def
  have hδg_pos : 0 < δg := by
    have hden_pos : 0 < 2 * ((volume S) ^ (1 / p.toReal)).toReal := by
      have hpos1 : (0 : ℝ) < 2 := by norm_num
      have hS_toReal_pos : 0 < ((volume S) ^ (1 / p.toReal)).toReal := by
        refine ENNReal.toReal_pos ?_ h_powS_ne_top
        intro h_zero
        have : volume S = 0 := by
          by_contra h_ne_zero
          have : 0 < volume S ^ (1 / p.toReal) :=
            ENNReal.rpow_pos_of_nonneg hμS_pos h_exponent_nonneg
          exact this.ne' h_zero
        exact (ne_of_gt hμS_pos) this
      exact mul_pos hpos1 hS_toReal_pos
    exact div_pos hε hden_pos
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ :=
    mollifier_converges_continuous g ψ hg_cont hg_compact hψ δg hδg_pos

  -- We will require η < min δ₀ 1 to also control the support of ψ_η.
  refine ⟨min δ₀ 1, lt_min hδ₀_pos zero_lt_one, ?_⟩
  intro η hη_pos hη_lt

  -- Abbreviations
  set mη : (Fin n → ℝ) → ℝ := fun y => scaledMollifier ψ η y with hmη
  let mηC : (Fin n → ℝ) → ℂ := fun y => (mη y : ℝ)

  -- Estimate by three-way triangle inequality in Lᵖ
  -- Define the two convolutions
  set conv_f : (Fin n → ℝ) → ℂ :=
    fun x => ∫ y, f (x - y) * mηC y with hconvf
  set conv_g : (Fin n → ℝ) → ℂ :=
    fun x => ∫ y, g (x - y) * mηC y with hconvg

  -- Show measurability of the subterms needed for the triangle inequality
  have hfg_meas : AEStronglyMeasurable (fun x => f x - g x) volume :=
    hf.aestronglyMeasurable.sub hg_memLp.aestronglyMeasurable
  -- Continuity and compact support properties needed throughout
  have h_div_cont :
      Continuous (fun y : (Fin n → ℝ) => fun i => y i / η) := by
    have :
        (fun y : (Fin n → ℝ) => fun i => y i / η)
          = fun y : (Fin n → ℝ) => (η⁻¹ : ℝ) • y := by
      funext y i; simp [div_eq_mul_inv, mul_comm]
    simpa [this] using (continuous_const_smul (η⁻¹ : ℝ))
  have h_mη_cont : Continuous mη := by
    simpa [mη, hmη, scaledMollifier]
      using (continuous_const.mul (hψ.smooth.continuous.comp h_div_cont))
  have h_mηC_cont : Continuous mηC := by
    simpa using (continuous_ofReal.comp h_mη_cont)
  have h_mηC_compact : HasCompactSupport mηC := by
    -- transfer compact support from the real-valued scaled mollifier
    have h_real := hasCompactSupport_scaledMollifier hψ.compact_support hη_pos
    -- upgrade to ℂ-valued by eventual equality
    rw [hasCompactSupport_iff_eventuallyEq] at h_real ⊢
    exact h_real.mono (by
      intro y hy
      simp only [mηC, mη]
      have : scaledMollifier ψ η y = 0 := hy
      rw [this]
      simp)

  have hmη_memLp_one : MemLp mηC 1 volume := by
    -- Move integrability from ℝ to ℂ via continuous/compact support
    -- (mηC has compact support and is continuous)
    have h_intC : Integrable mηC volume :=
      h_mηC_cont.integrable_of_hasCompactSupport h_mηC_compact
    simpa [memLp_one_iff_integrable (μ := volume)] using h_intC

  -- Convolution bounds (Young with r = p, q = 1): obtain MemLp and eLpNorm bounds
  have h_conv_f_memLp : MemLp conv_f p volume ∧
      eLpNorm conv_f p volume ≤ eLpNorm f p volume * eLpNorm mηC 1 volume := by
    simpa [conv_f, hconvf]
      using
        (young_convolution_inequality (f := f) (g := mηC)
          (p := p) (q := (1 : ℝ≥0∞)) (r := p)
          hp (by rfl) (by simp [add_comm]) hf hmη_memLp_one)
  have h_conv_g_memLp : MemLp conv_g p volume ∧
      eLpNorm conv_g p volume ≤ eLpNorm g p volume * eLpNorm mηC 1 volume := by
    simpa [conv_g, hconvg]
      using
        (young_convolution_inequality (f := g) (g := mηC)
          (p := p) (q := (1 : ℝ≥0∞)) (r := p)
          hp (by rfl) (by simp [add_comm]) hg_memLp hmη_memLp_one)
  have h_conv_f_meas : AEStronglyMeasurable conv_f volume :=
    (h_conv_f_memLp.1).aestronglyMeasurable
  have h_conv_g_meas : AEStronglyMeasurable conv_g volume :=
    (h_conv_g_memLp.1).aestronglyMeasurable
  have hg_conv_meas : AEStronglyMeasurable (fun x => g x - conv_g x) volume :=
    hg_cont.aestronglyMeasurable.sub h_conv_g_meas
  have hconv_diff_meas :
      AEStronglyMeasurable (fun x => conv_g x - conv_f x) volume :=
    h_conv_g_meas.sub h_conv_f_meas

  -- Apply the three-term triangle inequality
  have h_triangle :=
    eLpNorm_triangle_three (f := f) (g := g)
      (ψ := conv_g) (φ := conv_f) (p := p) hp hfg_meas hg_conv_meas hconv_diff_meas

  -- We will now bound each of the three terms on the right-hand side.
  -- Term A: ‖f - g‖ₚ < ε/4 (by density choice)
  have hA_lt :
      eLpNorm (fun x => f x - g x) p volume < ENNReal.ofReal (ε / 4) := hfg_small

  -- Term C: ‖conv_g - conv_f‖ₚ ≤ ‖g - f‖ₚ · ‖mηC‖₁, and ‖mηC‖₁ = 1
  have h_conv_sub_ae :
      (fun x => ∫ a, (g (x - a) - f (x - a)) * mηC a) =ᶠ[ae volume]
        (fun x => conv_g x - conv_f x) := by
    -- Use linearity of convolution on differences; provide integrability in y for a.e. x
    have h_int_g : ∀ᵐ x ∂volume, Integrable (fun y => g (x - y) * mηC y) volume := by
      -- actually for all x: product of continuous with compact support is integrable
      have h_all : ∀ x, Integrable (fun y => g (x - y) * mηC y) volume := by
        intro x
        have h_transl : Continuous (fun y : (Fin n → ℝ) => g (x - y)) := by
          have h_sub : Continuous (fun y : (Fin n → ℝ) => x - y) :=
            continuous_const.sub continuous_id
          exact hg_cont.comp h_sub
        have h_prod_cont : Continuous (fun y => g (x - y) * mηC y) :=
          h_transl.mul h_mηC_cont
        have h_prod_compact :
            HasCompactSupport (fun y => g (x - y) * mηC y) := by
          -- compact support from mηC
          have : Function.support (fun y => g (x - y) * mηC y) ⊆ Function.support mηC := by
            apply Function.support_mul_subset_right
          exact h_mηC_compact.mono this
        exact h_prod_cont.integrable_of_hasCompactSupport h_prod_compact
      exact Filter.Eventually.of_forall h_all
    have h_int_g_ae :
        ∀ᵐ x ∂volume, Integrable (fun y => g (x - y) * mηC y) volume := by
      -- we actually prove a stronger statement: for all x
      refine Filter.Eventually.of_forall ?_
      intro x
      -- As above (h_int_g), the product of continuous compactly supported functions is integrable
      have h_transl : Continuous (fun y : (Fin n → ℝ) => g (x - y)) := by
        have h_sub : Continuous (fun y : (Fin n → ℝ) => x - y) :=
          continuous_const.sub continuous_id
        exact hg_cont.comp h_sub
      have h_prod_cont : Continuous (fun y => g (x - y) * mηC y) :=
        h_transl.mul h_mηC_cont
      have h_prod_compact :
          HasCompactSupport (fun y => g (x - y) * mηC y) := by
        have : Function.support (fun y => g (x - y) * mηC y)
                ⊆ Function.support mηC := by
          apply Function.support_mul_subset_right
        exact h_mηC_compact.mono this
      exact h_prod_cont.integrable_of_hasCompactSupport h_prod_compact

    have h_int_f_ae :
        ∀ᵐ x ∂volume, Integrable (fun y => f (x - y) * mηC y) volume := by
      by_cases hp_one : p = 1
      · -- Case p = 1, take q = ∞
        have hmηC_mem_top : MemLp mηC ∞ volume :=
          h_mηC_cont.memLp_of_hasCompactSupport h_mηC_compact
        -- Build the Holder triple instance for (p,q,r) = (1,∞,1)
        have p_inv_add : p⁻¹ + (∞ : ℝ≥0∞)⁻¹ = (1 : ℝ≥0∞) := by
          simp [hp_one]
        haveI : ENNReal.HolderTriple p ∞ 1 := ⟨by simpa [p_inv_add, inv_one]⟩
        -- Prove integrability for all x via MemLp.integrable_mul on y
        refine Filter.Eventually.of_forall ?_
        intro x
        -- Translation preserves MemLp in y
        have h_pres_neg : MeasurePreserving (fun y : (Fin n → ℝ) => -y) volume volume :=
          Measure.measurePreserving_neg (volume : Measure (Fin n → ℝ))
        have h_pres_add :
            MeasurePreserving (fun y : (Fin n → ℝ) => y + x) volume volume :=
          measurePreserving_add_right (μ := volume) x
        have h_pres :
            MeasurePreserving (fun y : (Fin n → ℝ) => x - y) volume volume := by
          -- x - y = x + (-y)
          have := h_pres_add.comp h_pres_neg
          simpa [Function.comp, sub_eq_add_neg, add_comm] using this
        have hf_shift_mem : MemLp (fun y => f (x - y)) p volume :=
          hf.comp_measurePreserving h_pres
        -- Apply Hölder (product lies in L¹)
        have : Integrable (fun y => (fun y => f (x - y)) y * mηC y) volume :=
          (MemLp.integrable_mul (μ := volume) (p := p) (q := (∞ : ℝ≥0∞))
            hf_shift_mem hmηC_mem_top)
        simpa using this
      · -- Case 1 < p < ∞: choose q the conjugate exponent to p
        have hp_one_lt : (1 : ℝ≥0∞) < p := lt_of_le_of_ne hp (by simpa [eq_comm] using hp_one)
        have hp_lt_top : p < ⊤ := lt_of_le_of_ne le_top hp_ne_top
        obtain ⟨q, hpq, -⟩ :=
          conjugate_exponent_formula (p := p) hp_one_lt hp_lt_top
        -- Extract 1/p + 1/q = 1 from `IsConjugateExponent` proof
        have hpq_sum : 1 / p + 1 / q = 1 := by
          rcases hpq with h1 | h2 | hpq'
          · -- Case p = 1, q = ∞: contradicts 1 < p
            rcases h1 with ⟨hp_eq, -⟩
            rw [hp_eq] at hp_one_lt
            norm_num at hp_one_lt
          · -- Case p = ∞, q = 1: contradicts p < ∞
            rcases h2 with ⟨hp_eq, -⟩
            rw [hp_eq] at hp_lt_top
            simp at hp_lt_top
          · -- Case 1 < p < ∞ and 1 < q < ∞ and 1/p + 1/q = 1
            rcases hpq' with ⟨_, _, _, _, hsum⟩
            exact hsum
        have p_inv_add : p⁻¹ + q⁻¹ = 1 := by simpa [one_div] using hpq_sum
        haveI : ENNReal.HolderTriple p q 1 := ⟨by simp [p_inv_add, inv_one]⟩
        have hmηC_mem_q : MemLp mηC q volume :=
          h_mηC_cont.memLp_of_hasCompactSupport h_mηC_compact
        -- Prove integrability for all x via MemLp.integrable_mul on y
        refine Filter.Eventually.of_forall ?_
        intro x
        have h_pres_neg : MeasurePreserving (fun y : (Fin n → ℝ) => -y) volume volume :=
          Measure.measurePreserving_neg (volume : Measure (Fin n → ℝ))
        have h_pres_add :
            MeasurePreserving (fun y : (Fin n → ℝ) => y + x) volume volume :=
          measurePreserving_add_right (μ := volume) x
        have h_pres :
            MeasurePreserving (fun y : (Fin n → ℝ) => x - y) volume volume := by
          have := h_pres_add.comp h_pres_neg
          simpa [Function.comp, sub_eq_add_neg, add_comm] using this
        have hf_shift_mem : MemLp (fun y => f (x - y)) p volume :=
          hf.comp_measurePreserving h_pres
        have : Integrable (fun y => (fun y => f (x - y)) y * mηC y) volume :=
          (MemLp.integrable_mul (μ := volume) (p := p) (q := q)
            hf_shift_mem hmηC_mem_q)
        simpa using this
    -- Aggregate both fibrewise integrability results
    have h_ae_both :
        ∀ᵐ x ∂volume,
          Integrable (fun y => g (x - y) * mηC y) volume ∧
          Integrable (fun y => f (x - y) * mηC y) volume := by
      filter_upwards [h_int_g_ae, h_int_f_ae] with x hxg hxf
      exact ⟨hxg, hxf⟩
    -- On the a.e. set where both integrals exist, use linearity to rewrite the difference
    have h_eq_ae :
        (fun x => ∫ a, (g (x - a) - f (x - a)) * mηC a)
          =ᶠ[ae volume]
        (fun x => conv_g x - conv_f x) := by
      filter_upwards [h_ae_both] with x hx
      rcases hx with ⟨hg_int, hf_int⟩
      have h_sub_int :
          Integrable (fun a => g (x - a) * mηC a - f (x - a) * mηC a) volume :=
        hg_int.sub hf_int
      have h_eq :
          ∫ a, ((g (x - a) - f (x - a)) * mηC a) =
            (∫ a, g (x - a) * mηC a) - ∫ a, f (x - a) * mηC a := by
        have h_left :
            (fun a => (g (x - a) - f (x - a)) * mηC a)
              = fun a => g (x - a) * mηC a - f (x - a) * mηC a := by
          funext a; ring
        simp [h_left, integral_sub hg_int hf_int]
      simpa [conv_g, conv_f, hconvg, hconvf] using h_eq
    -- Conclude the desired a.e. equality
    simpa [MeasureTheory.convolution] using h_eq_ae
  have h_conv_diff_bound :
      eLpNorm (fun x => conv_g x - conv_f x) p volume
        ≤ eLpNorm (fun x => g x - f x) p volume * eLpNorm mηC 1 volume := by
    -- Apply Young to (g - f) * mηC and compare a.e.
    have hY :=
      (young_convolution_inequality
        (f := fun x => g x - f x) (g := mηC)
        (p := p) (q := (1 : ℝ≥0∞)) (r := p)
        hp (by rfl) (by simp [add_comm])
        (hg_memLp.sub hf) hmη_memLp_one).2
    -- Conclude using a.e.-congruence
    refine (le_trans ?_ hY)
    have h_congr :=
      eLpNorm_congr_ae (μ := volume) (p := p) (f :=
        (fun x => ∫ a, (g (x - a) - f (x - a)) * mηC a))
        (g := fun x => conv_g x - conv_f x) h_conv_sub_ae
    simpa [MeasureTheory.convolution] using ge_of_eq h_congr

  -- Evaluate ‖mηC‖₁ = 1 using normalization and nonnegativity
  have hη_nonneg : 0 ≤ η := le_of_lt hη_pos
  have hmη_nonneg : ∀ x, 0 ≤ mη x :=
    scaledMollifier_nonneg hψ.nonneg hη_nonneg
  have hmηC_norm_eq : ∀ x, ‖mηC x‖ = mη x := by
    intro x
    have := hmη_nonneg x
    simp [mηC, Real.norm_eq_abs, abs_of_nonneg this]
  have h_enorm_eq :
      eLpNorm mηC 1 volume
        = ENNReal.ofReal (∫ x, mη x) := by
    -- eLpNorm for p = 1 equals the lintegral of the extended norm
    have h_nonneg_ae : 0 ≤ᵐ[volume] fun x => ‖mηC x‖ :=
      Filter.Eventually.of_forall (by intro x; exact norm_nonneg _)
    have h_integrable_norm : Integrable (fun x => ‖mηC x‖) volume := by
      -- From integrability of mηC
      have h_intC : Integrable mηC volume :=
        (memLp_one_iff_integrable (μ := volume)).1 hmη_memLp_one
      exact h_intC.norm
    have h_lint_eq :
        ∫⁻ x, ‖mηC x‖ₑ ∂volume
          = ENNReal.ofReal (∫ x, ‖mηC x‖ ∂volume) := by
      simpa [ofReal_norm_eq_enorm]
        using
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
            h_integrable_norm h_nonneg_ae).symm
    have h_norm_eq : ∫ x, ‖mηC x‖ ∂volume = ∫ x, mη x ∂volume := by
      have h1 : (fun x => ‖mηC x‖) = fun x => mη x := by
        funext x; simp [hmηC_norm_eq x]
      simp [h1]
    simp [MeasureTheory.eLpNorm_one_eq_lintegral_enorm, h_lint_eq, h_norm_eq]
  have hmη_one : eLpNorm mηC 1 volume = 1 := by
    rw [h_enorm_eq]
    rw [integral_scaledMollifier_eq_one hψ hη_pos]
    simp

  -- Now convert Term C into < ε/4 using the bound on ‖g - f‖ₚ
  have hC_lt :
      eLpNorm (fun x => conv_g x - conv_f x) p volume < ENNReal.ofReal (ε / 4) := by
    -- Bound by product and then use hmη_one
    have h_mul_le :
        eLpNorm (fun x => conv_g x - conv_f x) p volume
          ≤ eLpNorm (fun x => g x - f x) p volume := by
      calc eLpNorm (fun x => conv_g x - conv_f x) p volume
          ≤ eLpNorm (fun x => g x - f x) p volume * eLpNorm mηC 1 volume := h_conv_diff_bound
        _ = eLpNorm (fun x => g x - f x) p volume * 1 := by rw [hmη_one]
        _ = eLpNorm (fun x => g x - f x) p volume := by ring
    exact lt_of_le_of_lt h_mul_le hgf_small

  -- Term B: ‖g - conv_g‖ₚ on the finite-measure core set S is small by uniform bound
  -- First, note that outside S, both g and conv_g vanish once η < 1.
  -- Hence the difference equals its indicator on S.
  have hη_lt_one : η < 1 := lt_of_lt_of_le hη_lt (min_le_right _ _)
  have hS_contains_support :
      tsupport conv_g ⊆ S := by
    -- support(conv_g) ⊆ B_{R + η} ⊆ B_{R + 1} = S
    -- First, upgrade the tsupport bound for the real-valued kernel to the complex-valued one.
    have h_mη_real :
        tsupport (scaledMollifier ψ η)
          ⊆ Metric.closedBall (0 : Fin n → ℝ) η :=
      tsupport_scaledMollifier_subset hψ hη_pos
    have h_support_subset :
        Function.support mηC ⊆ Function.support (scaledMollifier ψ η) := by
      intro x hx
      have : mηC x ≠ 0 := hx
      -- If mη x = 0 then mηC x = 0; hence mη x ≠ 0
      have : mη x ≠ 0 := by
        intro hzero
        apply hx
        show mηC x = 0
        calc mηC x = ↑(mη x) := rfl
          _ = ↑(0 : ℝ) := by rw [hzero]
          _ = (0 : ℂ) := by norm_num
      show scaledMollifier ψ η x ≠ 0
      convert this
    have h_mηC_tsupport_subset :
        tsupport mηC ⊆ Metric.closedBall (0 : Fin n → ℝ) η := by
      -- tsupport mηC ⊆ tsupport mη by support inclusion, then use h_mη_real
      have h_ts_subset : tsupport mηC ⊆ tsupport (scaledMollifier ψ η) := by
        intro x hx
        have hx' : x ∈ closure (Function.support mηC) := by
          simpa [tsupport] using hx
        have hx'' : x ∈ closure (Function.support (scaledMollifier ψ η)) :=
          closure_mono h_support_subset hx'
        simpa [tsupport] using hx''
      exact h_ts_subset.trans h_mη_real
    have h_ball_subset :
        Metric.closedBall (0 : Fin n → ℝ) (R + η)
          ⊆ Metric.closedBall (0 : Fin n → ℝ) (R + 1) := by
      intro x hx
      have hx_norm : ‖x‖ ≤ R + η := by
        simpa [dist_eq_norm] using Metric.mem_closedBall.mp hx
      have h_le : R + η ≤ R + 1 := by
        have : (η : ℝ) ≤ 1 := le_of_lt hη_lt_one
        linarith
      have hx_norm' : ‖x‖ ≤ R + 1 := le_trans hx_norm h_le
      exact Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hx_norm')
    -- Use convolution support bound
    have h_conv_support :=
      convolution_support_ball_subset
        (f := g) (g := mηC) (R := R) (δ := η)
        hR_subset h_mηC_tsupport_subset
    -- Finish by transitivity
    exact h_conv_support.trans h_ball_subset

  have h_indicator_eq :
      (fun x => g x - conv_g x)
        = (fun x => Set.indicator S (fun z => g z - conv_g z) x) := by
    funext x
    by_cases hxS : x ∈ S
    · simp [Set.indicator, hxS]
    · -- outside S: both g and conv_g vanish
      have hx_notin_BR : x ∉ Metric.closedBall (0 : Fin n → ℝ) R := by
        intro hxBR
        have hxS' : x ∈ S := by
          have hxBR' : ‖x‖ ≤ R := by
            simpa [dist_eq_norm] using Metric.mem_closedBall.mp hxBR
          have hxS'' : ‖x‖ ≤ R + 1 := by linarith
          exact Metric.mem_closedBall.mpr (by simpa [hS_def, dist_eq_norm] using hxS'')
        exact hxS hxS'
      have hg_zero : g x = 0 := by
        -- use support inclusion: tsupport g ⊆ closedBall(0,R)
        by_contra hx_nonzero
        have hx_support : x ∈ Function.support g := by
          have : g x ≠ 0 := hx_nonzero
          simpa [Function.support] using this
        have hx_tsupport : x ∈ tsupport g :=
          subset_tsupport _ hx_support
        exact hx_notin_BR (hR_subset hx_tsupport)
      have hconv_zero : conv_g x = 0 := by
        have hx_notin : x ∉ tsupport conv_g := by
          intro hx_in
          have hxS' : x ∈ S := hS_contains_support hx_in
          exact hxS hxS'
        exact image_eq_zero_of_notMem_tsupport hx_notin
      simp [Set.indicator, hxS, hg_zero, hconv_zero]

  -- Use the indicator bound on S with the uniform ε-control given by mollifier_converges_continuous
  have h_pointwise_uniform : ∀ᵐ x ∂volume.restrict S,
      ‖g x - conv_g x‖ ≤ δg := by
    have h_all : ∀ x, ‖g x - conv_g x‖ ≤ δg := by
      intro x
      have : ‖g x - ∫ y, g (x - y) * mηC y‖ < δg := by
        -- apply the uniform convergence result for g with η < δ₀
        have hη_lt_δ₀ : η < δ₀ := lt_of_lt_of_le hη_lt (min_le_left _ _)
        have := hδ₀ η hη_pos hη_lt_δ₀ x
        simpa [conv_g, hconvg] using this
      exact le_of_lt this
    -- The bound holds on S
    apply Filter.Eventually.of_forall
    intro x
    exact h_all x

  have hB_bound :
      eLpNorm (fun x => g x - conv_g x) p volume
        ≤ (volume S) ^ (1 / p.toReal) * ENNReal.ofReal δg := by
    -- Since the function vanishes off S, apply the indicator restriction bound
    have h_indicator_eq' :
        eLpNorm (fun x => g x - conv_g x) p volume
          = eLpNorm (fun x => Set.indicator S (fun z => g z - conv_g z) x) p volume := by
      congr 1
    have h_core :=
      core_indicator_eLpNorm_bound (p := p) (coreSet := S)
        (h_core_meas := hS_meas)
        (g := fun x => g x - conv_g x) (δ := δg)
        (h_bound := by
          -- a.e. bound on S
          simpa using h_pointwise_uniform)
    simpa [h_indicator_eq'] using h_core

  -- Evaluate the right-hand side as ENNReal.ofReal (ε/2)
  have h_mul_eq :
      (volume S) ^ (1 / p.toReal) * ENNReal.ofReal δg
        = ENNReal.ofReal ((volume S) ^ (1 / p.toReal)).toReal * ENNReal.ofReal δg := by
    rw [ENNReal.ofReal_toReal h_powS_ne_top]
  have h_prod_eq :
      (volume S) ^ (1 / p.toReal) * ENNReal.ofReal δg
        = ENNReal.ofReal (ε / 2) := by
    -- Use δg = ε / (2 * ((μ S)^{1/p}).toReal)
    have hμS_toReal_nonneg : 0 ≤ ((volume S) ^ (1 / p.toReal)).toReal := ENNReal.toReal_nonneg
    have h_mul :
        ENNReal.ofReal ((volume S) ^ (1 / p.toReal)).toReal * ENNReal.ofReal δg
          = ENNReal.ofReal (((volume S) ^ (1 / p.toReal)).toReal * δg) := by
      rw [← ENNReal.ofReal_mul hμS_toReal_nonneg]
    have h_target : ((volume S) ^ (1 / p.toReal)).toReal * δg = ε / 2 := by
      rw [hδg_def]
      have hpow_pos : 0 < ((volume S) ^ (1 / p.toReal)).toReal := by
        apply ENNReal.toReal_pos
        · exact ne_of_gt (ENNReal.rpow_pos_of_nonneg hμS_pos h_exponent_nonneg)
        · exact h_powS_ne_top
      field_simp [ne_of_gt hpow_pos]
      ring
    -- Put the pieces together
    calc
      (volume S) ^ (1 / p.toReal) * ENNReal.ofReal δg
          = ENNReal.ofReal ((volume S) ^ (1 / p.toReal)).toReal * ENNReal.ofReal δg := h_mul_eq
      _ = ENNReal.ofReal (((volume S) ^ (1 / p.toReal)).toReal * δg) := h_mul
      _ = ENNReal.ofReal (ε / 2) := by rw [h_target]

  have hB_le :
      eLpNorm (fun x => g x - conv_g x) p volume ≤ ENNReal.ofReal (ε / 2) := by
    calc eLpNorm (fun x => g x - conv_g x) p volume
        ≤ (volume S) ^ (1 / p.toReal) * ENNReal.ofReal δg := hB_bound
      _ = ENNReal.ofReal (ε / 2) := h_prod_eq

  -- Finally, add the three bounds: ε/4 + ε/2 + ε/4 = ε
  -- Use monotonicity of addition in ℝ≥0∞.
  have h_sum_le :
      eLpNorm (fun x => f x - g x) p volume
        + eLpNorm (fun x => g x - conv_g x) p volume
        ≤ ENNReal.ofReal (ε / 4 + ε / 2) := by
    calc eLpNorm (fun x => f x - g x) p volume
            + eLpNorm (fun x => g x - conv_g x) p volume
          ≤ ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 2) := by
            exact add_le_add (le_of_lt hA_lt) hB_le
        _ = ENNReal.ofReal (ε / 4 + ε / 2) := by
            rw [← ENNReal.ofReal_add] <;> linarith
  have h_total_lt :
      eLpNorm (fun x => f x - g x) p volume
        + eLpNorm (fun x => g x - conv_g x) p volume
        + eLpNorm (fun x => conv_g x - conv_f x) p volume
        < ENNReal.ofReal (ε / 4 + ε / 2 + ε / 4) := by
    have h_sum_ne_top : eLpNorm (fun x => f x - g x) p volume
          + eLpNorm (fun x => g x - conv_g x) p volume ≠ ⊤ := by
      apply ne_of_lt
      calc eLpNorm (fun x => f x - g x) p volume
              + eLpNorm (fun x => g x - conv_g x) p volume
            ≤ ENNReal.ofReal (ε / 4 + ε / 2) := h_sum_le
          _ < ⊤ := ENNReal.ofReal_lt_top
    calc eLpNorm (fun x => f x - g x) p volume
            + eLpNorm (fun x => g x - conv_g x) p volume
            + eLpNorm (fun x => conv_g x - conv_f x) p volume
          < ENNReal.ofReal (ε / 4 + ε / 2) + ENNReal.ofReal (ε / 4) := by
            exact ENNReal.add_lt_add_of_le_of_lt h_sum_ne_top h_sum_le hC_lt
        _ = ENNReal.ofReal (ε / 4 + ε / 2 + ε / 4) := by
            rw [← ENNReal.ofReal_add] <;> linarith
  -- Conclude by triangle inequality
  have h_target_le :=
    calc
      eLpNorm (fun x => f x - conv_f x) p volume
          ≤ eLpNorm (fun x => f x - g x) p volume
              + eLpNorm (fun x => g x - conv_g x) p volume
              + eLpNorm (fun x => conv_g x - conv_f x) p volume :=
            h_triangle
      _ < ENNReal.ofReal (ε / 4 + ε / 2 + ε / 4) := h_total_lt
  -- ε/4 + ε/2 + ε/4 = ε
  have hε_sum : ε / 4 + ε / 2 + ε / 4 = ε := by ring
  simpa [conv_f, hconvf, hε_sum]
    using h_target_le

end Newton
