import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Real.ConjExponents
import Mathlib.MeasureTheory.Function.L1Space.Integrable

open MeasureTheory ENNReal NNReal
open scoped ENNReal BigOperators

variable {α : Type*} [MeasurableSpace α]
variable {μ : Measure α}
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/--
**Conjugate exponent relation.**

For 1 ≤ p ≤ ∞, the conjugate exponent q satisfies 1/p + 1/q = 1.
-/
def IsConjugateExponent (p q : ℝ≥0∞) : Prop :=
  (p = 1 ∧ q = ∞) ∨ (p = ∞ ∧ q = 1) ∨
  (1 < p ∧ p < ∞ ∧ 1 < q ∧ q < ∞ ∧ 1 / p + 1 / q = 1)

section HolderGeneral

/--
**Hölder's inequality (basic form for p = 1, q = ∞).**

For any measurable functions f and g:
  ∫ |f · g| dμ ≤ ‖f‖_{L^1} · ‖g‖_{L^∞}
-/
theorem holder_inequality_one_infty
    (f : α → E) (g : α → F)
    (hf : Integrable f μ)
    (hg_ae : AEStronglyMeasurable g μ)
    (hg_bound : ∃ C, ∀ᵐ x ∂μ, ‖g x‖ ≤ C) :
    ∫ x, ‖f x‖ * ‖g x‖ ∂μ ≤
      (∫ x, ‖f x‖ ∂μ) * (sInf {C | ∀ᵐ x ∂μ, ‖g x‖ ≤ C}) := by
  by_cases hμ : μ = 0
  · simp [hμ]
  set S := {C : ℝ | ∀ᵐ x ∂μ, ‖g x‖ ≤ C} with hS
  have hS_nonempty : S.Nonempty :=
    let ⟨C, hC⟩ := hg_bound
    ⟨max C 0, hC.mono fun x hx => hx.trans <| le_max_left _ _⟩
  have hf_norm : Integrable (fun x => ‖f x‖) μ := hf.norm
  set A := ∫ x, ‖f x‖ * ‖g x‖ ∂μ with hA
  set a := ∫ x, ‖f x‖ ∂μ with ha
  have ha_nonneg : 0 ≤ a := by
    have : ∀ x, 0 ≤ ‖f x‖ := fun x => norm_nonneg _
    simpa [ha] using integral_nonneg this
  have holder_with_bound : ∀ {C : ℝ}, C ∈ S → A ≤ a * C := by
    intro C hC
    have hC_ae : ∀ᵐ x ∂μ, ‖g x‖ ≤ C := hC
    have hC_nonneg : 0 ≤ C :=
      by
        have hμ_univ_ne : μ (Set.univ : Set α) ≠ 0 :=
          by simpa [Measure.measure_univ_eq_zero] using hμ
        by_contra hCneg
        have hCneg' : C < 0 := lt_of_not_ge hCneg
        have hμset : μ {x | C < ‖g x‖} = 0 := by
          simpa [not_le] using (ae_iff).1 hC_ae
        have hset : {x | C < ‖g x‖} = (Set.univ : Set α) := by
          ext x
          have hx : C < ‖g x‖ := lt_of_lt_of_le hCneg' (norm_nonneg _)
          simp [hx]
        exact hμ_univ_ne <| by simpa [hset] using hμset
    have h_mul_le : (fun x => ‖f x‖ * ‖g x‖) ≤ᵐ[μ] fun x => C * ‖f x‖ :=
      hC_ae.mono fun x hx =>
        by
          have hfx : 0 ≤ ‖f x‖ := norm_nonneg _
          have : ‖f x‖ * ‖g x‖ ≤ ‖f x‖ * C :=
            (mul_le_mul_of_nonneg_left hx hfx : _)
          simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have h_mul_abs : ∀ᵐ x ∂μ, ‖‖f x‖ * ‖g x‖‖ ≤ C * ‖f x‖ :=
      hC_ae.mono fun x hx =>
        by
          have hfx : 0 ≤ ‖f x‖ := norm_nonneg _
          have hgx : 0 ≤ ‖g x‖ := norm_nonneg _
          have h_nonneg : 0 ≤ ‖f x‖ * ‖g x‖ := mul_nonneg hfx hgx
          have h_rhs_nonneg : 0 ≤ C * ‖f x‖ := mul_nonneg hC_nonneg hfx
          have : ‖f x‖ * ‖g x‖ ≤ ‖f x‖ * C :=
            (mul_le_mul_of_nonneg_left hx hfx : _)
          simpa [Real.norm_of_nonneg h_nonneg, Real.norm_of_nonneg h_rhs_nonneg,
            mul_comm, mul_left_comm, mul_assoc] using this
    have h_mul_meas : AEStronglyMeasurable (fun x => ‖f x‖ * ‖g x‖) μ :=
      (hf_norm.aestronglyMeasurable.mul hg_ae.norm)
    have h_const_int : Integrable (fun x => C * ‖f x‖) μ := hf_norm.const_mul C
    have h_mul_int : Integrable (fun x => ‖f x‖ * ‖g x‖) μ :=
      Integrable.mono' h_const_int h_mul_meas h_mul_abs
    have h_integral_le := integral_mono_ae h_mul_int h_const_int h_mul_le
    have h_integral_const : ∫ x, C * ‖f x‖ ∂μ = C * a := by
      simpa [ha, mul_comm] using
        integral_const_mul (μ := μ) (r := C) (f := fun x => ‖f x‖)
    have : A ≤ C * a := by
      simpa [A, h_integral_const] using h_integral_le
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have h_eps : ∀ {ε : ℝ}, 0 < ε → A ≤ a * (sInf S + ε) := by
    intro ε hε
    obtain ⟨C, hC_mem, hC_lt⟩ := Real.lt_sInf_add_pos hS_nonempty hε
    have hAC : A ≤ a * C := holder_with_bound hC_mem
    have h_le : C ≤ sInf S + ε := le_of_lt hC_lt
    have h_order : a * C ≤ a * (sInf S + ε) :=
      mul_le_mul_of_nonneg_left h_le ha_nonneg
    exact hAC.trans h_order
  have hA_nonneg : 0 ≤ A :=
    by
      have : ∀ x, 0 ≤ ‖f x‖ * ‖g x‖ :=
        fun x => mul_nonneg (norm_nonneg _) (norm_nonneg _)
      simpa [A] using integral_nonneg this
  have h_final : A ≤ a * sInf S := by
    by_cases ha_zero : a = 0
    · obtain ⟨C₀, hC₀⟩ := hS_nonempty
      have hA_le_zero : A ≤ 0 := by
        simpa [ha_zero] using holder_with_bound hC₀
      have hA_eq_zero : A = 0 :=
        le_antisymm hA_le_zero hA_nonneg
      simp [hA_eq_zero, ha_zero]
    · have ha_ne : a ≠ 0 := ha_zero
      have ha_pos : 0 < a := lt_of_le_of_ne ha_nonneg (by simpa [eq_comm] using ha_ne)
      have h_eps' : ∀ {ε : ℝ}, 0 < ε → A ≤ a * sInf S + ε := by
        intro ε hε
        have hδpos : 0 < ε / a := div_pos hε ha_pos
        have hmain := h_eps hδpos
        have hmul : a * (sInf S + ε / a) = a * sInf S + ε := by
          simp [mul_add, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, ha_ne]
        simpa [hmul, mul_comm, mul_left_comm, mul_assoc] using hmain
      have h_lt : ∀ {ε : ℝ}, 0 < ε → A < a * sInf S + ε := by
        intro ε hε
        have hhalf : 0 < ε / 2 := half_pos hε
        have hineq := h_eps' hhalf
        have hlt : a * sInf S + ε / 2 < a * sInf S + ε := by
          have := half_lt_self hε
          exact add_lt_add_left this _
        exact lt_of_le_of_lt hineq hlt
      exact (le_iff_forall_pos_lt_add).2 fun ε hε => h_lt hε
  simpa [A, a, S, mul_comm, mul_left_comm, mul_assoc] using h_final

/--
**Hölder's inequality (general form with eLpNorm).**

For conjugate exponents 1 ≤ p, q ≤ ∞ with 1/p + 1/q = 1:
  ∫ |f · g| dμ ≤ ‖f‖_{L^p(μ)} · ‖g‖_{L^q(μ)}
-/
theorem holder_inequality
    (p q : ℝ≥0∞)
    (hpq : IsConjugateExponent p q)
    (f : α → E) (g : α → F)
    (hf : MemLp f p μ)
    (hg : MemLp g q μ) :
    Integrable (fun x => ‖f x‖ * ‖g x‖) μ ∧
    ∫ x, ‖f x‖ * ‖g x‖ ∂μ ≤
      (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal := by
  rcases hpq with hpq | hpq | hpq
  · rcases hpq with ⟨hp, hq⟩
    subst hp; subst hq
    -- Case `p = 1`, `q = ∞`
    have hf_int : Integrable f μ := by
      simpa [memLp_one_iff_integrable] using hf
    obtain ⟨hg_meas, hg_fin⟩ := hg
    have hg_bound : ∃ C, ∀ᵐ x ∂μ, ‖g x‖ ≤ C := by
      have hg_ne_top' : eLpNorm g ∞ μ ≠ ∞ := ne_of_lt hg_fin
      have hg_ne_top : eLpNormEssSup g μ ≠ ∞ :=
        by simpa [eLpNorm, eLpNorm_exponent_top] using hg_ne_top'
      refine ⟨(eLpNorm g ∞ μ).toReal, ?_⟩
      refine (ae_le_eLpNormEssSup (μ := μ) (f := fun x => g x)).mono ?_
      intro x hx
      have hx' : ENNReal.ofReal ‖g x‖ ≤ eLpNormEssSup g μ := by
        simpa [ofReal_norm_eq_enorm] using hx
      have := (ENNReal.ofReal_le_iff_le_toReal hg_ne_top).mp hx'
      simpa [eLpNorm, eLpNorm_exponent_top] using this
    have hg_ae : AEStronglyMeasurable g μ := hg_meas
    have :=
      holder_inequality_one_infty (μ := μ) (f := f) (g := g) hf_int hg_ae hg_bound
    refine ⟨?_, ?_⟩
    · obtain ⟨C, hC⟩ := hg_bound
      set C₀ := max C 0
      have hC₀_nonneg : 0 ≤ C₀ := le_max_right _ _
      have hC₀_bound : ∀ᵐ x ∂μ, ‖g x‖ ≤ C₀ :=
        hC.mono fun x hx => le_max_of_le_left hx
      have h_meas : AEStronglyMeasurable (fun x => ‖f x‖ * ‖g x‖) μ :=
        (hf_int.aestronglyMeasurable.norm.mul hg_ae.norm)
      have h_dom : ∀ᵐ x ∂μ, ‖‖f x‖ * ‖g x‖‖ ≤ C₀ * ‖f x‖ :=
        hC₀_bound.mono fun x hx =>
          by
            have hf_nonneg : 0 ≤ ‖f x‖ := norm_nonneg _
            have hg_nonneg : 0 ≤ ‖g x‖ := norm_nonneg _
            have hmul_nonneg : 0 ≤ ‖f x‖ * ‖g x‖ := mul_nonneg hf_nonneg hg_nonneg
            have h_rhs_nonneg : 0 ≤ C₀ * ‖f x‖ := mul_nonneg hC₀_nonneg hf_nonneg
            have hmul_le : ‖f x‖ * ‖g x‖ ≤ ‖f x‖ * C₀ :=
              (mul_le_mul_of_nonneg_left hx hf_nonneg : _)
            simpa [Real.norm_of_nonneg hmul_nonneg, Real.norm_of_nonneg h_rhs_nonneg,
              mul_comm, mul_left_comm, mul_assoc] using hmul_le
      have h_majorant : Integrable (fun x => C₀ * ‖f x‖) μ :=
        (hf_int.norm.const_mul C₀)
      exact Integrable.mono' h_majorant h_meas h_dom
    · -- Express the L¹ norm of `f` via `eLpNorm`.
      have hf_norm : Integrable (fun x => ‖f x‖) μ := hf_int.norm
      have hf_nonneg : 0 ≤ᵐ[μ] fun x => ‖f x‖ :=
        Filter.Eventually.of_forall fun _ => norm_nonneg _
      have hf_lintegral :
          ∫⁻ x, ENNReal.ofReal (‖f x‖) ∂μ = ENNReal.ofReal (∫ x, ‖f x‖ ∂μ) := by
        simpa using
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf_norm hf_nonneg).symm
      have hf_eLpNorm :
          eLpNorm f 1 μ = ENNReal.ofReal (∫ x, ‖f x‖ ∂μ) := by
        simpa [MeasureTheory.eLpNorm_one_eq_lintegral_enorm, ofReal_norm_eq_enorm]
          using hf_lintegral
      have hf_toReal :
          (eLpNorm f 1 μ).toReal = ∫ x, ‖f x‖ ∂μ := by
        have h_nonneg : 0 ≤ ∫ x, ‖f x‖ ∂μ :=
          integral_nonneg fun _ => norm_nonneg _
        have := congrArg ENNReal.toReal hf_eLpNorm
        simpa [h_nonneg, ENNReal.toReal_ofReal] using this
      -- Obtain the essential supremum bound for `g` with the precise constant.
      have hg_ne_top' : eLpNorm g ∞ μ ≠ ∞ := ne_of_lt hg_fin
      have hg_ne_top : eLpNormEssSup g μ ≠ ∞ :=
        by simpa [eLpNorm, eLpNorm_exponent_top] using hg_ne_top'
      set K := (eLpNorm g ∞ μ).toReal with hK
      have hK_nonneg : 0 ≤ K := by
        simp [K]
      have hK_bound : ∀ᵐ x ∂μ, ‖g x‖ ≤ K := by
        refine (ae_le_eLpNormEssSup (μ := μ) (f := fun x => g x)).mono ?_
        intro x hx
        have hx' : ENNReal.ofReal ‖g x‖ ≤ eLpNormEssSup g μ := by
          simpa [ofReal_norm_eq_enorm] using hx
        have := (ENNReal.ofReal_le_iff_le_toReal hg_ne_top).mp hx'
        simpa [K, eLpNorm, eLpNorm_exponent_top] using this
      -- Compare the product with the majorant `K * ‖f x‖`.
      have hf_meas : AEStronglyMeasurable (fun x => ‖f x‖ * ‖g x‖) μ :=
        (hf_int.aestronglyMeasurable.norm.mul hg_ae.norm)
      have h_mul_le :
          (fun x => ‖f x‖ * ‖g x‖) ≤ᵐ[μ] fun x => K * ‖f x‖ :=
        hK_bound.mono fun x hx =>
          by
            have hf_nonneg' : 0 ≤ ‖f x‖ := norm_nonneg _
            have : ‖f x‖ * ‖g x‖ ≤ ‖f x‖ * K :=
              (mul_le_mul_of_nonneg_left hx hf_nonneg' : _)
            simpa [mul_comm, mul_left_comm, mul_assoc] using this
      have h_mul_abs :
          ∀ᵐ x ∂μ, ‖‖f x‖ * ‖g x‖‖ ≤ K * ‖f x‖ :=
        hK_bound.mono fun x hx =>
          by
            have hf_nonneg' : 0 ≤ ‖f x‖ := norm_nonneg _
            have hg_nonneg' : 0 ≤ ‖g x‖ := norm_nonneg _
            have h_prod_nonneg : 0 ≤ ‖f x‖ * ‖g x‖ :=
              mul_nonneg hf_nonneg' hg_nonneg'
            have h_rhs_nonneg : 0 ≤ K * ‖f x‖ := mul_nonneg hK_nonneg hf_nonneg'
            have : ‖f x‖ * ‖g x‖ ≤ ‖f x‖ * K :=
              (mul_le_mul_of_nonneg_left hx hf_nonneg' : _)
            simpa [Real.norm_of_nonneg h_prod_nonneg, Real.norm_of_nonneg h_rhs_nonneg,
              mul_comm, mul_left_comm, mul_assoc] using this
      have h_majorant : Integrable (fun x => K * ‖f x‖) μ :=
        hf_norm.const_mul K
      have h_prod_int : Integrable (fun x => ‖f x‖ * ‖g x‖) μ :=
        Integrable.mono' h_majorant hf_meas h_mul_abs
      have h_integral_le :=
        integral_mono_ae h_prod_int h_majorant h_mul_le
      have h_integral_const :
          ∫ x, K * ‖f x‖ ∂μ = K * ∫ x, ‖f x‖ ∂μ := by
        simpa [mul_comm] using
          integral_const_mul (μ := μ) (r := K) (f := fun x => ‖f x‖)
      have h_main :
          ∫ x, ‖f x‖ * ‖g x‖ ∂μ ≤ K * ∫ x, ‖f x‖ ∂μ := by
        simpa [h_integral_const] using h_integral_le
      simpa [hf_toReal, K, mul_comm, mul_left_comm, mul_assoc] using h_main
  · rcases hpq with ⟨hp, hq⟩
    subst hp; subst hq
    -- Case `p = ∞`, `q = 1`
    have hg_int : Integrable g μ := by
      simpa [memLp_one_iff_integrable] using hg
    obtain ⟨hf_meas, hf_fin⟩ := hf
    have hf_bound : ∃ C, ∀ᵐ x ∂μ, ‖f x‖ ≤ C := by
      have hf_ne_top' : eLpNorm f ∞ μ ≠ ∞ := ne_of_lt hf_fin
      have hf_ne_top : eLpNormEssSup f μ ≠ ∞ :=
        by simpa [eLpNorm, eLpNorm_exponent_top] using hf_ne_top'
      refine ⟨(eLpNorm f ∞ μ).toReal, ?_⟩
      refine (ae_le_eLpNormEssSup (μ := μ) (f := fun x => f x)).mono ?_
      intro x hx
      have hx' : ENNReal.ofReal ‖f x‖ ≤ eLpNormEssSup f μ := by
        simpa [ofReal_norm_eq_enorm] using hx
      have := (ENNReal.ofReal_le_iff_le_toReal hf_ne_top).mp hx'
      simpa [eLpNorm, eLpNorm_exponent_top] using this
    have hf_ae : AEStronglyMeasurable f μ := hf_meas
    have := by
      have h :=
        holder_inequality_one_infty (μ := μ) (E := F) (F := E)
          (f := g) (g := f) hg_int hf_ae hf_bound
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    refine ⟨?_, ?_⟩
    · obtain ⟨C, hC⟩ := hf_bound
      set C₀ := max C 0
      have hC₀_nonneg : 0 ≤ C₀ := le_max_right _ _
      have hC₀_bound : ∀ᵐ x ∂μ, ‖f x‖ ≤ C₀ :=
        hC.mono fun x hx => le_max_of_le_left hx
      have hg_meas : AEStronglyMeasurable g μ := hg_int.aestronglyMeasurable
      have h_meas : AEStronglyMeasurable (fun x => ‖f x‖ * ‖g x‖) μ :=
        (hf_ae.norm.mul hg_meas.norm)
      have h_dom : ∀ᵐ x ∂μ, ‖‖f x‖ * ‖g x‖‖ ≤ C₀ * ‖g x‖ :=
        hC₀_bound.mono fun x hx =>
          by
            have hf_nonneg : 0 ≤ ‖f x‖ := norm_nonneg _
            have hg_nonneg : 0 ≤ ‖g x‖ := norm_nonneg _
            have h_prod_nonneg : 0 ≤ ‖f x‖ * ‖g x‖ := mul_nonneg hf_nonneg hg_nonneg
            have h_rhs_nonneg : 0 ≤ C₀ * ‖g x‖ := mul_nonneg hC₀_nonneg hg_nonneg
            have h_mul_le : ‖f x‖ * ‖g x‖ ≤ C₀ * ‖g x‖ :=
              (mul_le_mul_of_nonneg_right hx hg_nonneg : _)
            simpa [Real.norm_of_nonneg h_prod_nonneg, Real.norm_of_nonneg h_rhs_nonneg,
              mul_comm, mul_left_comm, mul_assoc] using h_mul_le
      have h_majorant : Integrable (fun x => C₀ * ‖g x‖) μ :=
        hg_int.norm.const_mul C₀
      exact Integrable.mono' h_majorant h_meas h_dom
    · -- Express the L¹ norm of `g` via `eLpNorm`.
      have hg_norm : Integrable (fun x => ‖g x‖) μ := hg_int.norm
      have hg_nonneg : 0 ≤ᵐ[μ] fun x => ‖g x‖ :=
        Filter.Eventually.of_forall fun _ => norm_nonneg _
      have hg_lintegral :
          ∫⁻ x, ENNReal.ofReal (‖g x‖) ∂μ = ENNReal.ofReal (∫ x, ‖g x‖ ∂μ) := by
        simpa using
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg_norm hg_nonneg).symm
      have hg_eLpNorm :
          eLpNorm g 1 μ = ENNReal.ofReal (∫ x, ‖g x‖ ∂μ) := by
        simpa [MeasureTheory.eLpNorm_one_eq_lintegral_enorm, ofReal_norm_eq_enorm]
          using hg_lintegral
      have hg_toReal :
          (eLpNorm g 1 μ).toReal = ∫ x, ‖g x‖ ∂μ := by
        have h_nonneg : 0 ≤ ∫ x, ‖g x‖ ∂μ :=
          integral_nonneg fun _ => norm_nonneg _
        have := congrArg ENNReal.toReal hg_eLpNorm
        simpa [h_nonneg, ENNReal.toReal_ofReal] using this
      -- Obtain the essential supremum bound for `f` with the precise constant.
      have hf_ne_top' : eLpNorm f ∞ μ ≠ ∞ := ne_of_lt hf_fin
      have hf_ne_top : eLpNormEssSup f μ ≠ ∞ :=
        by simpa [eLpNorm, eLpNorm_exponent_top] using hf_ne_top'
      set K := (eLpNorm f ∞ μ).toReal with hK
      have hK_nonneg : 0 ≤ K := by
        simp [K]
      have hK_bound : ∀ᵐ x ∂μ, ‖f x‖ ≤ K := by
        refine (ae_le_eLpNormEssSup (μ := μ) (f := fun x => f x)).mono ?_
        intro x hx
        have hx' : ENNReal.ofReal ‖f x‖ ≤ eLpNormEssSup f μ := by
          simpa [ofReal_norm_eq_enorm] using hx
        have := (ENNReal.ofReal_le_iff_le_toReal hf_ne_top).mp hx'
        simpa [K, eLpNorm, eLpNorm_exponent_top] using this
      -- Compare the product with the majorant `K * ‖g x‖`.
      have hg_meas : AEStronglyMeasurable g μ := hg_int.aestronglyMeasurable
      have h_meas : AEStronglyMeasurable (fun x => ‖f x‖ * ‖g x‖) μ :=
        (hf_ae.norm.mul hg_meas.norm)
      have h_mul_le :
          (fun x => ‖f x‖ * ‖g x‖) ≤ᵐ[μ] fun x => K * ‖g x‖ :=
        hK_bound.mono fun x hx =>
          by
            have hg_nonneg' : 0 ≤ ‖g x‖ := norm_nonneg _
            have : ‖f x‖ * ‖g x‖ ≤ K * ‖g x‖ :=
              (mul_le_mul_of_nonneg_right hx hg_nonneg' : _)
            simpa [mul_comm, mul_left_comm, mul_assoc] using this
      have h_mul_abs :
          ∀ᵐ x ∂μ, ‖‖f x‖ * ‖g x‖‖ ≤ K * ‖g x‖ :=
        hK_bound.mono fun x hx =>
          by
            have hf_nonneg : 0 ≤ ‖f x‖ := norm_nonneg _
            have hg_nonneg' : 0 ≤ ‖g x‖ := norm_nonneg _
            have h_prod_nonneg : 0 ≤ ‖f x‖ * ‖g x‖ :=
              mul_nonneg hf_nonneg hg_nonneg'
            have h_rhs_nonneg : 0 ≤ K * ‖g x‖ :=
              mul_nonneg hK_nonneg hg_nonneg'
            have : ‖f x‖ * ‖g x‖ ≤ K * ‖g x‖ :=
              (mul_le_mul_of_nonneg_right hx hg_nonneg' : _)
            simpa [Real.norm_of_nonneg h_prod_nonneg, Real.norm_of_nonneg h_rhs_nonneg,
              mul_comm, mul_left_comm, mul_assoc] using this
      have h_majorant : Integrable (fun x => K * ‖g x‖) μ :=
        hg_norm.const_mul K
      have h_prod_int : Integrable (fun x => ‖f x‖ * ‖g x‖) μ :=
        Integrable.mono' h_majorant h_meas h_mul_abs
      have h_integral_le :=
        integral_mono_ae h_prod_int h_majorant h_mul_le
      have h_integral_const :
          ∫ x, K * ‖g x‖ ∂μ = K * ∫ x, ‖g x‖ ∂μ := by
        simpa [mul_comm] using
          integral_const_mul (μ := μ) (r := K) (f := fun x => ‖g x‖)
      have h_main :
          ∫ x, ‖f x‖ * ‖g x‖ ∂μ ≤ K * ∫ x, ‖g x‖ ∂μ := by
        simpa [h_integral_const] using h_integral_le
      simpa [hg_toReal, K, mul_comm, mul_left_comm, mul_assoc] using h_main
  · rcases hpq with ⟨hp, hp_top, hq, hq_top, hpq'⟩
    -- Case `1 < p, q < ∞`
    set pr := p.toReal with hpr
    set qr := q.toReal with hqr
    have hp_ne_top : p ≠ ∞ := ne_of_lt hp_top
    have hq_ne_top : q ≠ ∞ := ne_of_lt hq_top
    have hp_pos : 0 < p :=
      lt_of_le_of_lt (show (0 : ℝ≥0∞) ≤ 1 by simp) hp
    have hq_pos : 0 < q :=
      lt_of_le_of_lt (show (0 : ℝ≥0∞) ≤ 1 by simp) hq
    have hp_ne_zero : p ≠ 0 := ne_of_gt hp_pos
    have hq_ne_zero : q ≠ 0 := ne_of_gt hq_pos
    have hp_real_gt_one : 1 < pr := by
      have h₁ : (1 : ℝ≥0∞) ≠ ∞ := by simp
      have := (ENNReal.toReal_lt_toReal h₁ hp_ne_top).2 hp
      simpa [hpr] using this
    have hq_real_gt_one : 1 < qr := by
      have h₁ : (1 : ℝ≥0∞) ≠ ∞ := by simp
      have := (ENNReal.toReal_lt_toReal h₁ hq_ne_top).2 hq
      simpa [hqr] using this
    have pr_pos : 0 < pr := zero_lt_one.trans hp_real_gt_one
    have qr_pos : 0 < qr := zero_lt_one.trans hq_real_gt_one
    have pr_nonneg : 0 ≤ pr := pr_pos.le
    have qr_nonneg : 0 ≤ qr := qr_pos.le
    have hp_inv_ne_top : 1 / p ≠ ∞ := by
      simpa [one_div] using (ENNReal.inv_ne_top).2 hp_ne_zero
    have hq_inv_ne_top : 1 / q ≠ ∞ := by
      simpa [one_div] using (ENNReal.inv_ne_top).2 hq_ne_zero
    have hp_inv_toReal : (1 / p).toReal = 1 / pr := by
      simp [one_div, hpr, ENNReal.toReal_inv]
    have hq_inv_toReal : (1 / q).toReal = 1 / qr := by
      simp [one_div, hqr, ENNReal.toReal_inv]
    have hpq_real_sum : 1 / pr + 1 / qr = 1 := by
      have h := congrArg ENNReal.toReal hpq'
      have hsum_symm : (1 / p).toReal + (1 / q).toReal = (1 / p + 1 / q).toReal :=
        (ENNReal.toReal_add hp_inv_ne_top hq_inv_ne_top).symm
      have h_toReal_add : (1 / p).toReal + (1 / q).toReal = 1 :=
        hsum_symm.trans h
      simpa [hp_inv_toReal, hq_inv_toReal] using h_toReal_add
    have hpq_real_sum' : pr⁻¹ + qr⁻¹ = 1 := by
      simpa [one_div] using hpq_real_sum
    have hpq_real : pr.HolderConjugate qr :=
      (Real.holderConjugate_iff).2 ⟨hp_real_gt_one, hpq_real_sum'⟩
    have hp_ofReal : ENNReal.ofReal pr = p := by
      simp [hpr, hp_ne_top]
    have hq_ofReal : ENNReal.ofReal qr = q := by
      simp [hqr, hq_ne_top]
    have hf_norm : MemLp (fun x => ‖f x‖) p μ := hf.norm
    have hg_norm : MemLp (fun x => ‖g x‖) q μ := hg.norm
    have hf_norm_real : MemLp (fun x => ‖f x‖) (ENNReal.ofReal pr) μ := by
      simpa [hp_ofReal] using hf_norm
    have hg_norm_real : MemLp (fun x => ‖g x‖) (ENNReal.ofReal qr) μ := by
      simpa [hq_ofReal] using hg_norm
    have hf_nonneg : 0 ≤ᵐ[μ] fun x => ‖f x‖ :=
      Filter.Eventually.of_forall fun _ => norm_nonneg _
    have hg_nonneg : 0 ≤ᵐ[μ] fun x => ‖g x‖ :=
      Filter.Eventually.of_forall fun _ => norm_nonneg _
    have hf_pow_integrable : Integrable (fun x => ‖f x‖ ^ pr) μ :=
      hf.integrable_norm_rpow hp_ne_zero hp_ne_top
    have hg_pow_integrable : Integrable (fun x => ‖g x‖ ^ qr) μ :=
      hg.integrable_norm_rpow hq_ne_zero hq_ne_top
    have hf_pow_nonneg : 0 ≤ᵐ[μ] fun x => ‖f x‖ ^ pr :=
      Filter.Eventually.of_forall fun _ => Real.rpow_nonneg (norm_nonneg _) _
    have hg_pow_nonneg : 0 ≤ᵐ[μ] fun x => ‖g x‖ ^ qr :=
      Filter.Eventually.of_forall fun _ => Real.rpow_nonneg (norm_nonneg _) _
    haveI : ENNReal.HolderConjugate p q :=
      ⟨by simpa [one_div] using hpq'⟩
    have h_prod_int : Integrable (fun x => ‖f x‖ * ‖g x‖) μ := by
      simpa [Pi.mul_apply] using
        (MemLp.integrable_mul (p := p) (q := q) hf_norm hg_norm)
    have hf_lintegral :
        ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ pr) ∂μ =
            ENNReal.ofReal (∫ x, ‖f x‖ ^ pr ∂μ) := by
      simpa using
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf_pow_integrable
            hf_pow_nonneg).symm
    have hg_lintegral :
        ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ qr) ∂μ =
            ENNReal.ofReal (∫ x, ‖g x‖ ^ qr ∂μ) := by
      simpa using
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg_pow_integrable
            hg_pow_nonneg).symm
    have hf_integral_eq :
        ∫⁻ x, ‖f x‖ₑ ^ pr ∂μ = ENNReal.ofReal (∫ x, ‖f x‖ ^ pr ∂μ) := by
      have h :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf_pow_integrable
            hf_pow_nonneg).symm
      have hfun :
          (fun x => ENNReal.ofReal (‖f x‖ ^ pr)) = fun x => ‖f x‖ₑ ^ pr := by
        funext x
        simpa [ofReal_norm_eq_enorm]
          using (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) pr_nonneg).symm
      simpa [hfun] using h
    have hg_integral_eq :
        ∫⁻ x, ‖g x‖ₑ ^ qr ∂μ = ENNReal.ofReal (∫ x, ‖g x‖ ^ qr ∂μ) := by
      have h :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg_pow_integrable
            hg_pow_nonneg).symm
      have hfun :
          (fun x => ENNReal.ofReal (‖g x‖ ^ qr)) = fun x => ‖g x‖ₑ ^ qr := by
        funext x
        simpa [ofReal_norm_eq_enorm]
          using (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) qr_nonneg).symm
      simpa [hfun] using h
    set Af := ∫⁻ x, ‖f x‖ₑ ^ pr ∂μ with hAf
    set Ag := ∫⁻ x, ‖g x‖ₑ ^ qr ∂μ with hAg
    have hAf_eq : Af = ENNReal.ofReal (∫ x, ‖f x‖ ^ pr ∂μ) := by
      simpa [hAf] using hf_integral_eq
    have hAg_eq : Ag = ENNReal.ofReal (∫ x, ‖g x‖ ^ qr ∂μ) := by
      simpa [hAg] using hg_integral_eq
    have hAf_ne_top : Af ≠ ∞ := by
      simp [hAf_eq]
    have hAg_ne_top : Ag ≠ ∞ := by
      simp [hAg_eq]
    have hf_integral_nonneg : 0 ≤ ∫ x, ‖f x‖ ^ pr ∂μ :=
      integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
    have hAf_toReal : Af.toReal = ∫ x, ‖f x‖ ^ pr ∂μ := by
      have := congrArg ENNReal.toReal hAf_eq
      simpa [hf_integral_nonneg, ENNReal.toReal_ofReal] using this
    have hg_integral_nonneg : 0 ≤ ∫ x, ‖g x‖ ^ qr ∂μ :=
      integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
    have hAg_toReal : Ag.toReal = ∫ x, ‖g x‖ ^ qr ∂μ := by
      have := congrArg ENNReal.toReal hAg_eq
      simpa [hg_integral_nonneg, ENNReal.toReal_ofReal] using this
    have hf_norm_rpow : (∫ x, ‖f x‖ ^ pr ∂μ) ^ (1 / pr) =
        (eLpNorm f p μ).toReal := by
      have hf_eLpNorm :=
        eLpNorm_eq_lintegral_rpow_enorm (μ := μ) (f := f) hp_ne_zero hp_ne_top
      have h := congrArg ENNReal.toReal hf_eLpNorm
      have h_power : (Af ^ (1 / pr)).toReal = Af.toReal ^ (1 / pr) := by
        simpa using (ENNReal.toReal_rpow Af (1 / pr)).symm
      have h_main : (Af ^ (1 / pr)).toReal = (eLpNorm f p μ).toReal := by
        simpa [hAf] using h.symm
      have h_lhs : (Af ^ (1 / pr)).toReal =
          (∫ x, ‖f x‖ ^ pr ∂μ) ^ (1 / pr) := by
        simpa [hAf_toReal] using h_power
      exact h_lhs.symm.trans h_main
    have hg_norm_rpow : (∫ x, ‖g x‖ ^ qr ∂μ) ^ (1 / qr) =
        (eLpNorm g q μ).toReal := by
      have hg_eLpNorm :=
        eLpNorm_eq_lintegral_rpow_enorm (μ := μ) (f := g) hq_ne_zero hq_ne_top
      have h := congrArg ENNReal.toReal hg_eLpNorm
      have h_power : (Ag ^ (1 / qr)).toReal = Ag.toReal ^ (1 / qr) := by
        simpa using (ENNReal.toReal_rpow Ag (1 / qr)).symm
      have h_main : (Ag ^ (1 / qr)).toReal = (eLpNorm g q μ).toReal := by
        simpa [hAg] using h.symm
      have h_lhs : (Ag ^ (1 / qr)).toReal =
          (∫ x, ‖g x‖ ^ qr ∂μ) ^ (1 / qr) := by
        simpa [hAg_toReal] using h_power
      exact h_lhs.symm.trans h_main
    have hf_norm_rpow_inv : (∫ x, ‖f x‖ ^ pr ∂μ) ^ pr⁻¹ =
        (eLpNorm f p μ).toReal := by
      simpa [one_div] using hf_norm_rpow
    have hg_norm_rpow_inv : (∫ x, ‖g x‖ ^ qr ∂μ) ^ qr⁻¹ =
        (eLpNorm g q μ).toReal := by
      simpa [one_div] using hg_norm_rpow
    have h_main :=
      MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := pr) (q := qr)
        hpq_real hf_nonneg hg_nonneg hf_norm_real hg_norm_real
    have h_final :
        ∫ x, ‖f x‖ * ‖g x‖ ∂μ ≤
          (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal := by
      simpa [hf_norm_rpow_inv, hg_norm_rpow_inv] using h_main
    exact ⟨h_prod_int, h_final⟩

end HolderGeneral

theorem memLp_mul_of_memLp_conjugate
    (p q : ℝ≥0∞)
    (hpq : IsConjugateExponent p q)
    (f : α → ℝ) (g : α → ℝ)
    (hf : MemLp f p μ)
    (hg : MemLp g q μ) :
    Integrable (fun x => f x * g x) μ := by
  obtain ⟨h_int, -⟩ :=
    holder_inequality (μ := μ) (p := p) (q := q) hpq f g hf hg
  refine ⟨hf.aestronglyMeasurable.mul hg.aestronglyMeasurable, ?_⟩
  have h_finite : HasFiniteIntegral (fun x => ‖f x‖ * ‖g x‖) μ :=
    h_int.hasFiniteIntegral
  have h_finite' : HasFiniteIntegral (fun x => f x * g x) μ :=
    h_finite.congr' <|
      (Filter.Eventually.of_forall fun x => by
        simp [Real.norm_eq_abs, abs_mul])
  simpa using h_finite'

lemma eLpNorm_toReal_pos_of_ae_pos
    (p : ℝ≥0∞) (hp : 1 < p) (f : α → ℝ) (hf : MemLp f p μ)
    (hf_pos : ∀ᵐ x ∂μ, 0 < f x) (hμ_pos : μ Set.univ ≠ 0) :
    0 < (eLpNorm f p μ).toReal := by
  have hp_ne_zero : p ≠ 0 := by
    exact ne_of_gt <| (zero_lt_one.trans hp)
  have h_nonneg : 0 ≤ (eLpNorm f p μ).toReal := ENNReal.toReal_nonneg
  have h_ne : (eLpNorm f p μ).toReal ≠ 0 := by
    intro hzero
    have hnorm_ne_top : eLpNorm f p μ ≠ ∞ := ne_of_lt hf.2
    have hzero_cases := (ENNReal.toReal_eq_zero_iff (eLpNorm f p μ)).mp hzero
    have hnorm_zero : eLpNorm f p μ = 0 := by
      rcases hzero_cases with hzero' | htop
      · exact hzero'
      · exact (hnorm_ne_top htop).elim
    have hf_zero : f =ᵐ[μ] 0 :=
      (eLpNorm_eq_zero_iff (μ := μ) (f := f) (p := p) hf.1 hp_ne_zero).1 hnorm_zero
    have hf_ne_zero : ∀ᵐ x ∂μ, f x ≠ 0 :=
      hf_pos.mono fun x hx => ne_of_gt hx
    have hf_false : (∀ᵐ x ∂μ, False) :=
      (hf_ne_zero.and hf_zero).mono fun x hx => (hx.1 hx.2)
    have hf_false' : μ Set.univ = 0 := by
      have : μ {x | ¬False} = 0 := ae_iff.mp hf_false
      simp only [not_false_eq_true, Set.setOf_true] at this
      exact this
    exact (hμ_pos hf_false')
  exact lt_of_le_of_ne h_nonneg (by simpa [eq_comm] using h_ne)

/--
**Conjugate exponent computation.**

Compute the conjugate exponent explicitly from p.
-/
theorem conjugate_exponent_formula
    (p : ℝ≥0∞)
    (hp : 1 < p) (hp_top : p < ∞) :
    ∃ q : ℝ≥0∞, IsConjugateExponent p q ∧
    q = ENNReal.ofReal (p.toReal / (p.toReal - 1)) := by
  have hp_ne_top : p ≠ ∞ := ne_of_lt hp_top
  set pr := p.toReal with hpr
  have hpr_gt_one : 1 < pr := by
    have := (ENNReal.toReal_lt_toReal (by simp) hp_ne_top).2 hp
    simpa [hpr] using this
  have hpr_pos : 0 < pr := zero_lt_one.trans hpr_gt_one
  have hpr_ne_zero : pr ≠ 0 := ne_of_gt hpr_pos
  have hpr_sub_pos : 0 < pr - 1 := sub_pos.2 hpr_gt_one
  have hpr_sub_ne_zero : pr - 1 ≠ 0 := ne_of_gt hpr_sub_pos
  set qrReal := pr / (pr - 1) with hqrReal
  set q : ℝ≥0∞ := ENNReal.ofReal qrReal with hq
  have hq_ne_top : q ≠ ∞ := by simp [hq]
  have hq_pos_real : 0 < qrReal := div_pos hpr_pos hpr_sub_pos
  have hq_real_gt_one : 1 < qrReal := by
    have hdiff : qrReal - 1 = 1 / (pr - 1) := by
      field_simp [hqrReal, hpr_ne_zero, hpr_sub_ne_zero]
    have hpos' : 0 < qrReal - 1 := by
      have h := one_div_pos.2 hpr_sub_pos
      exact hdiff.symm ▸ h
    exact sub_pos.mp hpos'
  have hq_gt_one : 1 < q := by
    have h := (ENNReal.ofReal_lt_ofReal_iff hq_pos_real).2 hq_real_gt_one
    simpa [hq] using h
  have hq_lt_top : q < ∞ := by simp [hq]
  have hp_ofReal : ENNReal.ofReal pr = p := by
    simp [hp_ne_top, hpr]
  have hp_inv : p⁻¹ = ENNReal.ofReal (1 / pr) := by
    have := (ENNReal.ofReal_inv_of_pos hpr_pos).symm
    simpa [hp_ofReal, one_div] using this
  have hq_inv : q⁻¹ = ENNReal.ofReal (1 / qrReal) := by
    have := (ENNReal.ofReal_inv_of_pos hq_pos_real).symm
    simpa [hq, one_div] using this
  have hsum_real : 1 / pr + 1 / qrReal = 1 := by
    field_simp [hqrReal, hpr_ne_zero, hpr_sub_ne_zero]
  have hsum_real_inv : pr⁻¹ + qrReal⁻¹ = 1 := by simpa [one_div] using hsum_real
  have hsum : 1 / p + 1 / q = 1 := by
    have h1 : 0 ≤ 1 / pr := by positivity
    have h2 : 0 ≤ 1 / qrReal := by positivity
    calc
      1 / p + 1 / q = p⁻¹ + q⁻¹ := by simp [one_div]
      _ = ENNReal.ofReal (1 / pr) + ENNReal.ofReal (1 / qrReal) := by simp [hp_inv, hq_inv]
      _ = ENNReal.ofReal (1 / pr + 1 / qrReal) := (ENNReal.ofReal_add h1 h2).symm
      _ = ENNReal.ofReal 1 := by simp [hsum_real_inv]
      _ = 1 := by simp
  refine ⟨q, ?_, by simp [hq, hpr, hqrReal]⟩
  refine Or.inr ?_
  refine Or.inr ?_
  exact ⟨hp, hp_top, hq_gt_one, hq_lt_top, hsum⟩

section MinkowskiAux

variable {β : Type*} [MeasurableSpace β]
variable {ν : Measure β}

/--
Auxiliary estimate used in the proof of Minkowski's integral inequality.  It bounds the pairing
between the norm of a fibrewise integral and a dual element of `L^q`.
-/
lemma holder_kernel_pairing_bound
    [NormedSpace ℝ E] [SFinite μ] [SFinite ν]
    (p q : ℝ≥0∞) (hpq : IsConjugateExponent p q)
    {F : α → β → E} {φ : α → ℝ}
    (hF_meas : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν))
    (hF_prod : Integrable (Function.uncurry F) (μ.prod ν))
    (hF_memLp : ∀ᵐ y ∂ν, MemLp (fun x => F x y) p μ)
    (hF_norm : Integrable (fun y => (eLpNorm (fun x => F x y) p μ).toReal) ν)
    (hφ_mem : MemLp φ q μ) :
    |∫ x, ‖∫ y, F x y ∂ν‖ * φ x ∂μ|
      ≤ (eLpNorm φ q μ).toReal *
        ∫ y, (eLpNorm (fun x => F x y) p μ).toReal ∂ν := by
  -- Unpack the integrability information furnished by the product assumptions.
  have h_prod_info :=
    (integrable_prod_iff (μ := μ) (ν := ν)
        (f := Function.uncurry F) hF_meas).mp hF_prod
  have h_integrable_slices :
      ∀ᵐ x ∂μ, Integrable (fun y => F x y) ν := by
    simpa [Function.uncurry] using h_prod_info.1
  have h_integrable_norm :
      Integrable (fun x => ∫ y, ‖F x y‖ ∂ν) μ := by
    simpa [Function.uncurry] using h_prod_info.2
  -- Pointwise control of the pairing integrand by a simpler positive majorant.
  have h_pointwise_bound :
      (fun x => |‖∫ y, F x y ∂ν‖ * φ x|)
        ≤ᵐ[μ] fun x => (∫ y, ‖F x y‖ ∂ν) * |φ x| := by
    refine h_integrable_slices.mono ?_
    intro x _
    have hnorm_le :
        ‖∫ y, F x y ∂ν‖ ≤ ∫ y, ‖F x y‖ ∂ν := by
      simpa using (norm_integral_le_integral_norm (μ := ν) (f := fun y => F x y))
    have h_abs_mul :
        |‖∫ y, F x y ∂ν‖ * φ x|
          = ‖∫ y, F x y ∂ν‖ * |φ x| := by
      have h_nonneg : 0 ≤ ‖∫ y, F x y ∂ν‖ := norm_nonneg _
      simp [abs_mul, abs_of_nonneg h_nonneg]
    have h_nonneg_abs : 0 ≤ |φ x| := abs_nonneg _
    have h_mul_le :
        ‖∫ y, F x y ∂ν‖ * |φ x|
          ≤ (∫ y, ‖F x y‖ ∂ν) * |φ x| :=
      mul_le_mul_of_nonneg_right hnorm_le h_nonneg_abs
    simpa [h_abs_mul]
  -- Apply Hölder to each fibre to control the inner integral with respect to `μ`.
  have h_holder_fibre :
      ∀ᵐ y ∂ν,
        Integrable (fun x => ‖F x y‖ * |φ x|) μ ∧
          ∫ x, ‖F x y‖ * |φ x| ∂μ
            ≤ (eLpNorm (fun x => F x y) p μ).toReal * (eLpNorm φ q μ).toReal := by
    refine hF_memLp.mono ?_
    intro y hy
    have h_holder :=
      holder_inequality (μ := μ) (p := p) (q := q) hpq
        (f := fun x => F x y) (g := fun x => φ x)
        hy hφ_mem
    constructor
    · simpa using h_holder.1
    · simpa using h_holder.2
  have h_holder_integrable :
      ∀ᵐ y ∂ν, Integrable (fun x => ‖F x y‖ * |φ x|) μ :=
    h_holder_fibre.mono fun _ hy => hy.1
  have h_holder_bound' :
      (fun y => ∫ x, ‖F x y‖ * |φ x| ∂μ)
        ≤ᵐ[ν]
          fun y =>
            (eLpNorm (fun x => F x y) p μ).toReal * (eLpNorm φ q μ).toReal :=
    h_holder_fibre.mono fun _ hy => hy.2
  have hφ_norm_nonneg : 0 ≤ (eLpNorm φ q μ).toReal := ENNReal.toReal_nonneg
  have h_bound_integrable :
      Integrable (fun y => (eLpNorm (fun x => F x y) p μ).toReal) ν := hF_norm
  have h_bound_integrable' :
      Integrable (fun y =>
        (eLpNorm (fun x => F x y) p μ).toReal * (eLpNorm φ q μ).toReal) ν := by
    simpa [mul_comm] using
      (h_bound_integrable.mul_const ((eLpNorm φ q μ).toReal))
  have h_integral_norm_nonneg :
      0 ≤ ∫ y, (eLpNorm (fun x => F x y) p μ).toReal ∂ν := by
    have h_nonneg : 0 ≤ᵐ[ν] fun y => (eLpNorm (fun x => F x y) p μ).toReal :=
      Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg
    exact integral_nonneg_of_ae h_nonneg
  have h_rhs_nonneg :
      0 ≤ (eLpNorm φ q μ).toReal *
          ∫ y, (eLpNorm (fun x => F x y) p μ).toReal ∂ν :=
    mul_nonneg hφ_norm_nonneg h_integral_norm_nonneg
  -- Package the nonnegative kernel used for the Fubini step.
  set G : α → β → ℝ := fun x y => ‖F x y‖ * |φ x| with hG_def
  have hG_nonneg : ∀ x y, 0 ≤ G x y := by
    intro x y
    have h₁ : 0 ≤ ‖F x y‖ := norm_nonneg _
    have h₂ : 0 ≤ |φ x| := abs_nonneg _
    simpa [G, hG_def, mul_comm] using mul_nonneg h₁ h₂
  -- Express the iterated integral of the kernel via Fubini.
  have hG_integrable : Integrable (Function.uncurry G) (μ.prod ν) := by
    -- First, record that the kernel is almost everywhere strongly measurable.
    have hF_norm_aesm :
        AEStronglyMeasurable
          (fun z : α × β => ‖F z.1 z.2‖)
          (μ.prod ν) := hF_meas.norm
    have hφ_aesm : AEStronglyMeasurable φ μ := hφ_mem.aestronglyMeasurable
    have hφ_prod_aesm :
        AEStronglyMeasurable (fun z : α × β => |φ z.1|) (μ.prod ν) := by
      simpa [Real.norm_eq_abs] using (hφ_aesm.comp_fst).norm
    have hG_aesm :
        AEStronglyMeasurable (Function.uncurry G) (μ.prod ν) := by
      simpa [Function.uncurry, G, hG_def]
        using hF_norm_aesm.mul hφ_prod_aesm
    -- Convert the slice-wise lintegral into a real integral using nonnegativity.
    have h_lintegral_eq :
        ∫⁻ y, ∫⁻ x, ENNReal.ofReal (G x y) ∂μ ∂ν
          = ∫⁻ y, ENNReal.ofReal (∫ x, G x y ∂μ) ∂ν := by
      refine lintegral_congr_ae ?_
      filter_upwards [h_holder_integrable] with y hy
      have h_nonneg : 0 ≤ᵐ[μ] fun x => G x y :=
        Filter.Eventually.of_forall fun x => hG_nonneg x y
      have h_eq :=
        MeasureTheory.ofReal_integral_eq_lintegral_ofReal hy h_nonneg
      simpa [Function.uncurry, G, hG_def] using h_eq.symm
    -- Use the Hölder bound to control the iterated lintegral.
    have h_lintegral_bound :
        ∫⁻ y, ∫⁻ x, ENNReal.ofReal (G x y) ∂μ ∂ν
          ≤ ∫⁻ y,
              ENNReal.ofReal
                ((eLpNorm (fun x => F x y) p μ).toReal *
                  (eLpNorm φ q μ).toReal) ∂ν := by
      have h_ofReal_bound :
          (fun y => ENNReal.ofReal (∫ x, G x y ∂μ))
            ≤ᵐ[ν]
              fun y =>
                ENNReal.ofReal
                  ((eLpNorm (fun x => F x y) p μ).toReal *
                    (eLpNorm φ q μ).toReal) :=
        h_holder_bound'.mono fun y hy => by
          exact ENNReal.ofReal_le_ofReal hy
      have := lintegral_mono_ae h_ofReal_bound
      simpa [h_lintegral_eq]
        using this
    -- The dominating function on the right-hand side is integrable, hence finite.
    have h_bound_nonneg :
        0 ≤ᵐ[ν]
            fun y =>
              (eLpNorm (fun x => F x y) p μ).toReal * (eLpNorm φ q μ).toReal :=
      Filter.Eventually.of_forall fun y =>
        by
          have h1 : 0 ≤ (eLpNorm (fun x => F x y) p μ).toReal :=
            ENNReal.toReal_nonneg
          have h2 : 0 ≤ (eLpNorm φ q μ).toReal :=
            ENNReal.toReal_nonneg
          exact mul_nonneg h1 h2
    have h_bound_lintegral_lt_top :
        ∫⁻ y,
            ENNReal.ofReal
              ((eLpNorm (fun x => F x y) p μ).toReal * (eLpNorm φ q μ).toReal) ∂ν <
            ∞ := by
      have h_eq :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
            h_bound_integrable' h_bound_nonneg).symm
      simp [h_eq]
    -- Combine the estimates to obtain finiteness of the product lintegral.
    have h_prod_lintegral_lt_top :
        ∫⁻ z, ENNReal.ofReal (Function.uncurry G z) ∂μ.prod ν < ∞ := by
      have h_ofReal_aemeas :
          AEMeasurable (fun z : α × β => ENNReal.ofReal (G z.1 z.2)) (μ.prod ν) :=
        (hG_aesm.aemeasurable).ennreal_ofReal
      have h_prod_eq :
          ∫⁻ z, ENNReal.ofReal (G z.1 z.2) ∂μ.prod ν
            = ∫⁻ y, ∫⁻ x, ENNReal.ofReal (G x y) ∂μ ∂ν :=
        MeasureTheory.lintegral_prod_symm (μ := μ) (ν := ν)
          (f := fun z : α × β => ENNReal.ofReal (G z.1 z.2)) h_ofReal_aemeas
      have h_iter_lt_top :
          ∫⁻ y, ∫⁻ x, ENNReal.ofReal (G x y) ∂μ ∂ν < ∞ :=
        lt_of_le_of_lt h_lintegral_bound h_bound_lintegral_lt_top
      have h_prod_lt_top :
          ∫⁻ z, ENNReal.ofReal (G z.1 z.2) ∂μ.prod ν < ∞ := by
        exact h_prod_eq ▸ h_iter_lt_top
      simpa [Function.uncurry]
        using h_prod_lt_top
    -- Assemble the integrability statement.
    have h_norm_lintegral_eq :
        ∫⁻ z, ‖Function.uncurry G z‖ₑ ∂μ.prod ν
          = ∫⁻ z, ENNReal.ofReal (Function.uncurry G z) ∂μ.prod ν := by
      refine lintegral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro z
      have hz_nonneg : 0 ≤ Function.uncurry G z := hG_nonneg z.1 z.2
      have hz_abs : |Function.uncurry G z| = Function.uncurry G z :=
        abs_of_nonneg hz_nonneg
      calc
        ‖Function.uncurry G z‖ₑ
            = ENNReal.ofReal ‖Function.uncurry G z‖ := by
              simpa using (ofReal_norm_eq_enorm (Function.uncurry G z)).symm
        _ = ENNReal.ofReal (Function.uncurry G z) := by
              simp [Real.norm_eq_abs, hz_abs]
    have h_hasFiniteIntegral :
        HasFiniteIntegral (Function.uncurry G) (μ.prod ν) := by
      simpa [HasFiniteIntegral, h_norm_lintegral_eq]
        using h_prod_lintegral_lt_top
    exact ⟨hG_aesm, h_hasFiniteIntegral⟩
  have h_integral_swap :
      ∫ x, ∫ y, G x y ∂ν ∂μ = ∫ y, ∫ x, G x y ∂μ ∂ν := by
    have hG_meas :
        AEStronglyMeasurable (Function.uncurry G) (μ.prod ν) :=
      hG_integrable.aestronglyMeasurable
    simpa [Function.uncurry, G, hG_def]
      using
        MeasureTheory.integral_integral_swap
          (μ := μ) (ν := ν) (f := fun x y => G x y)
          hG_integrable
  -- Control the integral of the pairing using the positive kernel `G`.
  set g : α → ℝ := fun x => ‖∫ y, F x y ∂ν‖ * φ x
  set majorant : α → ℝ := fun x => ∫ y, G x y ∂ν
  have h_majorant_integrable : Integrable majorant μ :=
    hG_integrable.integral_prod_left
  have h_majorant_nonneg : 0 ≤ᵐ[μ] majorant :=
    Filter.Eventually.of_forall fun x => by
      have h_const_nonneg : 0 ≤ |φ x| := abs_nonneg _
      have h_integrand_nonneg : ∀ y, 0 ≤ G x y := fun y => by
        have h_norm_nonneg : 0 ≤ ‖F x y‖ := norm_nonneg _
        simpa [G, hG_def, mul_comm, mul_left_comm, mul_assoc]
          using mul_nonneg h_norm_nonneg h_const_nonneg
      have h_nonneg : 0 ≤ ∫ y, G x y ∂ν :=
        integral_nonneg fun y => h_integrand_nonneg y
      simpa [majorant]
        using h_nonneg
  have h_majorant_ae_eq :
      majorant =ᵐ[μ]
        fun x => (∫ y, ‖F x y‖ ∂ν) * |φ x| := by
    refine h_integrable_slices.mono ?_
    intro x hx
    have h_const_mul :
        ∫ y, G x y ∂ν
          = |φ x| * ∫ y, ‖F x y‖ ∂ν := by
      simpa [majorant, G, hG_def, mul_comm, mul_left_comm, mul_assoc]
        using integral_const_mul (μ := ν) (r := |φ x|)
          (f := fun y => ‖F x y‖)
    simpa [majorant, G, hG_def, mul_comm, mul_left_comm, mul_assoc]
      using h_const_mul
  have h_abs_le_majorant :
      ∀ᵐ x ∂μ, |g x| ≤ majorant x := by
    filter_upwards [h_pointwise_bound, h_majorant_ae_eq] with x hx_bound hx_eq
    have hx_bound' :
        |g x| ≤ (∫ y, ‖F x y‖ ∂ν) * |φ x| := by
      simpa [g, mul_comm, mul_left_comm, mul_assoc] using hx_bound
    have hx_majorant :
        (∫ y, ‖F x y‖ ∂ν) * |φ x| = majorant x := by
      simpa using hx_eq.symm
    simpa [hx_majorant] using hx_bound'
  -- Establish integrability of the pairing integrand via domination by `majorant`.
  have h_g_aesm : AEStronglyMeasurable g μ := by
    have h_intF : Integrable (fun x => ∫ y, F x y ∂ν) μ :=
      hF_prod.integral_prod_left
    have h_intF_norm :
        AEStronglyMeasurable (fun x => ‖∫ y, F x y ∂ν‖) μ :=
      (h_intF.aestronglyMeasurable.norm)
    have hφ_aesm' : AEStronglyMeasurable φ μ := hφ_mem.aestronglyMeasurable
    exact h_intF_norm.mul hφ_aesm'
  have h_g_integrable : Integrable g μ :=
    Integrable.mono' h_majorant_integrable h_g_aesm
      (h_abs_le_majorant.mono fun _ hx => by
        simpa [Real.norm_eq_abs] using hx)
  -- Pass to absolute values and compare with the iterated integral of `G`.
  have h_abs_integral_le_majorant :
      |∫ x, g x ∂μ| ≤ ∫ x, majorant x ∂μ := by
    calc
      |∫ x, g x ∂μ| ≤ ∫ x, |g x| ∂μ :=
        by
          simpa using
            (abs_integral_le_integral_abs (μ := μ) (f := g))
      _ ≤ ∫ x, majorant x ∂μ :=
        integral_mono_ae (μ := μ)
          (f := fun x => |g x|) (g := majorant)
          h_g_integrable.abs h_majorant_integrable
          (h_abs_le_majorant.mono fun _ hx => hx)
  -- Rewrite the majorant integral using Fubini and bound it by Hölder.
  have h_majorant_eq : ∫ x, majorant x ∂μ = ∫ y, ∫ x, G x y ∂μ ∂ν := by
    simpa [majorant]
      using h_integral_swap
  have h_inner_integrable :
      Integrable (fun y => ∫ x, G x y ∂μ) ν :=
    hG_integrable.integral_prod_right
  have h_holder_bound_integral :
      ∫ y, ∫ x, G x y ∂μ ∂ν
        ≤ ∫ y,
            (eLpNorm (fun x => F x y) p μ).toReal * (eLpNorm φ q μ).toReal ∂ν :=
    integral_mono_ae (μ := ν)
      (f := fun y => ∫ x, G x y ∂μ)
      (g := fun y =>
        (eLpNorm (fun x => F x y) p μ).toReal * (eLpNorm φ q μ).toReal)
      h_inner_integrable h_bound_integrable'
      h_holder_bound'
  have h_majorant_bound :
      ∫ x, majorant x ∂μ
        ≤ (eLpNorm φ q μ).toReal *
            ∫ y, (eLpNorm (fun x => F x y) p μ).toReal ∂ν := by
    have h_const_mul :
        ∫ y, (eLpNorm (fun x => F x y) p μ).toReal * (eLpNorm φ q μ).toReal ∂ν
          = (eLpNorm φ q μ).toReal * ∫ y, (eLpNorm (fun x => F x y) p μ).toReal ∂ν := by
      simpa [mul_comm, mul_left_comm, mul_assoc]
        using integral_const_mul (μ := ν)
          (r := (eLpNorm φ q μ).toReal)
          (f := fun y => (eLpNorm (fun x => F x y) p μ).toReal)
    calc
      ∫ x, majorant x ∂μ
          = ∫ y, ∫ x, G x y ∂μ ∂ν := h_majorant_eq
      _ ≤ ∫ y,
            (eLpNorm (fun x => F x y) p μ).toReal * (eLpNorm φ q μ).toReal ∂ν :=
        h_holder_bound_integral
      _ = (eLpNorm φ q μ).toReal *
            ∫ y, (eLpNorm (fun x => F x y) p μ).toReal ∂ν :=
        h_const_mul
  -- Combine the estimates.
  have h_abs_integral_final :
      |∫ x, g x ∂μ|
        ≤ (eLpNorm φ q μ).toReal *
            ∫ y, (eLpNorm (fun x => F x y) p μ).toReal ∂ν :=
    h_abs_integral_le_majorant.trans h_majorant_bound
  -- Conclude by substituting back the definition of `g`.
  simpa [g] using h_abs_integral_final

end MinkowskiAux
