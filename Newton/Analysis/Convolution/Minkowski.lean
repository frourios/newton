import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Newton.MeasureTheory.Integral.Holder
import Newton.MeasureTheory.Function.LpSpace.Duality

open MeasureTheory ENNReal NNReal
open scoped ENNReal

namespace Newton

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β}
variable {E : Type*} [NormedAddCommGroup E]

/--
Relate the integral of the norm of an integrable function with the corresponding lintegral.
-/
lemma integral_norm_eq_toReal_lintegral
    [NormedSpace ℝ E] {f : α → E} (hf : Integrable f μ) :
    ∫ x, ‖f x‖ ∂μ = (∫⁻ x, ‖f x‖ₑ ∂μ).toReal := by
  have hf_norm : Integrable (fun x => ‖f x‖) μ := hf.norm
  have h_nonneg : 0 ≤ᵐ[μ] fun x => ‖f x‖ :=
    Filter.Eventually.of_forall fun _ => norm_nonneg _
  have h_eq :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf_norm h_nonneg
  have h_int_nonneg : 0 ≤ ∫ x, ‖f x‖ ∂μ :=
    integral_nonneg_of_ae h_nonneg
  have h_toReal := congrArg ENNReal.toReal h_eq
  simpa [ENNReal.toReal_ofReal, h_int_nonneg, ofReal_norm_eq_enorm] using h_toReal

section MinkowskiGeneral

variable [SFinite μ] [SFinite ν]

/--
**Minkowski's integral inequality (general form with eLpNorm).**

For 1 ≤ p < ∞ and measurable F : α × β → E,
  ‖∫ F(·, y) dν(y)‖_{L^p(μ)} ≤ ∫ ‖F(·, y)‖_{L^p(μ)} dν(y)

This is the key inequality for proving Young's inequality for convolution.
-/
theorem minkowski_integral_inequality
    [NormedSpace ℝ E] (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_ne_top : p ≠ ∞) (F : α → β → E)
    (hF : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν))
    (hF_prod : Integrable (Function.uncurry F) (μ.prod ν))
    (hF_int : ∀ᵐ y ∂ν, Integrable (fun x => F x y) μ)
    (hF_memLp : ∀ᵐ y ∂ν, MemLp (fun x => F x y) p μ)
    (hF_norm : Integrable (fun y => (eLpNorm (fun x => F x y) p μ).toReal) ν) :
    eLpNorm (fun x => ∫ y, F x y ∂ν) p μ ≤
    ENNReal.ofReal (∫ y, (eLpNorm (fun x => F x y) p μ).toReal ∂ν) := by
  have h_meas : AEStronglyMeasurable (fun x => ∫ y, F x y ∂ν) μ := by
    simpa using
      (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
        (μ := μ) (ν := ν) (f := Function.uncurry F) hF)
  have h_integrable : Integrable (fun x => ∫ y, F x y ∂ν) μ := by
    have h_bound :
        ∀ᵐ x ∂μ, ‖∫ y, F x y ∂ν‖ ≤ ∫ y, ‖F x y‖ ∂ν :=
      ae_of_all _ fun x => norm_integral_le_integral_norm (μ := ν) (f := fun y => F x y)
    refine Integrable.mono'
      (hF_prod.integral_norm_prod_left)
      h_meas
      h_bound
  have h_norm_finite : (∫⁻ y, ‖(eLpNorm (fun x => F x y) p μ).toReal‖ₑ ∂ν) < ∞ :=
    hF_norm.hasFiniteIntegral
  -- The right-hand side is nonnegative, so we may work with real-valued estimates
  have h_rhs_nonneg :
      0 ≤ ∫ y, (eLpNorm (fun x => F x y) p μ).toReal ∂ν :=
    integral_nonneg fun y => ENNReal.toReal_nonneg
  -- Reduce the claim to the integral formulation of the `L^p` seminorm
  have hp_ne_zero : p ≠ 0 := by
    intro h
    have : (1 : ℝ≥0∞) ≤ 0 := by simp [h] at hp
    exact (not_le_of_gt (zero_lt_one : (0 : ℝ≥0∞) < 1)) this
  have h_lhs_rewrite :=
    eLpNorm_eq_lintegral_rpow_enorm (μ := μ)
      (f := fun x => ∫ y, F x y ∂ν) hp_ne_zero hp_ne_top
  -- Work with the auxiliary scalar function given by the norm of the fibrewise integral.
  set g : α → ℝ := fun x => ‖∫ y, F x y ∂ν‖
  set B : ℝ := ∫ y, (eLpNorm (fun x => F x y) p μ).toReal ∂ν
  have hB_nonneg : 0 ≤ B :=
    integral_nonneg fun _ => ENNReal.toReal_nonneg
  by_cases hp_eq_one : p = 1
  · subst hp_eq_one
    have h_pointwise :
        ∀ᵐ x ∂μ, g x ≤ ∫ y, ‖F x y‖ ∂ν :=
      ae_of_all _ fun x =>
        norm_integral_le_integral_norm (μ := ν) (f := fun y => F x y)
    have hg_int : Integrable g μ := h_integrable.norm
    have h_integral_le :
        ∫ x, g x ∂μ ≤ ∫ x, ∫ y, ‖F x y‖ ∂ν ∂μ :=
      integral_mono_ae hg_int
        (hF_prod.integral_norm_prod_left)
        h_pointwise
    have h_inner_eq :
        ∀ᵐ y ∂ν,
          ∫ x, ‖F x y‖ ∂μ =
            (eLpNorm (fun x => F x y) 1 μ).toReal := by
      filter_upwards [hF_int] with y hy_int
      have h_eq :=
        integral_norm_eq_toReal_lintegral (μ := μ)
          (f := fun x => F x y) hy_int
      simpa [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
        using h_eq
    have h_double : ∫ x, ∫ y, ‖F x y‖ ∂ν ∂μ = B := by
      have h_swap :=by
        have h_norm_integrable :
            Integrable (Function.uncurry fun x y => ‖F x y‖) (μ.prod ν) :=
          hF_prod.norm
        simpa using
          MeasureTheory.integral_integral_swap
            (μ := μ) (ν := ν) (f := fun x y => ‖F x y‖)
            h_norm_integrable
      have h_congr := integral_congr_ae h_inner_eq
      simpa [g, B] using h_swap.trans h_congr
    have h_integral_bound : ∫ x, g x ∂μ ≤ B := by
      simpa [h_double] using h_integral_le
    have h_toReal_aux :=
      integral_norm_eq_toReal_lintegral (μ := μ)
        (f := fun x => ∫ y, F x y ∂ν) h_integrable
    have h_toReal :
        (eLpNorm (fun x => ∫ y, F x y ∂ν) 1 μ).toReal = ∫ x, g x ∂μ := by
      simpa [g, MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
        using h_toReal_aux.symm
    have h_toReal_le :
        (eLpNorm (fun x => ∫ y, F x y ∂ν) 1 μ).toReal ≤ B := by
      simpa [h_toReal] using h_integral_bound
    have h_memLp :
        MemLp (fun x => ∫ y, F x y ∂ν) 1 μ :=
      (memLp_one_iff_integrable : _ ↔ _).2 h_integrable
    have h_ne_top := h_memLp.eLpNorm_ne_top
    exact
      (le_ofReal_iff_toReal_le h_ne_top hB_nonneg).2 h_toReal_le
  · have hp_one_lt : 1 < p :=
      lt_of_le_of_ne' hp (by simpa [eq_comm] using hp_eq_one)
    have hp_lt_top : p < ∞ :=
      lt_of_le_of_ne le_top hp_ne_top
    obtain ⟨q, hpq, -⟩ :=
      conjugate_exponent_formula (p := p) hp_one_lt hp_lt_top
    have hq_gt_one : 1 < q := by
      rcases hpq with hpq | hpq
      · rcases hpq with ⟨hp_eq, _⟩
        simp [hp_eq] at hp_one_lt
      · rcases hpq with hpq | hpq
        · rcases hpq with ⟨hp_eq, _⟩
          simpa [hp_eq] using hp_lt_top.ne
        · rcases hpq with ⟨_, _, hq, _, _⟩
          exact hq
    have hg_mem : MemLp g p μ :=
      memLp_norm_integral (μ := μ) (ν := ν) (p := p)
        hp hp_ne_top hF hF_prod hF_memLp hF_norm
    have h_pairing_bound :
        ∀ φ : α → ℝ,
          MemLp φ q μ →
          (eLpNorm φ q μ).toReal ≤ 1 →
          Integrable (fun x => g x * φ x) μ →
          |∫ x, g x * φ x ∂μ| ≤ B := by
      intro φ hφ_mem hφ_norm _hφ_int
      have h_est :=
        holder_kernel_pairing_bound (μ := μ) (ν := ν)
          (p := p) (q := q) hpq
          hF hF_prod hF_memLp hF_norm hφ_mem
      have h_mul :
          (eLpNorm φ q μ).toReal * B ≤ B := by
        have := mul_le_mul_of_nonneg_right hφ_norm hB_nonneg
        simpa [mul_comm, mul_left_comm, mul_assoc]
          using this
      exact h_est.trans h_mul
    have h_norm_le :
        (eLpNorm g p μ).toReal ≤ B :=
      lp_duality_norm_le_of_pairing_bound (μ := μ)
        (p := p) (q := q)
        hp_one_lt hq_gt_one hpq hg_mem h_pairing_bound
    have h_ne_top :
        eLpNorm (fun x => ∫ y, F x y ∂ν) p μ ≠ ∞ := by
      have hg_ne_top := hg_mem.eLpNorm_ne_top
      simpa [g]
        using hg_ne_top
    have h_toReal_le :
        (eLpNorm (fun x => ∫ y, F x y ∂ν) p μ).toReal ≤ B := by
      simpa [g] using h_norm_le
    exact
      (le_ofReal_iff_toReal_le h_ne_top hB_nonneg).2 h_toReal_le

end MinkowskiGeneral

section ConvolutionPreparatory

variable {G : Type*}
variable [NormedAddCommGroup G] [MeasurableSpace G]
variable [MeasurableAdd₂ G] [MeasurableNeg G]
variable (μ : Measure G) [SFinite μ] [μ.IsAddRightInvariant]

/--
Almost everywhere measurability of the convolution kernel produced from `L^p` data. This lemma
packages the hypotheses needed to apply Minkowski's integral inequality in the Young inequality
arguments.
-/
lemma convolution_kernel_aestronglyMeasurable
    (f g : G → ℂ)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun q : G × G => f (q.1 - q.2) * g q.2) (μ.prod μ) := by
  have hf_aemeas : AEMeasurable f μ := hf.aemeasurable
  have hg_aemeas : AEMeasurable g μ := hg.aemeasurable
  have h_sub_qmp :
      Measure.QuasiMeasurePreserving (fun q : G × G => q.1 - q.2)
        (μ.prod μ) μ := by
    have h_sub_prod :
        MeasurePreserving (fun q : G × G => (q.1 - q.2, q.2))
          (μ.prod μ) (μ.prod μ) :=
      measurePreserving_sub_prod (μ := μ) (ν := μ)
    have h_fst_qmp :
        Measure.QuasiMeasurePreserving (fun q : G × G => q.1)
          (μ.prod μ) μ :=
      MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)
    have h_comp := h_fst_qmp.comp h_sub_prod.quasiMeasurePreserving
    simpa [Function.comp, sub_eq_add_neg, add_comm, add_left_comm]
      using h_comp
  have hf_prod_aemeas :
      AEMeasurable (fun q : G × G => f (q.1 - q.2)) (μ.prod μ) :=
    hf_aemeas.comp_quasiMeasurePreserving h_sub_qmp
  have hg_prod_aemeas :
      AEMeasurable (fun q : G × G => g q.2) (μ.prod μ) :=
    hg_aemeas.comp_quasiMeasurePreserving
      (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ))
  have h_mul_aemeas :
      AEMeasurable (fun q : G × G => f (q.1 - q.2) * g q.2) (μ.prod μ) := by
    have := hf_prod_aemeas.mul hg_prod_aemeas
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  exact h_mul_aemeas.aestronglyMeasurable

/--
Integrability of the convolution kernel assuming the factors themselves are integrable. This is the
basic input needed for the convolution estimates below.
-/
lemma convolution_kernel_integrable
    (f g : G → ℂ)
    (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun q : G × G => f (q.1 - q.2) * g q.2) (μ.prod μ) := by
  -- Basic measurability for the kernel
  have h_meas : AEStronglyMeasurable
      (fun q : G × G => f (q.1 - q.2) * g q.2) (μ.prod μ) :=
    convolution_kernel_aestronglyMeasurable (μ := μ)
      f g hf.aestronglyMeasurable hg.aestronglyMeasurable
  -- Work with the nonnegative integrand built from the norms of `f` and `g`.
  set Af : G → ℝ≥0∞ := fun x => ‖f x‖ₑ
  set Ag : G → ℝ≥0∞ := fun y => ‖g y‖ₑ
  have hAf_aemeas : AEMeasurable Af μ :=
    hf.aestronglyMeasurable.enorm
  have hAg_aemeas : AEMeasurable Ag μ :=
    hg.aestronglyMeasurable.enorm
  have hAf_lt_top : (∫⁻ x, Af x ∂μ) < ∞ := by
    simpa [Af, HasFiniteIntegral]
      using hf.hasFiniteIntegral
  have hAg_lt_top : (∫⁻ y, Ag y ∂μ) < ∞ := by
    simpa [Ag, HasFiniteIntegral]
      using hg.hasFiniteIntegral
  -- Express the norm of the kernel pointwise in terms of `Af` and `Ag`.
  have h_norm_rewrite :
      (∫⁻ q : G × G, ‖f (q.1 - q.2) * g q.2‖ₑ ∂(μ.prod μ))
        = ∫⁻ q : G × G, Af (q.1 - q.2) * Ag q.2 ∂(μ.prod μ) := by
    refine lintegral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro q
    simp [Af, Ag, mul_comm]
  -- Change variables via the measure-preserving map `(x, y) ↦ (x - y, y)`.
  set τ : G × G → G × G := fun q => (q.1 - q.2, q.2)
  have h_pres : MeasurePreserving τ (μ.prod μ) (μ.prod μ) :=
    measurePreserving_sub_prod (μ := μ) (ν := μ)
  have h_map : Measure.map τ (μ.prod μ) = μ.prod μ := h_pres.map_eq
  have hAf_prod_aemeas :
      AEMeasurable (fun q : G × G => Af q.1) (μ.prod μ) :=
    hAf_aemeas.comp_quasiMeasurePreserving
      (MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ))
  have hAg_prod_aemeas :
      AEMeasurable (fun q : G × G => Ag q.2) (μ.prod μ) :=
    hAg_aemeas.comp_quasiMeasurePreserving
      (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ))
  have h_prod_aemeas :
      AEMeasurable (fun q : G × G => Af q.1 * Ag q.2) (μ.prod μ) :=
    hAf_prod_aemeas.mul hAg_prod_aemeas
  have h_change :
      ∫⁻ q : G × G, Af (q.1 - q.2) * Ag q.2 ∂(μ.prod μ)
        = ∫⁻ q : G × G, Af q.1 * Ag q.2 ∂(μ.prod μ) := by
    have h_integrand_map :
        AEMeasurable (fun q : G × G => Af q.1 * Ag q.2)
          (Measure.map τ (μ.prod μ)) := by
      simpa [h_map]
        using h_prod_aemeas
    have h_comp :=
      lintegral_map' h_integrand_map
        (aemeasurable_id'.comp_measurable h_pres.measurable)
    have h_comp' :
        ∫⁻ q, Af q.1 * Ag q.2 ∂(μ.prod μ)
          = ∫⁻ q, Af (τ q).1 * Ag (τ q).2 ∂(μ.prod μ) := by
      simpa [τ, h_map]
        using h_comp
    simpa [τ]
      using h_comp'.symm
  -- Evaluate the remaining product integral via Tonelli.
  have h_tonelli :=
    MeasureTheory.lintegral_prod (μ := μ) (ν := μ)
      (f := fun q : G × G => Af q.1 * Ag q.2) h_prod_aemeas
  have h_const_mul :
      ∀ x : G, ∫⁻ y, Af x * Ag y ∂μ = Af x * ∫⁻ y, Ag y ∂μ := by
    intro x
    simpa using
      (lintegral_const_mul'' (μ := μ)
        (r := Af x) (f := Ag) hAg_aemeas)
  have h_split :
      ∫⁻ q : G × G, Af q.1 * Ag q.2 ∂(μ.prod μ)
        = ∫⁻ x : G, ∫⁻ y : G, Af x * Ag y ∂μ ∂μ := by
    simpa [Function.uncurry]
      using h_tonelli
  have h_point :
      (fun x : G => ∫⁻ y, Af x * Ag y ∂μ)
        = fun x : G => Af x * ∫⁻ y, Ag y ∂μ := by
    funext x
    exact h_const_mul x
  have h_outer :
      ∫⁻ x : G, Af x * ∫⁻ y : G, Ag y ∂μ ∂μ
        = (∫⁻ y, Ag y ∂μ) * ∫⁻ x, Af x ∂μ := by
    simpa [mul_comm]
      using
        (lintegral_mul_const'' (μ := μ)
          (r := ∫⁻ y, Ag y ∂μ) (f := Af) hAf_aemeas)
  have h_lintegral_prod :
      ∫⁻ q : G × G, Af q.1 * Ag q.2 ∂(μ.prod μ)
        = (∫⁻ x, Af x ∂μ) * (∫⁻ y, Ag y ∂μ) := by
    calc
      ∫⁻ q : G × G, Af q.1 * Ag q.2 ∂(μ.prod μ)
          = ∫⁻ x : G, ∫⁻ y : G, Af x * Ag y ∂μ ∂μ := h_split
      _ = ∫⁻ x : G, Af x * ∫⁻ y : G, Ag y ∂μ ∂μ := by
            simp [h_point]
      _ = (∫⁻ y, Ag y ∂μ) * ∫⁻ x, Af x ∂μ := h_outer
      _ = (∫⁻ x, Af x ∂μ) * (∫⁻ y, Ag y ∂μ) := by
            simp [mul_comm]
  -- Collect the previous computations to bound the kernel integral.
  have h_kernel_lintegral :
      (∫⁻ q : G × G, ‖f (q.1 - q.2) * g q.2‖ₑ ∂(μ.prod μ))
        = (∫⁻ x, Af x ∂μ) * (∫⁻ y, Ag y ∂μ) := by
    calc
      ∫⁻ q, ‖f (q.1 - q.2) * g q.2‖ₑ ∂(μ.prod μ)
          = ∫⁻ q, Af (q.1 - q.2) * Ag q.2 ∂(μ.prod μ) := h_norm_rewrite
      _ = ∫⁻ q, Af q.1 * Ag q.2 ∂(μ.prod μ) := h_change
      _ = (∫⁻ x, Af x ∂μ) * (∫⁻ y, Ag y ∂μ) := h_lintegral_prod
  have h_aux :
      (∫⁻ q : G × G, Af (q.1 - q.2) * Ag q.2 ∂(μ.prod μ)) < ∞ := by
    simpa [h_change, h_lintegral_prod]
      using ENNReal.mul_lt_top hAf_lt_top hAg_lt_top
  have h_kernel_fin :
      (∫⁻ q : G × G, ‖f (q.1 - q.2) * g q.2‖ₑ ∂(μ.prod μ)) < ∞ := by
    simpa [h_norm_rewrite]
      using h_aux
  exact ⟨h_meas, h_kernel_fin⟩

end ConvolutionPreparatory

end Newton
