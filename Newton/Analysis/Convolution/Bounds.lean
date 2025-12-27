import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Newton.Analysis.Convolution.Basic
import Newton.Analysis.Convolution.Minkowski

open MeasureTheory Complex NNReal
open scoped ENNReal ContDiff Pointwise

variable {n : ℕ}

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

lemma convolution_sub
    (f₁ f₂ g : (Fin n → ℝ) → ℂ)
    (hconv₁ : ∀ᵐ x ∂volume, Integrable (fun y => f₁ (x - y) * g y) volume)
    (hconv₂ : ∀ᵐ x ∂volume, Integrable (fun y => f₂ (x - y) * g y) volume) :
    (fun x => ∫ a, (f₁ (x - a) - f₂ (x - a)) * g a) =ᶠ[ae volume]
    (fun x => (∫ a, f₁ (x - a) * g a) - ∫ a, f₂ (x - a) * g a) := by
  have h_ae_both : ∀ᵐ x ∂volume, Integrable (fun a => f₁ (x - a) * g a) volume ∧
                                    Integrable (fun a => f₂ (x - a) * g a) volume := by
    filter_upwards [hconv₁, hconv₂] with x h₁ h₂
    exact ⟨h₁, h₂⟩
  filter_upwards [h_ae_both] with x ⟨hint₁, hint₂⟩
  have h₁ :
      ∫ a, (f₁ (x - a) - f₂ (x - a)) * g a =
        ∫ a, f₁ (x - a) * g a - f₂ (x - a) * g a := by
    simp [sub_mul]
  have h₂ :
      ∫ a, f₁ (x - a) * g a - f₂ (x - a) * g a =
        (∫ a, f₁ (x - a) * g a) - ∫ a, f₂ (x - a) * g a := by
    simpa using integral_sub hint₁ hint₂
  exact h₁.trans h₂

section MollifierProperties

/--
Transport `AEMeasurable` across a positive scalar multiple of a measure.
If `f` is a.e.-measurable w.r.t. `μ`, then it is also a.e.-measurable w.r.t. `c • μ`.
This simple helper is used to avoid threading measurability through `map` equalities.
-/
lemma aemeasurable_smul_measure_of_aemeasurable
    {α : Type*} [MeasurableSpace α]
    (f : α → ℝ≥0∞) (μ : Measure α) (c : ℝ≥0∞)
    (hf : AEMeasurable f μ) : AEMeasurable f (c • μ) := by
  rcases hf with ⟨g, hg_meas, hfg⟩
  refine ⟨g, hg_meas, ?_⟩
  -- Transfer the a.e. equality along the scalar multiple of the measure.
  -- If μ {x | f x ≠ g x} = 0 then (c • μ) {x | f x ≠ g x} = 0.
  -- Extract the null set statement from the a.e. equality
  have h_zero : μ {x | f x ≠ g x} = 0 := (ae_iff).1 hfg
  -- Scale the measure: null sets remain null for `c • μ`
  have h_zero' : (c • μ) {x | f x ≠ g x} = 0 := by
    -- Avoid `simp` turning equality into a disjunction via `mul_eq_zero`.
    -- Directly rewrite using `Measure.smul_apply` and `h_zero`.
    simp [Measure.smul_apply, h_zero]
  -- Turn the null-set statement back into an a.e. equality for `c • μ`.
  exact (ae_iff).2 h_zero'

/--
**Scaled mollifier L¹ norm bound.**

For the scaled mollifier ψ_η with ∫ ψ = 1, we have ‖ψ_η‖₁ = 1.
-/
theorem scaled_mollifier_L1_norm_one
    (ψ : (Fin n → ℝ) → ℝ)
    (η : ℝ)
    (hη : 0 < η)
    (hψ_int : Integrable ψ volume)
    (hψ_norm : ∫ x, ψ x = 1)
    (hψ_nonneg : ∀ x, 0 ≤ ψ x) :
    eLpNorm (fun (x : Fin n → ℝ) => η^(-(n : ℝ)) * ψ (fun i => x i / η)) 1 volume =
      ENNReal.ofReal 1 := by
  -- Define the scaled mollifier and the scaling map.
  set ψη : (Fin n → ℝ) → ℝ :=
    fun x => η^(-(n : ℝ)) * ψ (fun i => x i / η) with hψη_def
  set g : (Fin n → ℝ) → (Fin n → ℝ) := fun x => (1 / η : ℝ) • x with hg_def

  -- Basic measurability for the scaling map
  have hg_meas : Measurable g := by
    simpa [hg_def] using (continuous_const_smul (1 / η : ℝ)).measurable

  -- Pointwise positivity of ψη due to ψ ≥ 0 and η > 0.
  have hψη_nonneg : ∀ x, 0 ≤ ψη x := by
    intro x
    have hx_arg : (η⁻¹ : ℝ) • x = fun i => x i * η⁻¹ := by
      funext i
      simp [Pi.smul_apply, smul_eq_mul, mul_comm]
    have hψ_nonneg_at : 0 ≤ ψ (g x) := hψ_nonneg (g x)
    have hηpos : 0 ≤ η^(-(n : ℝ)) := by
      have : 0 < η^(-(n : ℝ)) := by
        simpa using Real.rpow_pos_of_pos hη (-(n : ℝ))
      exact this.le
    -- Align ψ (g x) with ψ (fun i => x i / η) using hx_arg
    simpa [hψη_def, hg_def, one_div, div_eq_mul_inv, hx_arg, mul_comm, mul_left_comm, mul_assoc]
      using mul_nonneg hηpos hψ_nonneg_at

  -- Rewrite the L¹ seminorm as a nonnegative lintegral and factor out the constant η^{-n}.
  have h_step1 :
      eLpNorm ψη 1 volume
        = ENNReal.ofReal (η^(-(n : ℝ))) *
            ∫⁻ x, ENNReal.ofReal (ψ (g x)) ∂volume := by
    -- Start from the L¹ formula for `eLpNorm` and rewrite the integrand.
    have hη_nonneg : 0 ≤ η^(-(n : ℝ)) := by
      have : 0 < η^(-(n : ℝ)) := by simpa using Real.rpow_pos_of_pos hη (-(n : ℝ))
      exact this.le
    have h_enorm_eq :
        ∀ᵐ x ∂volume,
          (‖ψη x‖ₑ : ℝ≥0∞)
            = ENNReal.ofReal (η^(-(n : ℝ))) * ENNReal.ofReal (ψ (g x)) := by
      refine Filter.Eventually.of_forall (fun x => ?_)
      have hψgx_nonneg : 0 ≤ ψ (g x) := hψ_nonneg (g x)
      -- Align arguments: (η⁻¹) • x = fun i => x i * η⁻¹
      have hx_arg : (η⁻¹ : ℝ) • x = fun i => x i * η⁻¹ := by
        funext i; simp [Pi.smul_apply, smul_eq_mul, mul_comm]
      calc
        (‖ψη x‖ₑ : ℝ≥0∞)
            = ENNReal.ofReal ‖ψη x‖ := (ofReal_norm_eq_enorm (ψη x)).symm
        _   = ENNReal.ofReal (ψη x) := by
              simp [Real.norm_eq_abs, abs_of_nonneg (hψη_nonneg x)]
        _   = ENNReal.ofReal (η^(-(n : ℝ)) * ψ (g x)) := by
              simp [hψη_def, hg_def, one_div, div_eq_mul_inv, hx_arg,
                mul_comm, mul_left_comm, mul_assoc]
        _   = ENNReal.ofReal (η^(-(n : ℝ))) * ENNReal.ofReal (ψ (g x)) := by
              -- Use `ENNReal.ofReal_mul` (one nonneg proof argument) and specify `p`, `q`.
              simpa [mul_comm, mul_left_comm, mul_assoc]
                using (ENNReal.ofReal_mul
                  (p := η^(-(n : ℝ))) (q := ψ (g x)) hη_nonneg)
    -- Pull the constant out of the lintegral using the `c ≠ ∞` variant.
    have h_c_ne_top : ENNReal.ofReal (η^(-(n : ℝ))) ≠ ∞ := by simp
    calc
      eLpNorm ψη 1 volume
          = ∫⁻ x, ‖ψη x‖ₑ ∂volume := by
                simp [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
      _   = ∫⁻ x, ENNReal.ofReal (η^(-(n : ℝ))) * ENNReal.ofReal (ψ (g x)) ∂volume := by
                simpa using lintegral_congr_ae h_enorm_eq
      _   = ENNReal.ofReal (η^(-(n : ℝ))) * ∫⁻ x, ENNReal.ofReal (ψ (g x)) ∂volume := by
                simpa [mul_comm, mul_left_comm, mul_assoc]
                  using
                    (lintegral_const_mul' (μ := volume)
                      (ENNReal.ofReal (η^(-(n : ℝ))))
                      (fun x : (Fin n → ℝ) => ENNReal.ofReal (ψ (g x)))
                      h_c_ne_top)

  -- Compute the pushforward of Lebesgue measure under the linear scaling map x ↦ (1/η)·x.
  have h_map_scale :
      Measure.map g volume
        = ENNReal.ofReal (abs ((LinearMap.det
              ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹)) • volume := by
    -- This is a standard Jacobian formula for linear maps on ℝ^n.
    simpa [g, hg_def]
      using Real.map_linearMap_volume_pi_eq_smul_volume_pi
        (f := ( (1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ))
        (by
          -- Show det ≠ 0 via the explicit determinant formula and η ≠ 0.
          have hne : (1 / η : ℝ) ≠ 0 := one_div_ne_zero (ne_of_gt hη)
          have hdet :
              LinearMap.det
                  ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
                = (1 / η : ℝ) ^ Module.finrank ℝ (Fin n → ℝ) := by
            simp
          have hpow2 : (1 / η : ℝ) ^ (Module.finrank ℝ (Fin n → ℝ)) ≠ 0 :=
            pow_ne_zero (Module.finrank ℝ (Fin n → ℝ)) hne
          simpa [hdet] using hpow2)
  -- Change variables: express the lintegral of ψ ∘ g via the pushforward measure.
  have h_change :
      ∫⁻ x, ENNReal.ofReal (ψ (g x)) ∂volume
        = ENNReal.ofReal (abs ((LinearMap.det
            ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹))
            * ∫⁻ y, ENNReal.ofReal (ψ y) ∂volume := by
    -- Build AEMeasurable for the integrand under the pushforward measure.
    have hψ_aemeas : AEMeasurable ψ volume :=
      hψ_int.aestronglyMeasurable.aemeasurable
    have h_ofReal_aemeas_map :
        AEMeasurable (fun y : (Fin n → ℝ) => ENNReal.ofReal (ψ y))
          (Measure.map g volume) := by
      -- Use the helper to transport a.e.-measurability across the scalar multiple
      -- given by `h_map_scale`.
      have h_ofReal_aemeas_vol :
          AEMeasurable (fun y : (Fin n → ℝ) => ENNReal.ofReal (ψ y)) volume :=
        hψ_aemeas.ennreal_ofReal
      -- `Measure.map g volume = c • volume` where `c = ofReal |det g|⁻¹`.
      -- Hence a.e.-measurability transfers from `volume` to `Measure.map g volume`.
      simpa [h_map_scale]
        using aemeasurable_smul_measure_of_aemeasurable
          (f := fun y : (Fin n → ℝ) => ENNReal.ofReal (ψ y))
          (μ := volume)
          (c := ENNReal.ofReal (abs ((LinearMap.det
            ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹)))
          h_ofReal_aemeas_vol
    -- Change of variables for lintegral via `lintegral_map'`.
    have h_map_eq :=
      lintegral_map' (μ := volume)
        (f := fun y : (Fin n → ℝ) => ENNReal.ofReal (ψ y))
        (g := g) h_ofReal_aemeas_map
        (aemeasurable_id'.comp_measurable hg_meas)
    -- Pull out the scaling factor from the pushforward measure using `lintegral_smul_measure`.
    have h_pull_const :
        ∫⁻ y, ENNReal.ofReal (ψ y) ∂(Measure.map g volume)
          = ENNReal.ofReal (abs ((LinearMap.det
              ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹))
              * ∫⁻ y, ENNReal.ofReal (ψ y) ∂volume := by
      simp [h_map_scale, lintegral_smul_measure, mul_comm, mul_left_comm, mul_assoc]
    simpa [h_map_eq] using h_pull_const

  -- Convert the remaining lintegral to a real integral using nonnegativity of ψ.
  have hψ_nonneg_ae : 0 ≤ᵐ[volume] fun y => ψ y :=
    Filter.Eventually.of_forall hψ_nonneg
  have hψ_lintegral :
      ∫⁻ y, ENNReal.ofReal (ψ y) ∂volume
        = ENNReal.ofReal (∫ y, ψ y ∂volume) := by
    -- Use the standard bridge between lintegral and integral for nonnegative integrable ψ.
    simpa using
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hψ_int hψ_nonneg_ae).symm

  have h_det_simp :
      ENNReal.ofReal (abs ((LinearMap.det
          ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹))
        = ENNReal.ofReal (η ^ (n : ℝ)) := by
    -- Evaluate the determinant and simplify using η > 0.
    have hdet :
        LinearMap.det ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
          = (1 / η : ℝ) ^ (Module.finrank ℝ (Fin n → ℝ)) := by
      simp
    have hfinrank : (Module.finrank ℝ (Fin n → ℝ)) = n := by
      simp
    -- Since η > 0, ((1/η)^n)⁻¹ = η^n and is nonnegative, so its absolute value equals itself.
    have h_pow_inv : ((1 / η : ℝ) ^ n)⁻¹ = η ^ n := by
      -- Use (a^n)⁻¹ = (a⁻¹)^n with a = 1/η and (1/η)⁻¹ = η.
      simp [one_div, inv_inv]
    have h_nonneg : 0 ≤ ((1 / η : ℝ) ^ n)⁻¹ := by
      -- Positivity from η > 0.
      have hpos : 0 < (1 / η : ℝ) := by
        simpa [one_div] using (inv_pos.mpr hη)
      exact inv_nonneg.mpr (le_of_lt (pow_pos hpos n))
    have h_abs_eq : abs (((1 / η : ℝ) ^ n)⁻¹) = ((1 / η : ℝ) ^ n)⁻¹ :=
      abs_of_nonneg h_nonneg
    -- Translate nat-power to real-power.
    have h_nat_to_real : (η ^ n : ℝ) = η ^ (n : ℝ) := by
      simp
    -- Conclude.
    calc
      ENNReal.ofReal (abs ((LinearMap.det
          ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹))
          = ENNReal.ofReal (abs (((1 / η : ℝ) ^ (Module.finrank ℝ (Fin n → ℝ))) )⁻¹) := by
            simp [hdet]
      _ = ENNReal.ofReal (abs (((1 / η : ℝ) ^ n)⁻¹)) := by simp [hfinrank]
      _ = ENNReal.ofReal (((1 / η : ℝ) ^ n)⁻¹) := by simp [abs_of_pos hη]
      _ = ENNReal.ofReal (η ^ n) := by simp [h_pow_inv]
      _ = ENNReal.ofReal (((η : ℝ) ^ (n : ℝ))) := by
        -- Avoid `simp` looping by using a directed rewrite.
        exact congrArg ENNReal.ofReal h_nat_to_real

  -- Combine all equalities and simplify using ∫ ψ = 1 and rpow rules.
  have h_prod :
      ENNReal.ofReal (η^(-(n : ℝ)))
        * (ENNReal.ofReal (abs ((LinearMap.det
            ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹)))
        = ENNReal.ofReal 1 := by
    -- Use multiplicativity of ofReal and rpow addition.
    have hη_pos_real : 0 ≤ η^(-(n : ℝ)) :=
      (Real.rpow_pos_of_pos hη (-(n : ℝ))).le
    have hη_pow_pos : 0 ≤ η ^ (n : ℝ) :=
      (Real.rpow_pos_of_pos hη (n : ℝ)).le
    have h_mul_ofReal :
        ENNReal.ofReal (η^(-(n : ℝ)) * η ^ (n : ℝ))
          = ENNReal.ofReal (η^(-(n : ℝ))) * ENNReal.ofReal (η ^ (n : ℝ)) := by
      simpa [mul_comm, mul_left_comm, mul_assoc]
        using (ENNReal.ofReal_mul (p := η^(-(n : ℝ))) (q := η ^ (n : ℝ)) hη_pos_real)
    -- Simplify the product inside ofReal using rpow_add.
    have h_rpow : η^(-(n : ℝ)) * η ^ (n : ℝ) = (η : ℝ) ^ (0 : ℝ) := by
      have h_add := Real.rpow_add hη (-(n : ℝ)) (n : ℝ)
      -- x^(a+b) = x^a * x^b ⇒ x^a * x^b = x^(a+b)
      -- Here a = -n, b = n, so a + b = 0.
      have hsum : (-(n : ℝ)) + (n : ℝ) = 0 := by simp
      simpa [hsum, Real.rpow_zero] using h_add.symm
    -- Conclude the product equals 1.
    have h_one : ENNReal.ofReal ((η : ℝ) ^ (0 : ℝ)) = ENNReal.ofReal 1 := by
      simp
    calc
      ENNReal.ofReal (η^(-(n : ℝ)))
          * ENNReal.ofReal (abs ((LinearMap.det
              ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹))
          = ENNReal.ofReal (η^(-(n : ℝ))) * ENNReal.ofReal (η ^ (n : ℝ)) := by
                simp [abs_of_pos hη]
      _ = ENNReal.ofReal (η^(-(n : ℝ)) * η ^ (n : ℝ)) := by
                -- Use the earlier multiplicativity lemma tailored to rpow terms.
                simpa using h_mul_ofReal.symm
      _ = ENNReal.ofReal ((η : ℝ) ^ (0 : ℝ)) := by
        simpa using h_rpow
      _ = ENNReal.ofReal 1 := h_one

  -- Final assembly: start from `h_step1`, apply the change-of-variables `h_change`,
  -- convert the remaining lintegral using `hψ_lintegral`, and simplify with `hψ_norm`.
  calc
    eLpNorm ψη 1 volume
        = ENNReal.ofReal (η^(-(n : ℝ))) *
            ∫⁻ x, ENNReal.ofReal (ψ (g x)) ∂volume := h_step1
    _ = (ENNReal.ofReal (η^(-(n : ℝ))) *
            ENNReal.ofReal (abs ((LinearMap.det
              ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹)))
            * ∫⁻ y, ENNReal.ofReal (ψ y) ∂volume := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            congrArg (fun z => ENNReal.ofReal (η^(-(n : ℝ))) * z) h_change
    _ = ENNReal.ofReal 1 * ENNReal.ofReal (∫ y, ψ y ∂volume) := by
          -- First, multiply the constant factor equality `h_prod` by the lintegral.
          have hconst_mul :
              (ENNReal.ofReal (η^(-(n : ℝ))) *
                ENNReal.ofReal (abs ((LinearMap.det
                  ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹)))
                * ∫⁻ y, ENNReal.ofReal (ψ y) ∂volume
                = ENNReal.ofReal 1 * ∫⁻ y, ENNReal.ofReal (ψ y) ∂volume := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using
              congrArg (fun c => c * ∫⁻ y, ENNReal.ofReal (ψ y) ∂volume) h_prod
          -- Then convert the lintegral using `hψ_lintegral`.
          simpa [hψ_lintegral] using hconst_mul
    _ = ENNReal.ofReal 1 := by simp [hψ_norm]

end MollifierProperties

section ConvolutionDifferenceBounds

/--
**Bound on difference of convolutions (L¹ case).**

‖(g - f₀) * ψ‖₁ ≤ ‖g - f₀‖₁ · ‖ψ‖₁

Corresponds to h_conv_diff_bound in the code.
-/
theorem convolution_diff_bound_L1
    (f₁ f₂ ψ : (Fin n → ℝ) → ℂ)
    (hf₁ : Integrable f₁ volume)
    (hf₂ : Integrable f₂ volume)
    (hψ : Integrable ψ volume) :
    eLpNorm (fun x =>
      (∫ y, f₁ (x - y) * ψ y) - (∫ y, f₂ (x - y) * ψ y)) 1 volume ≤
      eLpNorm (fun x => f₁ x - f₂ x) 1 volume * eLpNorm ψ 1 volume := by
  -- Rewrite the difference of convolutions as the convolution of the difference.
  have hconv₁ : ∀ᵐ x ∂volume, Integrable (fun y => f₁ (x - y) * ψ y) volume := by
    have h_kernel :=
      convolution_kernel_integrable (μ := volume)
        (f := f₁) (g := ψ) hf₁ hψ
    have h := Integrable.prod_right_ae (μ := volume) (ν := volume) h_kernel
    refine h.mono ?_
    intro x hx
    simpa [sub_eq_add_neg] using hx
  have hconv₂ : ∀ᵐ x ∂volume, Integrable (fun y => f₂ (x - y) * ψ y) volume := by
    have h_kernel :=
      convolution_kernel_integrable (μ := volume)
        (f := f₂) (g := ψ) hf₂ hψ
    have h := Integrable.prod_right_ae (μ := volume) (ν := volume) h_kernel
    refine h.mono ?_
    intro x hx
    simpa [sub_eq_add_neg] using hx
  have h_sub_ae := convolution_sub (f₁ := f₁) (f₂ := f₂) (g := ψ) hconv₁ hconv₂

  -- Use ae-equality to replace the L¹ norm by the convolution of the difference.
  have h_eq_eLp :
      eLpNorm (fun x =>
        (∫ y, f₁ (x - y) * ψ y) - (∫ y, f₂ (x - y) * ψ y)) 1 volume
        = eLpNorm (fun x => ∫ y, (f₁ (x - y) - f₂ (x - y)) * ψ y) 1 volume := by
    -- note the equality in `convolution_sub` has the opposite orientation
    simpa using
      eLpNorm_congr_ae (μ := volume) (p := (1 : ℝ≥0∞)) h_sub_ae.symm

  -- Apply Young (L¹×L¹→L¹) to the convolution of the difference with ψ.
  have hdiff_int : Integrable (fun x => f₁ x - f₂ x) volume := hf₁.sub hf₂
  have hdiff_mem : MemLp (fun x => f₁ x - f₂ x) 1 volume :=
    (memLp_one_iff_integrable (μ := volume)).2 hdiff_int
  have hψ_mem : MemLp ψ 1 volume :=
    (memLp_one_iff_integrable (μ := volume)).2 hψ
  have h_young :=
    young_convolution_inequality
      (f := fun x => f₁ x - f₂ x) (g := ψ)
      (p := (1 : ℝ≥0∞)) (q := (1 : ℝ≥0∞)) (r := (1 : ℝ≥0∞))
      (hp := by simp) (hq := by simp) (hpqr := by simp)
      hdiff_mem hψ_mem

  -- Assemble the estimate.
  have :
      eLpNorm (fun x => ∫ y, (f₁ (x - y) - f₂ (x - y)) * ψ y) 1 volume ≤
        eLpNorm (fun x => f₁ x - f₂ x) 1 volume * eLpNorm ψ 1 volume := by
    simpa using h_young.2
  simpa [h_eq_eLp] using this

/--
**Bound on difference of convolutions with a normalized mollifier (L¹ case).**

If ψ is a non-negative mollifier with unit mass, convolution with the scaled
ψ does not increase the L¹ distance between two functions.
-/
theorem mollifier_convolution_diff_L1
    (g f₀ : (Fin n → ℝ) → ℂ)
    (ψ : (Fin n → ℝ) → ℝ)
    (hg : Integrable g volume)
    (hf₀ : Integrable f₀ volume)
    (hψ_nonneg : ∀ x, 0 ≤ ψ x)
    (hψ_int : ∫ x, ψ x = 1) :
    ∀ η : ℝ, 0 < η → η < 1 →
      eLpNorm (fun x =>
        (∫ y, g (x - y) * (↑(η^(-(n : ℝ)) * ψ (fun i => y i / η)) : ℂ)) -
        (∫ y, f₀ (x - y) * (↑(η^(-(n : ℝ)) * ψ (fun i => y i / η)) : ℂ)))
        1 volume ≤
      eLpNorm (fun x => g x - f₀ x) 1 volume := by
  intro η hη_pos _hη_lt_one
  -- Define the scaled mollifier (real and complex versions).
  set ψηR : (Fin n → ℝ) → ℝ :=
    fun y => η^(-(n : ℝ)) * ψ (fun i => y i / η) with hψηR_def
  set ψηC : (Fin n → ℝ) → ℂ := fun y => (ψηR y : ℝ) with hψηC_def

  -- L¹ norm of the scaled mollifier equals 1.
  -- First, obtain integrability of ψ from the normalization assumption.
  have hψ_integrable : Integrable ψ volume := by
    by_contra hnot
    have h0 : ∫ x, ψ x ∂volume = 0 := by
      simp [MeasureTheory.integral_undef hnot]  -- integral is 0 if not integrable
    have : (1 : ℝ) = 0 := by
      calc
        (1 : ℝ) = ∫ x, ψ x ∂volume := by simpa using hψ_int.symm
        _ = 0 := h0
    exact one_ne_zero this
  have hψηR_L1 : eLpNorm ψηR 1 volume = ENNReal.ofReal 1 := by
    simpa [hψηR_def]
      using scaled_mollifier_L1_norm_one (ψ := ψ) (η := η)
        hη_pos hψ_integrable hψ_int hψ_nonneg
  -- Transfer the L¹ norm equality to the complex-valued version.
  have hψηC_L1 : eLpNorm ψηC 1 volume = ENNReal.ofReal 1 := by
    have h_eq : eLpNorm ψηC 1 volume = eLpNorm ψηR 1 volume := by
      refine eLpNorm_congr_norm_ae (μ := volume) (p := (1 : ℝ≥0∞)) ?_
      exact Filter.Eventually.of_forall (fun x => by
        simp [ψηC, hψηC_def, Real.norm_eq_abs])
    simpa [h_eq] using hψηR_L1

  -- Obtain integrability of the complex scaled mollifier from its finite L¹ norm.
  have hψηC_meas : AEStronglyMeasurable ψηC volume := by
    -- Build AEMeasurable for the real scaled mollifier, then lift to complex via ofReal.
    have hψ_meas : AEMeasurable ψ volume :=
      hψ_integrable.aestronglyMeasurable.aemeasurable
    have h_scale_meas : Measurable fun y : (Fin n → ℝ) => (1 / η : ℝ) • y :=
      (continuous_const_smul (1 / η : ℝ)).measurable
    -- Compute the pushforward of volume under scaling and derive quasi-measure-preserving.
    have h_map_scale :
        Measure.map (fun y : (Fin n → ℝ) => (1 / η : ℝ) • y) volume
          = ENNReal.ofReal (abs ((LinearMap.det
                ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹)) • volume := by
      simpa
        using Real.map_linearMap_volume_pi_eq_smul_volume_pi
          (f := ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))))
          (by
            have hne : (1 / η : ℝ) ≠ 0 := one_div_ne_zero (ne_of_gt hη_pos)
            have hdet :
                LinearMap.det
                    ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
                  = (1 / η : ℝ) ^ Module.finrank ℝ (Fin n → ℝ) := by
              simp
            have hpow2 : (1 / η : ℝ) ^ (Module.finrank ℝ (Fin n → ℝ)) ≠ 0 :=
              pow_ne_zero (Module.finrank ℝ (Fin n → ℝ)) hne
            simpa [hdet] using hpow2)
    have h_scale_qmp :
        Measure.QuasiMeasurePreserving (fun y : (Fin n → ℝ) => (1 / η : ℝ) • y)
          volume volume := by
      refine ⟨h_scale_meas, ?_⟩
      have h_le :
          Measure.map (fun y : (Fin n → ℝ) => (1 / η : ℝ) • y) volume ≤
            ENNReal.ofReal (abs ((LinearMap.det
              ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹)) • volume := by
        simpa [h_map_scale] using (le_of_eq h_map_scale)
      exact Measure.absolutelyContinuous_of_le_smul h_le
    -- Compose along the quasi-measure-preserving scaling map.
    have h_comp : AEMeasurable (fun y => ψ ((1 / η) • y)) volume :=
      hψ_meas.comp_quasiMeasurePreserving h_scale_qmp
    have h_c_meas : AEMeasurable (fun _ : (Fin n → ℝ) => η^(-(n : ℝ))) volume :=
      (measurable_const : Measurable fun _ : (Fin n → ℝ) => η^(-(n : ℝ))).aemeasurable
    -- Rewrite the argument `η⁻¹ • x` to the coordinate form `fun i => x i / η`.
    have h_arg_eq_inv :
        (fun x : (Fin n → ℝ) => ψ (η⁻¹ • x))
          = (fun x : (Fin n → ℝ) => ψ (fun i => x i / η)) := by
      funext x
      have : (η⁻¹ : ℝ) • x = (fun i => x i * η⁻¹) := by
        funext i; simp [Pi.smul_apply, smul_eq_mul, mul_comm]
      simp [div_eq_mul_inv, this]
    have h_comp' : AEMeasurable (fun y : (Fin n → ℝ) => ψ ((1 / η) • y)) volume := by
      simpa [one_div] using h_comp
    have h_comp2 : AEMeasurable (fun y : (Fin n → ℝ) => ψ (fun i => y i / η)) volume := by
      -- Convert `((1/η) • y)` to `(η⁻¹ • y)` and then rewrite by coordinates.
      have h_comp'' : AEMeasurable (fun y : (Fin n → ℝ) => ψ (η⁻¹ • y)) volume := by
        simpa [one_div] using h_comp'
      simpa [h_arg_eq_inv] using h_comp''
    have hψηR_ae : AEMeasurable ψηR volume := by
      simpa [ψηR, hψηR_def] using h_c_meas.mul h_comp2
    have hψηR_sm : AEStronglyMeasurable ψηR volume := hψηR_ae.aestronglyMeasurable
    exact (Complex.measurable_ofReal.comp_aemeasurable hψηR_sm.aemeasurable).aestronglyMeasurable

  have hψηC_int : Integrable ψηC volume := by
    -- From measurability and the finite L¹ norm we get membership in L¹, hence integrable.
    have h_lt_top : eLpNorm ψηC 1 volume < (⊤ : ℝ≥0∞) := by
      simp [hψηC_L1]
    have h_mem : MemLp ψηC 1 volume := ⟨hψηC_meas, h_lt_top⟩
    simpa using (memLp_one_iff_integrable (μ := volume)).1 h_mem

  -- Apply the L¹ convolution difference bound with the scaled mollifier.
  have h_bound :=
    convolution_diff_bound_L1 (f₁ := g) (f₂ := f₀)
      (ψ := ψηC) hg hf₀ hψηC_int

  -- Replace the multiplier by 1 using the computed L¹ norm.
  have hψηC_L1_one : eLpNorm ψηC 1 volume = (1 : ℝ≥0∞) := by
    simpa using hψηC_L1.trans (by simp)

  have h_form_total :
      (fun x =>
        (∫ y, g (x - y) * (↑(ψηR y) : ℂ)) - ∫ y, f₀ (x - y) * (↑(ψηR y) : ℂ))
        = (fun x =>
            (∫ y, g (x - y) * (((↑η : ℂ) ^ n)⁻¹ * ↑(ψ (fun i => y i / η)))) -
              ∫ y, f₀ (x - y) * (((↑η : ℂ) ^ n)⁻¹ * ↑(ψ (fun i => y i / η)))) := by
    funext x
    simp [ψηR, hψηR_def, one_div, div_eq_mul_inv,
          Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow,
          Real.rpow_neg (le_of_lt hη_pos), Real.rpow_natCast,
          mul_comm, mul_left_comm, mul_assoc]
  -- Apply the bound after rewriting both convolution terms inside the difference.
  simpa [ψηC, hψηC_def, hψηC_L1_one, one_mul, h_form_total]
    using h_bound

/--
**Bound on difference of convolutions (L² case).**

‖(g - f₀) * ψ‖₂ ≤ ‖g - f₀‖₂ · ‖ψ‖₁

L² version of the above, used for L² error bounds.
-/
theorem convolution_diff_bound_L2
    (f₁ f₂ ψ : (Fin n → ℝ) → ℂ)
    (hf₁ : MemLp f₁ 2 volume)
    (hf₂ : MemLp f₂ 2 volume)
    (hψ : Integrable ψ volume) :
    eLpNorm (fun x =>
      (∫ y, f₁ (x - y) * ψ y) - (∫ y, f₂ (x - y) * ψ y)) 2 volume ≤
      eLpNorm (fun x => f₁ x - f₂ x) 2 volume * eLpNorm ψ 1 volume := by
  -- Lebesgue measure on ℝ^n is neg-invariant; provide the instance locally for this section.
  haveI : (volume : Measure (Fin n → ℝ)).IsNegInvariant := by
    let μ : Measure (Fin n → ℝ) := volume
    refine ⟨?_⟩
    set T :=
      (-1 : ℝ) •
        (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    have h_det_eq :
        LinearMap.det T =
          (-1 : ℝ) ^ Module.finrank ℝ (Fin n → ℝ) := by
      simpa [T]
        using
          (LinearMap.det_smul (-1 : ℝ)
            (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
    have h_abs_det : abs (LinearMap.det T) = (1 : ℝ) := by
      simp [h_det_eq]
    have h_det_ne_zero : LinearMap.det T ≠ 0 := by
      have h_abs_ne : abs (LinearMap.det T) ≠ 0 := by
        simp [h_abs_det]
      exact abs_ne_zero.mp h_abs_ne
    have h_map_aux :=
      Real.map_linearMap_volume_pi_eq_smul_volume_pi
        (f := T) h_det_ne_zero
    have h_abs_inv : abs ((LinearMap.det T)⁻¹) = (1 : ℝ) := by
      have := abs_inv (LinearMap.det T)
      simpa [h_abs_det, h_det_ne_zero]
        using this
    have h_scalar :
        ENNReal.ofReal (abs ((LinearMap.det T)⁻¹)) = (1 : ℝ≥0∞) := by
      simp [h_abs_inv]
    have h_T_eq_neg : (T : (Fin n → ℝ) → (Fin n → ℝ)) = fun y => -y := by
      funext y
      simp [T, LinearMap.smul_apply, Pi.smul_apply, neg_one_smul]
    have h_map :
        Measure.map (fun y : (Fin n → ℝ) => -y) volume = volume := by
      calc Measure.map (fun y : (Fin n → ℝ) => -y) volume
          = Measure.map T volume := by rw [h_T_eq_neg]
        _ = ENNReal.ofReal (abs ((LinearMap.det T)⁻¹)) • volume := h_map_aux
        _ = (1 : ℝ≥0∞) • volume := by rw [h_scalar]
        _ = volume := one_smul _ _
    have h_neg_eq_neg : (Neg.neg : (Fin n → ℝ) → (Fin n → ℝ)) = fun y => -y := by
      rfl
    have h_neg_eq :
        Measure.neg (μ := (volume : Measure (Fin n → ℝ))) = volume := by
      unfold Measure.neg
      rw [h_neg_eq_neg]
      exact h_map
    exact h_neg_eq
  -- Step 1: establish a.e. integrability of the two convolution integrands
  have hconv₁ : ∀ᵐ x ∂volume, Integrable (fun y => f₁ (x - y) * ψ y) volume := by
    simpa using
      (MeasureTheory.convolution_fiber_integrable_L2_L1
        (μ := volume) (f := f₁) (g := ψ) hf₁ hψ)
  have hconv₂ : ∀ᵐ x ∂volume, Integrable (fun y => f₂ (x - y) * ψ y) volume := by
    simpa using
      (MeasureTheory.convolution_fiber_integrable_L2_L1
        (μ := volume) (f := f₂) (g := ψ) hf₂ hψ)

  -- Step 2: rewrite the difference of convolutions as the convolution of the difference
  have h_sub_ae := convolution_sub (f₁ := f₁) (f₂ := f₂) (g := ψ) hconv₁ hconv₂
  have h_eq_eLp :
      eLpNorm (fun x =>
        (∫ y, f₁ (x - y) * ψ y) - (∫ y, f₂ (x - y) * ψ y)) 2 volume
        = eLpNorm (fun x => ∫ y, (f₁ (x - y) - f₂ (x - y)) * ψ y) 2 volume := by
    simpa using eLpNorm_congr_ae (μ := volume) (p := (2 : ℝ≥0∞)) h_sub_ae.symm

  -- Step 3: apply Young's inequality in the L² × L¹ → L² form
  have hdiff_mem : MemLp (fun x => f₁ x - f₂ x) 2 volume := hf₁.sub hf₂
  have hYoung := by
    have hg1 : MemLp ψ 1 volume := (memLp_one_iff_integrable (μ := volume)).2 hψ
    have h :=
      young_convolution_inequality (f := f₁ - f₂) (g := ψ)
        (p := (2 : ℝ≥0∞)) (q := (1 : ℝ≥0∞)) (r := (2 : ℝ≥0∞))
        (hp := by norm_num) (hq := by simp)
        (hpqr := by simp [one_div, add_comm, add_left_comm, add_assoc])
        hdiff_mem hg1
    simpa using h
  have h_bound :
      eLpNorm (fun x => ∫ y, (f₁ (x - y) - f₂ (x - y)) * ψ y) 2 volume ≤
        eLpNorm (fun x => f₁ x - f₂ x) 2 volume * eLpNorm ψ 1 volume := by
    simpa using hYoung.2

  -- Step 4: assemble the estimate using the a.e. equality
  simpa [h_eq_eLp] using h_bound

end ConvolutionDifferenceBounds
