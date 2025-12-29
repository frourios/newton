import Newton.Gauge.LieAlgebra

open Matrix

namespace Newton

variable {N : ℕ}

/-- Adjoint ad action: ad(A)(B) = [A, B]

The ad action of su(N) element A on another element B.
This defines the map B ↦ [A, B].
-/
noncomputable def adjointAd (A : SuNAlgebra N) (B : SuNAlgebra N) : SuNAlgebra N :=
  ⁅A, B⁆

namespace adjointAd

/-- ad action preserves addition: ad(A)(B + C) = ad(A)(B) + ad(A)(C) -/
theorem add (A B C : SuNAlgebra N) :
    adjointAd A (B + C) = adjointAd A B + adjointAd A C := by
  simp only [adjointAd]
  exact lie_add A B C

/-- ad action preserves scalar multiplication: ad(A)(r • B) = r • ad(A)(B) -/
theorem smul (A : SuNAlgebra N) (r : ℝ) (B : SuNAlgebra N) :
    adjointAd A (r • B) = r • adjointAd A B := by
  simp only [adjointAd]
  apply SuNAlgebra.ext
  simp only [SuNAlgebra.lie_def, SuNAlgebra.smul_matrix]
  rw [Matrix.mul_smul, Matrix.smul_mul, smul_sub]

/-- ad action preserves zero: ad(A)(0) = 0 -/
@[simp]
theorem zero (A : SuNAlgebra N) : adjointAd A (0 : SuNAlgebra N) = 0 := by
  simp only [adjointAd]
  exact lie_zero A

/-- ad action of zero is the zero map: ad(0)(B) = 0 -/
@[simp]
theorem zero_left (B : SuNAlgebra N) : adjointAd (0 : SuNAlgebra N) B = 0 := by
  simp only [adjointAd]
  exact zero_lie B

/-- ad action on self is zero: ad(A)(A) = 0 -/
@[simp]
theorem self (A : SuNAlgebra N) : adjointAd A A = 0 := by
  simp only [adjointAd]
  exact lie_self A

/-- Antisymmetry of ad action: ad(A)(B) = -ad(B)(A) -/
theorem antisymm (A B : SuNAlgebra N) : adjointAd A B = -adjointAd B A := by
  simp only [adjointAd]
  rw [← lie_skew]

end adjointAd

/-- Leibniz rule for ad action (derivation property)

ad(A)([B, C]) = [ad(A)(B), C] + [B, ad(A)(C)]

This follows directly from the Jacobi identity.
-/
theorem adjoint_leibniz (A B C : SuNAlgebra N) :
    adjointAd A ⁅B, C⁆ = ⁅adjointAd A B, C⁆ + ⁅B, adjointAd A C⁆ := by
  simp only [adjointAd]
  exact SuNAlgebra.jacobi_identity_alt A B C

/-- Composition rule for ad action

[[A, B], C] = [A, [B, C]] - [B, [A, C]]

This is a fundamental property of the adjoint representation of Lie algebras.
-/
theorem adjointAd_bracket (A B C : SuNAlgebra N) :
    adjointAd ⁅A, B⁆ C = adjointAd A (adjointAd B C) - adjointAd B (adjointAd A C) := by
  simp only [adjointAd]
  apply SuNAlgebra.ext
  simp only [SuNAlgebra.lie_def, SuNAlgebra.sub_matrix]
  noncomm_ring

/-- Left linearity of ad action: ad(A + B) = ad(A) + ad(B) -/
theorem adjointAd_add_left (A B C : SuNAlgebra N) :
    adjointAd (A + B) C = adjointAd A C + adjointAd B C := by
  simp only [adjointAd]
  exact add_lie A B C

/-- Left scalar multiplication of ad action: ad(r • A) = r • ad(A) -/
theorem adjointAd_smul_left (r : ℝ) (A B : SuNAlgebra N) :
    adjointAd (r • A) B = r • adjointAd A B := by
  simp only [adjointAd]
  apply SuNAlgebra.ext
  simp only [SuNAlgebra.lie_def, SuNAlgebra.smul_matrix]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_sub]

/-- Killing form expressed via ad action

The relation B(X, Y) = Tr(XY) holds.
-/
theorem killingForm_via_ad [DecidableEq (Fin N)] (A B : SuNAlgebra N) :
    killingForm A B = trace (A.matrix * B.matrix) := rfl

/-- Double application of ad action: ad(A)(ad(A)(B)) = [A, [A, B]] -/
noncomputable def adjointAd2 (A B : SuNAlgebra N) : SuNAlgebra N :=
  adjointAd A (adjointAd A B)

/-- Expansion of ad(A)^2(B) = [A, [A, B]] -/
theorem adjointAd2_def (A B : SuNAlgebra N) :
    adjointAd2 A B = ⁅A, ⁅A, B⁆⁆ := rfl

/-- ad(A)^2(A) = 0 (from Jacobi identity) -/
@[simp]
theorem adjointAd2_self (A : SuNAlgebra N) : adjointAd2 A A = 0 := by
  simp only [adjointAd2, adjointAd]
  rw [lie_self]
  exact lie_zero A

end Newton
