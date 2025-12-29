import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Lie.OfAssociative

open Matrix

namespace Newton

variable {N : ℕ}

/-- Lie algebra su(N) of SU(N)
N×N complex matrices A satisfying:
1. Traceless: Tr(A) = 0
2. Anti-Hermitian: A† = -A (where † denotes conjugate transpose)
-/
structure SuNAlgebra (N : ℕ) where
  /-- Matrix representation -/
  matrix : Matrix (Fin N) (Fin N) ℂ
  /-- Traceless condition -/
  trace_zero : trace matrix = 0
  /-- Anti-Hermitian condition: A† = -A -/
  anti_hermitian : conjTranspose matrix = -matrix

namespace SuNAlgebra

/-- Zero element -/
instance : Zero (SuNAlgebra N) where
  zero := {
    matrix := 0
    trace_zero := by simp [trace]
    anti_hermitian := by simp [conjTranspose]
  }

/-- Addition -/
instance : Add (SuNAlgebra N) where
  add A B := {
    matrix := A.matrix + B.matrix
    trace_zero := by
      simp only [trace_add, A.trace_zero, B.trace_zero, add_zero]
    anti_hermitian := by
      simp only [conjTranspose_add, A.anti_hermitian, B.anti_hermitian, neg_add]
  }

/-- Negation -/
instance : Neg (SuNAlgebra N) where
  neg A := {
    matrix := -A.matrix
    trace_zero := by simp [trace_neg, A.trace_zero]
    anti_hermitian := by
      simp only [conjTranspose_neg, A.anti_hermitian, neg_neg]
  }

/-- Subtraction -/
instance : Sub (SuNAlgebra N) where
  sub A B := A + (-B)

/-- Real scalar multiplication (su(N) is a real vector space) -/
instance : SMul ℝ (SuNAlgebra N) where
  smul r A := {
    matrix := (r : ℂ) • A.matrix
    trace_zero := by
      simp only [trace_smul, A.trace_zero, smul_zero]
    anti_hermitian := by
      rw [conjTranspose_smul, A.anti_hermitian]
      simp only [Complex.star_def, Complex.conj_ofReal, smul_neg]
  }

/-- Equality via matrix equality -/
theorem ext {A B : SuNAlgebra N} (h : A.matrix = B.matrix) : A = B := by
  cases A; cases B
  simp_all

/-- SuNAlgebra equality is equivalent to matrix equality -/
@[simp]
theorem matrix_eq_iff {A B : SuNAlgebra N} : A.matrix = B.matrix ↔ A = B :=
  ⟨ext, fun h => h ▸ rfl⟩

/-- If matrix is zero, then the element is zero -/
theorem ext_matrix {A : SuNAlgebra N} (h : A.matrix = 0) : A = 0 :=
  ext h

/-- Zero element has zero matrix -/
@[simp]
theorem zero_matrix : (0 : SuNAlgebra N).matrix = 0 := rfl

/-- Addition is compatible with matrix addition -/
@[simp]
theorem add_matrix (A B : SuNAlgebra N) : (A + B).matrix = A.matrix + B.matrix := rfl

/-- Negation is compatible with matrix negation -/
@[simp]
theorem neg_matrix (A : SuNAlgebra N) : (-A).matrix = -A.matrix := rfl

/-- Scalar multiplication is compatible with matrix scalar multiplication -/
@[simp]
theorem smul_matrix (r : ℝ) (A : SuNAlgebra N) : (r • A).matrix = (r : ℂ) • A.matrix := rfl

/-- Subtraction is compatible with matrix subtraction -/
@[simp]
theorem sub_matrix (A B : SuNAlgebra N) : (A - B).matrix = A.matrix - B.matrix := rfl

/-- Additive commutative group instance -/
instance : AddCommGroup (SuNAlgebra N) where
  add_assoc a b c := by
    apply ext
    simp only [add_matrix, _root_.add_assoc]
  zero_add a := by
    apply ext
    simp only [add_matrix, zero_matrix, _root_.zero_add]
  add_zero a := by
    apply ext
    simp only [add_matrix, zero_matrix, _root_.add_zero]
  add_comm a b := by
    apply ext
    simp only [add_matrix, _root_.add_comm]
  nsmul n a := {
    matrix := n • a.matrix
    trace_zero := by simp only [trace_smul, a.trace_zero, smul_zero]
    anti_hermitian := by
      rw [conjTranspose_smul, a.anti_hermitian, smul_neg]
      simp only [star_trivial]
  }
  nsmul_zero a := by
    apply ext
    simp only [zero_smul, zero_matrix]
  nsmul_succ n a := by
    apply ext
    simp only [add_matrix]
    rw [add_smul, one_smul]
  zsmul n a := {
    matrix := n • a.matrix
    trace_zero := by simp only [trace_smul, a.trace_zero, smul_zero]
    anti_hermitian := by
      rw [conjTranspose_smul, a.anti_hermitian, smul_neg]
      simp only [star_trivial]
  }
  zsmul_zero' a := by
    apply ext
    simp only [zero_smul, zero_matrix]
  zsmul_succ' n a := by
    apply ext
    simp only [add_matrix, Int.ofNat_eq_coe]
    rw [show (↑(n.succ) : ℤ) = (↑n : ℤ) + 1 from Int.natCast_succ n, add_smul, one_smul]
  zsmul_neg' n a := by
    apply ext
    simp only [neg_matrix, Int.negSucc_eq]
    rw [show (↑(n.succ) : ℤ) = (↑n : ℤ) + 1 from Int.natCast_succ n]
    rw [neg_smul]
  neg_add_cancel a := by
    apply ext
    simp only [add_matrix, neg_matrix, zero_matrix, _root_.neg_add_cancel]

end SuNAlgebra

/-- Lie bracket [A, B] = AB - BA for SuNAlgebra

The Lie bracket of two su(N) elements is again in su(N).
Uses Mathlib's Lie bracket on the underlying matrices.
-/
noncomputable def SuNAlgebra.lie (A B : SuNAlgebra N) : SuNAlgebra N where
  matrix := ⁅A.matrix, B.matrix⁆
  trace_zero := by
    rw [Ring.lie_def, trace_sub, trace_mul_comm]
    exact sub_self _
  anti_hermitian := by
    rw [Ring.lie_def]
    simp only [conjTranspose_sub, conjTranspose_mul]
    rw [A.anti_hermitian, B.anti_hermitian]
    simp only [neg_mul, mul_neg, neg_neg, neg_sub]

/-- LieRing instance for SuNAlgebra using Mathlib's Lie structure -/
noncomputable instance : LieRing (SuNAlgebra N) where
  bracket := SuNAlgebra.lie
  add_lie a b c := by
    apply SuNAlgebra.ext
    simp only [SuNAlgebra.lie, SuNAlgebra.add_matrix]
    rw [Ring.lie_def, Ring.lie_def, Ring.lie_def]
    noncomm_ring
  lie_add a b c := by
    apply SuNAlgebra.ext
    simp only [SuNAlgebra.lie, SuNAlgebra.add_matrix]
    rw [Ring.lie_def, Ring.lie_def, Ring.lie_def]
    noncomm_ring
  lie_self a := by
    apply SuNAlgebra.ext
    simp only [SuNAlgebra.lie, SuNAlgebra.zero_matrix]
    rw [Ring.lie_def]
    exact sub_self _
  leibniz_lie a b c := by
    apply SuNAlgebra.ext
    simp only [SuNAlgebra.lie, SuNAlgebra.add_matrix]
    simp only [Ring.lie_def]
    noncomm_ring

/-- Matrix representation of Lie bracket -/
@[simp]
theorem SuNAlgebra.lie_matrix (A B : SuNAlgebra N) :
    (⁅A, B⁆ : SuNAlgebra N).matrix = ⁅A.matrix, B.matrix⁆ := rfl

/-- Lie bracket expanded as commutator -/
theorem SuNAlgebra.lie_def (A B : SuNAlgebra N) :
    (⁅A, B⁆ : SuNAlgebra N).matrix = A.matrix * B.matrix - B.matrix * A.matrix :=
  Ring.lie_def A.matrix B.matrix

/-- Jacobi identity follows from Mathlib's lie_jacobi -/
theorem SuNAlgebra.jacobi_identity (A B C : SuNAlgebra N) :
    ⁅A, ⁅B, C⁆⁆ + ⁅B, ⁅C, A⁆⁆ + ⁅C, ⁅A, B⁆⁆ = (0 : SuNAlgebra N) := by
  apply SuNAlgebra.ext
  simp only [lie_matrix, SuNAlgebra.add_matrix, SuNAlgebra.zero_matrix]
  exact lie_jacobi A.matrix B.matrix C.matrix

/-- Alternative form of Jacobi identity -/
theorem SuNAlgebra.jacobi_identity_alt (A B C : SuNAlgebra N) :
    ⁅A, ⁅B, C⁆⁆ = ⁅⁅A, B⁆, C⁆ + ⁅B, ⁅A, C⁆⁆ := by
  apply SuNAlgebra.ext
  simp only [lie_matrix, SuNAlgebra.add_matrix]
  simp only [Ring.lie_def]
  noncomm_ring

/-- Real part of star z * z equals |z|² and is non-negative -/
theorem star_mul_self_re_nonneg (z : ℂ) : (star z * z).re ≥ 0 := by
  have h : star z * z = Complex.normSq z := by
    rw [Complex.normSq_eq_conj_mul_self]
    rfl
  rw [h]
  simp only [Complex.normSq_nonneg, ge_iff_le, Complex.ofReal_re]

/-- Real part of a sum equals sum of real parts -/
theorem Complex.re_finset_sum {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℂ) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s hnotin ih => simp [Finset.sum_insert hnotin, ih]

/-- Real part of Tr(A†A) is non-negative (diagonal elements of A†A are sums of |A_ij|²) -/
theorem trace_conjTranspose_mul_self_re_nonneg (M : Matrix (Fin N) (Fin N) ℂ) :
    (trace (conjTranspose M * M)).re ≥ 0 := by
  unfold trace diag
  simp only [conjTranspose_apply, mul_apply]
  have h : ∀ i j : Fin N, (star (M j i) * M j i).re ≥ 0 :=
    fun i j => star_mul_self_re_nonneg (M j i)
  simp only [ge_iff_le]
  rw [Complex.re_finset_sum]
  apply Finset.sum_nonneg
  intro i _
  rw [Complex.re_finset_sum]
  apply Finset.sum_nonneg
  intro j _
  exact h i j

/-- For non-zero matrix, Tr(M†M) > 0 -/
theorem trace_conjTranspose_mul_self_re_pos_of_ne_zero (M : Matrix (Fin N) (Fin N) ℂ)
    (hM : M ≠ 0) : (trace (conjTranspose M * M)).re > 0 := by
  have h_exists : ∃ i j, M i j ≠ 0 := by
    by_contra h_all_zero
    push_neg at h_all_zero
    apply hM
    ext i j
    exact h_all_zero i j
  obtain ⟨i₀, j₀, h_ne⟩ := h_exists
  unfold trace diag
  simp only [conjTranspose_apply, mul_apply]
  rw [Complex.re_finset_sum]
  apply Finset.sum_pos'
  · intro i _
    rw [Complex.re_finset_sum]
    apply Finset.sum_nonneg
    intro j _
    exact star_mul_self_re_nonneg (M j i)
  · use j₀, Finset.mem_univ j₀
    rw [Complex.re_finset_sum]
    apply Finset.sum_pos'
    · intro j _
      exact star_mul_self_re_nonneg (M j j₀)
    · use i₀, Finset.mem_univ i₀
      have h_pos : Complex.normSq (M i₀ j₀) > 0 := Complex.normSq_pos.mpr h_ne
      have h_eq : (star (M i₀ j₀) * M i₀ j₀).re = Complex.normSq (M i₀ j₀) := by
        set z := M i₀ j₀
        simp only [Complex.star_def]
        simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, neg_mul, sub_neg_eq_add,
                   Complex.normSq_apply]
      rw [h_eq]
      exact h_pos

/-- Square of an su(N) element has non-positive trace (Tr(A²) ≤ 0) -/
theorem SuNAlgebra.trace_square_nonpos (A : SuNAlgebra N) :
    (trace (A.matrix * A.matrix)).re ≤ 0 := by
  have h : A.matrix * A.matrix = -(conjTranspose A.matrix * A.matrix) := by
    rw [A.anti_hermitian]
    simp only [neg_mul, neg_neg]
  rw [h]
  simp only [trace_neg, Complex.neg_re]
  apply neg_nonpos_of_nonneg
  exact trace_conjTranspose_mul_self_re_nonneg A.matrix

/-- Killing form: B(A, B) = Tr(AB) -/
noncomputable def killingForm [DecidableEq (Fin N)] (A B : SuNAlgebra N) : ℂ :=
  trace (A.matrix * B.matrix)

/-- Killing form is symmetric -/
theorem killingForm_symm [DecidableEq (Fin N)] (A B : SuNAlgebra N) :
    killingForm A B = killingForm B A := by
  unfold killingForm
  exact trace_mul_comm A.matrix B.matrix

/-- Bilinearity of Killing form (left) -/
theorem killingForm_add_left [DecidableEq (Fin N)] (A B C : SuNAlgebra N) :
    killingForm (A + B) C = killingForm A C + killingForm B C := by
  unfold killingForm
  simp only [SuNAlgebra.add_matrix, add_mul, trace_add]

/-- Bilinearity of Killing form (right) -/
theorem killingForm_add_right [DecidableEq (Fin N)] (A B C : SuNAlgebra N) :
    killingForm A (B + C) = killingForm A B + killingForm A C := by
  unfold killingForm
  simp only [SuNAlgebra.add_matrix, mul_add, trace_add]

end Newton
