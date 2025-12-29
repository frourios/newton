import './TheoremList.css'

interface Theorem {
  name: string
  displayName: string
  description: string
  file: string
  line: number
  category: 'analysis' | 'measure-theory' | 'convolution' | 'distribution' | 'gauge-theory'
}

const GITHUB_BASE = 'https://github.com/frourios/newton/blob/main'

const theorems: Theorem[] = [
  // Fundamental Inequalities
  {
    name: 'Newton.holder_inequality',
    displayName: 'Hölder Inequality',
    description: 'For conjugate exponents p and q, ‖fg‖₁ ≤ ‖f‖_p ‖g‖_q',
    file: 'Newton/MeasureTheory/Integral/Holder.lean',
    line: 148,
    category: 'measure-theory',
  },
  {
    name: 'Newton.young_convolution_inequality',
    displayName: 'Young Convolution Inequality',
    description: 'For 1/p + 1/q = 1 + 1/r, ‖f * g‖_r ≤ ‖f‖_p ‖g‖_q',
    file: 'Newton/Analysis/Convolution/Basic.lean',
    line: 15,
    category: 'convolution',
  },
  {
    name: 'Newton.minkowski_integral_inequality',
    displayName: 'Minkowski Integral Inequality',
    description: '‖∫ f(·,y) dμ(y)‖_p ≤ ∫ ‖f(·,y)‖_p dμ(y)',
    file: 'Newton/Analysis/Convolution/Minkowski.lean',
    line: 58,
    category: 'analysis',
  },

  // Tonelli Theorems
  {
    name: 'Newton.tonelli_nonneg_prod_eq_iterated',
    displayName: 'Tonelli Theorem',
    description: 'For non-negative measurable functions, product integral equals iterated integral',
    file: 'Newton/MeasureTheory/Integral/Tonelli.lean',
    line: 34,
    category: 'measure-theory',
  },

  // Lp Space Theory
  {
    name: 'Newton.lp_duality_pairing',
    displayName: 'Lp Duality Pairing',
    description: 'The dual space of Lᵖ is Lᵍ for conjugate exponents',
    file: 'Newton/MeasureTheory/Function/LpSpace/Duality.lean',
    line: 28,
    category: 'measure-theory',
  },
  {
    name: 'Newton.lp_duality_norm_le_of_pairing_bound',
    displayName: 'Lp Duality Norm Bound',
    description: 'Duality characterization of Lp norm via supremum over unit ball',
    file: 'Newton/MeasureTheory/Function/LpSpace/Duality.lean',
    line: 625,
    category: 'measure-theory',
  },

  // Mollifier Convergence
  {
    name: 'Newton.mollifier_converges_continuous',
    displayName: 'Mollifier Convergence (Continuous)',
    description: 'Convolution with scaled mollifier converges uniformly for continuous functions',
    file: 'Newton/Analysis/Convolution/ApproximateIdentity.lean',
    line: 327,
    category: 'convolution',
  },
  {
    name: 'Newton.mollifier_converges_Lp',
    displayName: 'Mollifier Convergence (Lp)',
    description: 'Convolution with mollifier converges in Lᵖ norm as scale → 0',
    file: 'Newton/Analysis/Convolution/ApproximateIdentity.lean',
    line: 782,
    category: 'convolution',
  },

  // Schwartz Density
  {
    name: 'Newton.schwartz_dense_L1_L2_simultaneous',
    displayName: 'Schwartz Density in L¹ ∩ L²',
    description: 'Schwartz functions are dense in L¹ ∩ L² simultaneously',
    file: 'Newton/Analysis/Distribution/SchwartzDensity.lean',
    line: 1328,
    category: 'distribution',
  },
  {
    name: 'Newton.smooth_compactSupport_dense_L1_L2_real',
    displayName: 'C∞_c Dense in L¹ ∩ L²',
    description: 'Smooth compactly supported functions are dense in L¹ ∩ L²',
    file: 'Newton/Analysis/Distribution/SchwartzDensity.lean',
    line: 1911,
    category: 'distribution',
  },

  // Convolution Bounds
  {
    name: 'Newton.convolution_diff_bound_L1',
    displayName: 'Convolution Difference Bound (L¹)',
    description: 'L¹ bound on the difference of convolutions',
    file: 'Newton/Analysis/Convolution/Bounds.lean',
    line: 331,
    category: 'convolution',
  },
  {
    name: 'Newton.convolution_diff_bound_L2',
    displayName: 'Convolution Difference Bound (L²)',
    description: 'L² bound on the difference of convolutions',
    file: 'Newton/Analysis/Convolution/Bounds.lean',
    line: 533,
    category: 'convolution',
  },

  // Gauge Theory - Lie Algebra
  {
    name: 'Newton.SuNAlgebra.jacobi_identity',
    displayName: 'Jacobi Identity for su(N)',
    description: '[A, [B, C]] + [B, [C, A]] + [C, [A, B]] = 0 for su(N) Lie algebra',
    file: 'Newton/Gauge/LieAlgebra.lean',
    line: 209,
    category: 'gauge-theory',
  },
  {
    name: 'Newton.SuNAlgebra.trace_square_nonpos',
    displayName: 'Trace Square Non-positive',
    description: 'For anti-Hermitian A, Tr(A²) has non-positive real part',
    file: 'Newton/Gauge/LieAlgebra.lean',
    line: 289,
    category: 'gauge-theory',
  },
  {
    name: 'Newton.killingForm_symm',
    displayName: 'Killing Form Symmetry',
    description: 'The Killing form B(A, B) = Tr(AB) is symmetric',
    file: 'Newton/Gauge/LieAlgebra.lean',
    line: 304,
    category: 'gauge-theory',
  },

  // Gauge Theory - SU(2) Commutation Relations
  {
    name: 'Newton.su2_bracket_12',
    displayName: 'su(2) Commutation [T₁, T₂] = T₃',
    description: 'Fundamental commutation relation of su(2) generators',
    file: 'Newton/Gauge/GellMannMatrices.lean',
    line: 226,
    category: 'gauge-theory',
  },
  {
    name: 'Newton.su2_bracket_23',
    displayName: 'su(2) Commutation [T₂, T₃] = T₁',
    description: 'Cyclic commutation relation of su(2) generators',
    file: 'Newton/Gauge/GellMannMatrices.lean',
    line: 307,
    category: 'gauge-theory',
  },
  {
    name: 'Newton.su2_bracket_31',
    displayName: 'su(2) Commutation [T₃, T₁] = T₂',
    description: 'Cyclic commutation relation of su(2) generators',
    file: 'Newton/Gauge/GellMannMatrices.lean',
    line: 387,
    category: 'gauge-theory',
  },
  {
    name: 'Newton.exists_noncommuting_elements',
    displayName: 'Non-commutativity of su(N)',
    description: 'For N ≥ 2, su(N) has non-commuting elements (non-Abelian)',
    file: 'Newton/Gauge/GellMannMatrices.lean',
    line: 722,
    category: 'gauge-theory',
  },

  // Gauge Theory - Adjoint Action
  {
    name: 'Newton.adjointAction.bracket',
    displayName: 'Adjoint Action Preserves Bracket',
    description: 'Ad(g)[A, B] = [Ad(g)A, Ad(g)B] for SU(N) gauge transformation',
    file: 'Newton/Gauge/GaugeTransformation.lean',
    line: 177,
    category: 'gauge-theory',
  },
  {
    name: 'Newton.adjointAction.compose',
    displayName: 'Adjoint Action Composition',
    description: 'Ad(gh)(A) = Ad(g)(Ad(h)(A)) - group homomorphism property',
    file: 'Newton/Gauge/GaugeTransformation.lean',
    line: 156,
    category: 'gauge-theory',
  },
  {
    name: 'Newton.adjoint_leibniz',
    displayName: 'Adjoint Leibniz Rule',
    description: 'ad(A)([B, C]) = [ad(A)(B), C] + [B, ad(A)(C)] - derivation property',
    file: 'Newton/Gauge/StructureConstants.lean',
    line: 64,
    category: 'gauge-theory',
  },
]

const categoryLabels: Record<Theorem['category'], string> = {
  'analysis': 'Analysis',
  'measure-theory': 'Measure Theory',
  'convolution': 'Convolution',
  'distribution': 'Distribution Theory',
  'gauge-theory': 'Gauge Theory',
}

const categoryColors: Record<Theorem['category'], string> = {
  'analysis': '#2563eb',
  'measure-theory': '#7c3aed',
  'convolution': '#059669',
  'distribution': '#dc2626',
  'gauge-theory': '#d97706',
}

export function TheoremList() {
  return (
    <div className="theorem-list">
      {theorems.map((theorem) => (
        <a
          key={theorem.name}
          href={`${GITHUB_BASE}/${theorem.file}#L${theorem.line}`}
          target="_blank"
          rel="noopener noreferrer"
          className="theorem-card"
        >
          <div className="theorem-header">
            <h3 className="theorem-name">{theorem.displayName}</h3>
            <span
              className="theorem-category"
              style={{ backgroundColor: categoryColors[theorem.category] }}
            >
              {categoryLabels[theorem.category]}
            </span>
          </div>
          <p className="theorem-description">{theorem.description}</p>
          <div className="theorem-meta">
            <code className="theorem-id">{theorem.name}</code>
            <span className="theorem-link">
              View source →
            </span>
          </div>
        </a>
      ))}
    </div>
  )
}
