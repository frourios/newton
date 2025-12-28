import { Layout } from '../components/Layout'
import { TheoremList } from '../components/TheoremList'
import './Home.css'

export function Home() {
  return (
    <Layout>
      <section className="hero-section">
        <h2>Verified Physics in Lean</h2>
        <p className="hero-description">
          Newton is building a world where anyone who discovers new theories in physics
          and mathematics can prove their consistency without peer review. Every theorem
          on the main branch is machine-verified with <strong>no axioms, sorry, admit, or trivial</strong>.
        </p>
        <div className="hero-badges">
          <span className="badge badge-verified">100% Verified</span>
          <span className="badge badge-lean">Lean 4</span>
          <span className="badge badge-mathlib">Mathlib</span>
        </div>
      </section>

      <section className="features-section">
        <h2>Why Newton?</h2>
        <div className="features-grid">
          <div className="feature-card">
            <div className="feature-icon">🔬</div>
            <h3>Machine Verification</h3>
            <p>Every proof is checked by the Lean compiler. If it builds, the mathematics is correct.</p>
          </div>
          <div className="feature-card">
            <div className="feature-icon">🌍</div>
            <h3>Open Science</h3>
            <p>No peer review gatekeepers. Anyone can verify and build upon our foundations.</p>
          </div>
          <div className="feature-card">
            <div className="feature-icon">🚀</div>
            <h3>Future Ready</h3>
            <p>Infrastructure prepared for unified field theories and Millennium Prize Problems.</p>
          </div>
        </div>
      </section>

      <section className="theorems-section">
        <h2>Proven Theorems</h2>
        <p className="section-description">
          Browse our collection of formally verified theorems. Each links directly to its
          complete proof in the source code.
        </p>
        <TheoremList />
      </section>

      <section className="quickstart-section">
        <h2>Quick Start</h2>
        <p>Add Newton to your Lean project:</p>
        <div className="code-block">
          <code>
            <span className="code-comment"># lakefile.toml</span><br />
            <span className="code-key">[[require]]</span><br />
            <span className="code-attr">name</span> = <span className="code-string">"Newton"</span><br />
            <span className="code-attr">git</span>  = <span className="code-string">"https://github.com/frourios/newton.git"</span><br />
            <span className="code-attr">rev</span>  = <span className="code-string">"main"</span>
          </code>
        </div>
      </section>
    </Layout>
  )
}
