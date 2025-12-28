import type { ReactNode } from 'react'
import { ThemeToggle } from './ThemeToggle'
import './Layout.css'

interface LayoutProps {
  children: ReactNode
  title?: string
  description?: string
  showGitHubButton?: boolean
}

export function Layout({
  children,
  title = 'Newton',
  description = 'Physics library for Lean',
  showGitHubButton = true
}: LayoutProps) {
  const repositoryUrl = 'https://github.com/frourios/newton'
  const repositoryName = 'newton'

  return (
    <>
      <a id="skip-to-content" href="#content">Skip to the content.</a>

      <header className="page-header" role="banner">
        <ThemeToggle />
        <h1 className="project-name">{title}</h1>
        <h2 className="project-tagline">{description}</h2>
        <a href="/docs" className="btn">Documentation</a>
        {showGitHubButton && (
          <a href={repositoryUrl} className="btn">GitHub</a>
        )}
      </header>

      <main id="content" className="main-content" role="main">
        {children}

        <footer className="site-footer">
          {showGitHubButton && (
            <span className="site-footer-owner">
              <a href={repositoryUrl}>{repositoryName}</a>
              {' '}is maintained by Frourio, Inc. Visit the GitHub repository for more information.
            </span>
          )}
        </footer>
      </main>
    </>
  )
}
