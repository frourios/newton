import { useEffect } from 'react'

declare global {
  interface Window {
    MathJax?: {
      Hub?: {
        Config: (config: unknown) => void
        Queue: (callback: unknown) => void
      }
      typeset?: () => void
    }
  }
}

export function MathJaxLoader() {
  useEffect(() => {
    // Add MathJax configuration script
    const configScript = document.createElement('script')
    configScript.type = 'text/x-mathjax-config'
    configScript.text = `
      MathJax.Hub.Config({
        tex2jax: {
          inlineMath: [['$','$'], ['\\\\(','\\\\)']],
          displayMath: [['$$','$$'], ['\\\\[','\\\\]']],
          processEscapes: true
        },
        TeX: {
          equationNumbers: {
            autoNumber: "AMS"
          }
        }
      });
    `
    document.head.appendChild(configScript)

    // Add MathJax library script
    const script = document.createElement('script')
    script.type = 'text/javascript'
    script.async = true
    script.src = 'https://cdnjs.cloudflare.com/ajax/libs/mathjax/2.7.7/MathJax.js?config=TeX-AMS-MML_HTMLorMML'
    document.head.appendChild(script)

    return () => {
      document.head.removeChild(configScript)
      document.head.removeChild(script)
    }
  }, [])

  return null
}
