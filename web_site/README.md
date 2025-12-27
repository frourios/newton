# Newton Website

This is the official website for Newton, a Physics library for Lean, built with Vite + React + TypeScript.

## Migration from Jekyll

This project is migrated from the Jekyll-based `home_page` directory. The migration includes:

- ✅ Layout matching the Cayman theme
- ✅ Home page
- ✅ 404 error page
- ✅ MathJax support for mathematical notation
- ✅ Responsive design with mobile support
- ✅ Custom favicon

## Development

```bash
# Install dependencies
npm install

# Start development server
npm run dev

# Build for production
npm run build

# Preview production build
npm run preview
```

## Project Structure

```
web_site/
├── public/
│   └── favicon.svg          # Newton logo
├── src/
│   ├── components/
│   │   ├── Layout.tsx       # Main layout component (Cayman theme)
│   │   ├── Layout.css       # Layout styles
│   │   └── MathJax.tsx      # MathJax integration
│   ├── pages/
│   │   ├── Home.tsx         # Home page
│   │   ├── NotFound.tsx     # 404 page
│   │   └── NotFound.css     # 404 styles
│   ├── App.tsx              # App router
│   ├── main.tsx             # Entry point
│   └── index.css            # Global styles
└── index.html               # HTML template
```

## Features

### Layout Component

The `Layout` component provides the main page structure matching the Jekyll Cayman theme:

- Header with project name and tagline
- Documentation and GitHub buttons
- Main content area
- Footer with repository information

### MathJax Support

MathJax is automatically loaded and configured for rendering mathematical equations. Use standard LaTeX syntax:

- Inline math: `$...$` or `\\(...\\)`
- Display math: `$$...$$` or `\\[...\\]`

### Routing

The site uses React Router for client-side routing:

- `/` - Home page
- `*` - 404 page for all other routes

## Deployment

The built files in the `dist/` directory can be deployed to any static hosting service:

- GitHub Pages
- Netlify
- Vercel
- Cloudflare Pages

## License

This project follows the same license as the Newton repository.
