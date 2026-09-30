import { Link } from 'react-router-dom'

export default function NotFoundPage() {
  return (
    <div className="page">
      <h1>Page not found</h1>
      <p>
        <Link to="/">Go to your notes</Link>
      </p>
    </div>
  )
}
