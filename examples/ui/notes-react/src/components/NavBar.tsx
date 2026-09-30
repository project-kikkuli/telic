import { useEffect, useState } from 'react'
import { NavLink, useLocation } from 'react-router-dom'
import { useAuth } from '../context/AuthContext'
import { useSettings } from '../context/SettingsContext'

export function NavBar({ onShowShortcuts }: { onShowShortcuts: () => void }) {
  const [open, setOpen] = useState(false)
  const { user } = useAuth()
  const { settings } = useSettings()
  const location = useLocation()

  useEffect(() => setOpen(false), [location.pathname])

  const name = settings.displayName || user?.email

  return (
    <header className="navbar">
      <NavLink to="/" className="brand">
        📝 Notes
      </NavLink>
      <button
        className="hamburger"
        aria-label="Menu"
        aria-expanded={open}
        aria-controls="main-menu"
        onClick={() => setOpen((o) => !o)}
      >
        <span />
        <span />
        <span />
      </button>
      <nav id="main-menu" className={open ? 'menu open' : 'menu'}>
        <NavLink to="/" end>
          Notes
        </NavLink>
        <NavLink to="/settings">Settings</NavLink>
        <NavLink to="/account">Account</NavLink>
        <button className="link-button" onClick={onShowShortcuts}>
          Shortcuts
        </button>
        {name && <span className="nav-user">{name}</span>}
      </nav>
    </header>
  )
}
