//@ aim NOTES-ESCAPE: WHILE a dialog is open, the app shall let the user get back to the notes screen.
//@   by: escape
//@ [NOTES-ESCAPE] ui escape: always reachable screen "/" and not overlay from overlay

//@ aim NOTES-SETTINGS: WHEN the user changes a setting, the app shall keep it the next time it is opened.
//@   by: settings-shown, theme, autosave, font-size
//@ [NOTES-SETTINGS] ui settings-shown: reachable radio "Dark" is enabled
//@ [NOTES-SETTINGS] ui theme: persists radio "Dark"
//@ [NOTES-SETTINGS] ui autosave: persists checkbox "Autosave notes while typing"
//@ [NOTES-SETTINGS] ui font-size: persists combobox "Font size"

//@ aim NOTES-CONTROLS: The app shall never cover its menu button or a dialog's close button.
//@   by: menu-visible, close-visible
//@ [NOTES-CONTROLS] ui menu-visible: unobscured button "Menu"
//@ [NOTES-CONTROLS] ui close-visible: unobscured button "Close"

//@ aim NOTES-KEYBOARD: WHILE a dialog with a Close button is open, pressing Escape shall close it.
//@   by: escape-key
//@ [NOTES-KEYBOARD] ui escape-key: always reachable not overlay from overlay and button "Close" by key "Escape"

//@ aim NOTES-SIGN-OUT: WHEN the user signs out, the app shall show the sign-in screen.
//@   by: sign-out
//@ [NOTES-SIGN-OUT] ui sign-out: always reachable screen "/login" from screen "/account"

import { useState } from 'react'
import { Navigate, Route, Routes, useLocation, useNavigate } from 'react-router-dom'
import { NavBar } from './components/NavBar'
import { Onboarding } from './components/Onboarding'
import { ShortcutsDialog } from './components/ShortcutsDialog'
import { RequireAuth } from './components/RequireAuth'
import { useAuth } from './context/AuthContext'
import { useLocalStorage } from './hooks/useLocalStorage'
import { useHotkeys } from './hooks/useHotkeys'
import NotesPage from './pages/NotesPage'
import SettingsPage from './pages/SettingsPage'
import AccountPage from './pages/AccountPage'
import LoginPage from './pages/LoginPage'
import NotFoundPage from './pages/NotFoundPage'

export default function App() {
  const { user } = useAuth()
  const navigate = useNavigate()
  const location = useLocation()
  const [onboarded, setOnboarded] = useLocalStorage('notes.onboarded', false)
  const [showShortcuts, setShowShortcuts] = useState(false)

  useHotkeys({
    'shift+?': () => user && setShowShortcuts(true),
    'mod+,': () => user && navigate('/settings'),
  })

  const onLogin = location.pathname === '/login'

  return (
    <div className="app">
      {!onLogin && user && <NavBar onShowShortcuts={() => setShowShortcuts(true)} />}
      <main className="content">
        <Routes>
          <Route path="/login" element={<LoginPage />} />
          <Route
            path="/"
            element={
              <RequireAuth>
                <NotesPage />
              </RequireAuth>
            }
          />
          <Route
            path="/notes/:id"
            element={
              <RequireAuth>
                <NotesPage />
              </RequireAuth>
            }
          />
          <Route
            path="/settings"
            element={
              <RequireAuth>
                <SettingsPage />
              </RequireAuth>
            }
          />
          <Route
            path="/account"
            element={
              <RequireAuth>
                <AccountPage />
              </RequireAuth>
            }
          />
          <Route path="/home" element={<Navigate to="/" replace />} />
          <Route path="*" element={<NotFoundPage />} />
        </Routes>
      </main>
      {user && !onboarded && <Onboarding onFinish={() => setOnboarded(true)} />}
      {showShortcuts && <ShortcutsDialog onClose={() => setShowShortcuts(false)} />}
    </div>
  )
}
