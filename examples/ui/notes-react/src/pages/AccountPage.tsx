import { useState } from 'react'
import { useNavigate } from 'react-router-dom'
import { useAuth } from '../context/AuthContext'
import { useNotes } from '../context/NotesContext'
import { useSettings } from '../context/SettingsContext'
import { useToast } from '../context/ToastContext'
import { Modal } from '../components/Modal'

export default function AccountPage() {
  const { user, signOut } = useAuth()
  const { notes } = useNotes()
  const { settings } = useSettings()
  const toast = useToast()
  const navigate = useNavigate()
  const [confirming, setConfirming] = useState(false)

  const handleSignOut = () => {
    signOut()
    toast('Signed out')
    navigate('/login')
  }

  return (
    <div className="page">
      <h1>Account</h1>
      <section className="card">
        <dl className="details">
          <dt>Name</dt>
          <dd>{settings.displayName || '—'}</dd>
          <dt>Email</dt>
          <dd>{user?.email}</dd>
          <dt>Notes</dt>
          <dd>{notes.length}</dd>
        </dl>
        <button className="button button-danger" onClick={() => setConfirming(true)}>
          Sign out
        </button>
      </section>
      {confirming && (
        <Modal
          title="Sign out?"
          onClose={() => setConfirming(false)}
          footer={
            <>
              <button className="button" onClick={() => setConfirming(false)}>
                Cancel
              </button>
              <button className="button button-danger" onClick={handleSignOut}>
                Sign out
              </button>
            </>
          }
        >
          <p>Your notes stay on this device. You can sign back in any time.</p>
        </Modal>
      )}
    </div>
  )
}
