import { useEffect, useMemo, useRef, useState } from 'react'
import { Link, useNavigate, useParams } from 'react-router-dom'
import { useNotes } from '../context/NotesContext'
import { useSettings } from '../context/SettingsContext'
import { useToast } from '../context/ToastContext'
import { useHotkeys } from '../hooks/useHotkeys'
import { ConfirmDeleteModal } from '../components/ConfirmDeleteModal'
import type { Note } from '../types'

function formatDate(ts: number) {
  return new Date(ts).toLocaleString(undefined, { month: 'short', day: 'numeric', hour: 'numeric', minute: '2-digit' })
}

export default function NotesPage() {
  const { id } = useParams()
  const { notes, createNote, deleteNote } = useNotes()
  const navigate = useNavigate()
  const toast = useToast()
  const [query, setQuery] = useState('')
  const [pendingDelete, setPendingDelete] = useState<Note | null>(null)
  const searchRef = useRef<HTMLInputElement>(null)

  const filtered = useMemo(() => {
    const q = query.trim().toLowerCase()
    if (!q) return notes
    return notes.filter((n) => n.title.toLowerCase().includes(q) || n.body.toLowerCase().includes(q))
  }, [notes, query])

  const selected = notes.find((n) => n.id === id)

  const handleNew = () => {
    const note = createNote()
    navigate(`/notes/${note.id}`)
  }

  useHotkeys({
    n: handleNew,
    '/': () => searchRef.current?.focus(),
  })

  const confirmDelete = () => {
    if (!pendingDelete) return
    deleteNote(pendingDelete.id)
    toast(`Deleted “${pendingDelete.title || 'Untitled'}”`, 'success')
    setPendingDelete(null)
    navigate('/')
  }

  return (
    <div className={selected ? 'notes-layout has-selection' : 'notes-layout'}>
      <aside className="notes-sidebar" aria-label="Notes list">
        <div className="notes-sidebar-header">
          <input
            ref={searchRef}
            type="search"
            placeholder="Search notes"
            aria-label="Search notes"
            value={query}
            onChange={(e) => setQuery(e.target.value)}
          />
          <button className="button button-primary" onClick={handleNew}>
            + New
          </button>
        </div>
        {filtered.length === 0 ? (
          <p className="empty">{query ? 'No notes match your search.' : 'No notes yet.'}</p>
        ) : (
          <ul className="notes-list">
            {filtered.map((n) => (
              <li key={n.id}>
                <Link to={`/notes/${n.id}`} className={n.id === id ? 'note-item active' : 'note-item'}>
                  <strong>{n.title || 'Untitled'}</strong>
                  <span className="note-preview">{n.body.slice(0, 60) || 'No content'}</span>
                  <time>{formatDate(n.updatedAt)}</time>
                </Link>
              </li>
            ))}
          </ul>
        )}
      </aside>
      <section className="notes-editor">
        {selected ? (
          <Editor key={selected.id} note={selected} onDelete={() => setPendingDelete(selected)} />
        ) : id ? (
          <div className="placeholder">
            <p>That note doesn’t exist.</p>
            <Link to="/">Back to notes</Link>
          </div>
        ) : (
          <div className="placeholder">
            <p>Select a note or create a new one.</p>
          </div>
        )}
      </section>
      {pendingDelete && (
        <ConfirmDeleteModal
          noteTitle={pendingDelete.title}
          onConfirm={confirmDelete}
          onCancel={() => setPendingDelete(null)}
        />
      )}
    </div>
  )
}

function Editor({ note, onDelete }: { note: Note; onDelete: () => void }) {
  const { updateNote } = useNotes()
  const { settings } = useSettings()
  const toast = useToast()
  const navigate = useNavigate()
  const [title, setTitle] = useState(note.title)
  const [body, setBody] = useState(note.body)
  const dirty = title !== note.title || body !== note.body

  const save = (silent = false) => {
    if (!dirty) return
    updateNote(note.id, { title, body })
    if (!silent) toast('Note saved', 'success')
  }

  useEffect(() => {
    if (!settings.autosave || !dirty) return
    const t = setTimeout(() => updateNote(note.id, { title, body }), 800)
    return () => clearTimeout(t)
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [title, body, settings.autosave])

  useHotkeys({ 'mod+s': () => save() })

  return (
    <div className="editor">
      <div className="editor-toolbar">
        <button className="link-button back-button" onClick={() => navigate('/')}>
          ← All notes
        </button>
        <span className="save-status">{dirty ? (settings.autosave ? 'Saving…' : 'Unsaved changes') : 'Saved'}</span>
        {!settings.autosave && (
          <button className="button" onClick={() => save()} disabled={!dirty}>
            Save
          </button>
        )}
        <button className="button button-danger" onClick={onDelete}>
          Delete
        </button>
      </div>
      <input
        className="editor-title"
        aria-label="Title"
        value={title}
        onChange={(e) => setTitle(e.target.value)}
        placeholder="Title"
      />
      <textarea
        className="editor-body"
        aria-label="Note body"
        value={body}
        onChange={(e) => setBody(e.target.value)}
        placeholder="Start writing…"
      />
    </div>
  )
}
