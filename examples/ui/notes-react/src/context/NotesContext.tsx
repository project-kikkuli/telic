import { createContext, useContext, type ReactNode } from 'react'
import { useLocalStorage } from '../hooks/useLocalStorage'
import type { Note } from '../types'

const seed: Note[] = [
  {
    id: 'welcome',
    title: 'Welcome to Notes',
    body: 'This is your first note. Edit it, or create a new one with the + button.\n\nPress ? to see keyboard shortcuts.',
    updatedAt: Date.now(),
  },
  {
    id: 'groceries',
    title: 'Groceries',
    body: '- Oat milk\n- Coffee beans\n- Lemons\n- Sourdough',
    updatedAt: Date.now() - 1000 * 60 * 60 * 5,
  },
]

interface NotesContextValue {
  notes: Note[]
  createNote: () => Note
  updateNote: (id: string, patch: Partial<Pick<Note, 'title' | 'body'>>) => void
  deleteNote: (id: string) => void
}

const NotesContext = createContext<NotesContextValue | null>(null)

export function NotesProvider({ children }: { children: ReactNode }) {
  const [notes, setNotes] = useLocalStorage<Note[]>('notes.items', seed)

  const createNote = () => {
    const note: Note = { id: crypto.randomUUID(), title: 'Untitled', body: '', updatedAt: Date.now() }
    setNotes((ns) => [note, ...ns])
    return note
  }

  const updateNote = (id: string, patch: Partial<Pick<Note, 'title' | 'body'>>) => {
    setNotes((ns) => ns.map((n) => (n.id === id ? { ...n, ...patch, updatedAt: Date.now() } : n)))
  }

  const deleteNote = (id: string) => setNotes((ns) => ns.filter((n) => n.id !== id))

  const sorted = [...notes].sort((a, b) => b.updatedAt - a.updatedAt)

  return (
    <NotesContext.Provider value={{ notes: sorted, createNote, updateNote, deleteNote }}>
      {children}
    </NotesContext.Provider>
  )
}

export function useNotes() {
  const ctx = useContext(NotesContext)
  if (!ctx) throw new Error('useNotes must be used inside NotesProvider')
  return ctx
}
