import { createContext, useContext, type ReactNode } from 'react'
import { useLocalStorage } from '../hooks/useLocalStorage'
import type { User } from '../types'

interface AuthContextValue {
  user: User | null
  signIn: (email: string, password: string) => Promise<void>
  signOut: () => void
}

const AuthContext = createContext<AuthContextValue | null>(null)

export function AuthProvider({ children }: { children: ReactNode }) {
  const [user, setUser] = useLocalStorage<User | null>('notes.user', null)

  const signIn = async (email: string, password: string) => {
    await new Promise((r) => setTimeout(r, 400))
    if (!email.includes('@')) throw new Error('Enter a valid email address.')
    if (password.length < 4) throw new Error('Password must be at least 4 characters.')
    setUser({ email })
  }

  const signOut = () => setUser(null)

  return <AuthContext.Provider value={{ user, signIn, signOut }}>{children}</AuthContext.Provider>
}

export function useAuth() {
  const ctx = useContext(AuthContext)
  if (!ctx) throw new Error('useAuth must be used inside AuthProvider')
  return ctx
}
