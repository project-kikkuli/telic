import { createContext, useContext, useEffect, type ReactNode } from 'react'
import { useLocalStorage } from '../hooks/useLocalStorage'
import { useMediaQuery } from '../hooks/useMediaQuery'
import type { Settings } from '../types'

const defaults: Settings = {
  theme: 'system',
  fontSize: 'medium',
  autosave: true,
  displayName: '',
}

interface SettingsContextValue {
  settings: Settings
  update: (patch: Partial<Settings>) => void
  reset: () => void
  resolvedTheme: 'light' | 'dark'
}

const SettingsContext = createContext<SettingsContextValue | null>(null)

export function SettingsProvider({ children }: { children: ReactNode }) {
  const [settings, setSettings] = useLocalStorage<Settings>('notes.settings', defaults)
  const prefersDark = useMediaQuery('(prefers-color-scheme: dark)')
  const resolvedTheme = settings.theme === 'system' ? (prefersDark ? 'dark' : 'light') : settings.theme

  useEffect(() => {
    document.documentElement.dataset.theme = resolvedTheme
  }, [resolvedTheme])

  useEffect(() => {
    document.documentElement.dataset.fontSize = settings.fontSize
  }, [settings.fontSize])

  const update = (patch: Partial<Settings>) => setSettings((s) => ({ ...s, ...patch }))
  const reset = () => setSettings(defaults)

  return (
    <SettingsContext.Provider value={{ settings, update, reset, resolvedTheme }}>
      {children}
    </SettingsContext.Provider>
  )
}

export function useSettings() {
  const ctx = useContext(SettingsContext)
  if (!ctx) throw new Error('useSettings must be used inside SettingsProvider')
  return ctx
}
