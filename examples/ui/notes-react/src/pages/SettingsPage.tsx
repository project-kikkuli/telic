import { useState, type FormEvent } from 'react'
import { useSettings } from '../context/SettingsContext'
import { useToast } from '../context/ToastContext'
import type { FontSize, Theme } from '../types'

export default function SettingsPage() {
  const { settings, update, reset } = useSettings()
  const toast = useToast()
  const [name, setName] = useState(settings.displayName)

  const saveName = (e: FormEvent) => {
    e.preventDefault()
    update({ displayName: name.trim() })
    toast('Display name updated', 'success')
  }

  return (
    <div className="page settings-page">
      <h1>Settings</h1>

      <section className="card">
        <h2>Appearance</h2>
        <fieldset>
          <legend>Theme</legend>
          {(['light', 'dark', 'system'] as Theme[]).map((t) => (
            <label key={t} className="radio">
              <input
                type="radio"
                name="theme"
                value={t}
                checked={settings.theme === t}
                onChange={() => update({ theme: t })}
              />
              {t[0].toUpperCase() + t.slice(1)}
            </label>
          ))}
        </fieldset>
        <label className="field">
          <span>Font size</span>
          <select value={settings.fontSize} onChange={(e) => update({ fontSize: e.target.value as FontSize })}>
            <option value="small">Small</option>
            <option value="medium">Medium</option>
            <option value="large">Large</option>
          </select>
        </label>
      </section>

      <section className="card">
        <h2>Editor</h2>
        <label className="toggle">
          <input
            type="checkbox"
            checked={settings.autosave}
            onChange={(e) => {
              update({ autosave: e.target.checked })
              toast(e.target.checked ? 'Autosave on' : 'Autosave off')
            }}
          />
          <span>Autosave notes while typing</span>
        </label>
      </section>

      <section className="card">
        <h2>Profile</h2>
        <form onSubmit={saveName} className="inline-form">
          <label className="field">
            <span>Display name</span>
            <input value={name} onChange={(e) => setName(e.target.value)} placeholder="Your name" maxLength={40} />
          </label>
          <button className="button button-primary" type="submit" disabled={name.trim() === settings.displayName}>
            Save
          </button>
        </form>
      </section>

      <button
        className="link-button"
        onClick={() => {
          reset()
          setName('')
          toast('Settings reset to defaults')
        }}
      >
        Reset to defaults
      </button>
    </div>
  )
}
