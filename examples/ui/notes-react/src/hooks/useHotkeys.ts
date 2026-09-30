import { useEffect, useRef } from 'react'

type Handler = (e: KeyboardEvent) => void

function isTyping(target: EventTarget | null) {
  const el = target as HTMLElement | null
  if (!el) return false
  return el.tagName === 'INPUT' || el.tagName === 'TEXTAREA' || el.tagName === 'SELECT' || el.isContentEditable
}

export function useHotkeys(bindings: Record<string, Handler>) {
  const ref = useRef(bindings)
  ref.current = bindings

  useEffect(() => {
    const onKey = (e: KeyboardEvent) => {
      const combo = [(e.metaKey || e.ctrlKey) && 'mod', e.shiftKey && 'shift', e.key.toLowerCase()]
        .filter(Boolean)
        .join('+')
      const handler = ref.current[combo]
      if (!handler) return
      if (!combo.startsWith('mod') && isTyping(e.target)) return
      e.preventDefault()
      handler(e)
    }
    window.addEventListener('keydown', onKey)
    return () => window.removeEventListener('keydown', onKey)
  }, [])
}
