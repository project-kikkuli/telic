import type { WeekStart } from './types'

export function todayIso() {
  return new Date().toISOString().slice(0, 10)
}

export function weekRange(weekStart: WeekStart) {
  const now = new Date()
  const day = now.getDay()
  const startOffset = weekStart === 'monday' ? (day + 6) % 7 : day
  const start = new Date(now)
  start.setDate(now.getDate() - startOffset)
  const end = new Date(start)
  end.setDate(start.getDate() + 6)
  return [start.toISOString().slice(0, 10), end.toISOString().slice(0, 10)] as const
}

export function formatDue(due: string) {
  const d = new Date(due + 'T00:00:00')
  return d.toLocaleDateString(undefined, { month: 'short', day: 'numeric' })
}
