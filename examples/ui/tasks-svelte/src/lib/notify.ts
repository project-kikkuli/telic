import { settings } from './store.svelte'

export async function requestNotificationPermission() {
  if (!('Notification' in window)) return false
  if (Notification.permission === 'granted') return true
  const result = await Notification.requestPermission()
  return result === 'granted'
}

export function notify(title: string, body?: string) {
  if (!settings.value.notifications) return
  if (!('Notification' in window) || Notification.permission !== 'granted') return
  new Notification(title, { body })
}
