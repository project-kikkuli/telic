import { persisted } from './persisted.svelte'
import type { Project, Settings, Task } from './types'

const today = new Date()
const iso = (offset: number) => {
  const d = new Date(today)
  d.setDate(d.getDate() + offset)
  return d.toISOString().slice(0, 10)
}

const seedProjects: Project[] = [
  { id: 'inbox', name: 'Inbox', color: '#64748b' },
  { id: 'work', name: 'Work', color: '#2563eb' },
  { id: 'home', name: 'Home', color: '#16a34a' },
]

const seedTasks: Task[] = [
  { id: 't1', projectId: 'work', title: 'Write Q4 planning doc', notes: 'Outline goals and staffing.', done: false, priority: 'high', due: iso(1), createdAt: Date.now() - 50000 },
  { id: 't2', projectId: 'work', title: 'Review pull requests', notes: '', done: false, priority: 'medium', due: iso(0), createdAt: Date.now() - 40000 },
  { id: 't3', projectId: 'work', title: 'Update onboarding checklist', notes: '', done: true, priority: 'low', due: iso(-3), createdAt: Date.now() - 30000 },
  { id: 't4', projectId: 'home', title: 'Book dentist appointment', notes: 'Dr. Patel, mornings only.', done: false, priority: 'medium', due: iso(-1), createdAt: Date.now() - 20000 },
  { id: 't5', projectId: 'home', title: 'Fix leaky tap', notes: '', done: false, priority: 'low', due: null, createdAt: Date.now() - 10000 },
  { id: 't6', projectId: 'inbox', title: 'Call Sam back', notes: '', done: false, priority: 'high', due: iso(3), createdAt: Date.now() },
]

const defaultSettings: Settings = {
  notifications: false,
  defaultProjectId: 'inbox',
  weekStart: 'monday',
}

export const projects = persisted<Project[]>('tasks.projects', seedProjects)
export const tasks = persisted<Task[]>('tasks.items', seedTasks)
export const settings = persisted<Settings>('tasks.settings', defaultSettings)
export const consent = persisted<'accepted' | 'rejected' | null>('tasks.consent', null)

export function addProject(name: string) {
  const palette = ['#9333ea', '#ea580c', '#0891b2', '#db2777', '#ca8a04']
  const project: Project = {
    id: crypto.randomUUID(),
    name,
    color: palette[projects.value.length % palette.length],
  }
  projects.value = [...projects.value, project]
  return project
}

export function addTask(projectId: string, title: string) {
  const task: Task = {
    id: crypto.randomUUID(),
    projectId,
    title,
    notes: '',
    done: false,
    priority: 'medium',
    due: null,
    createdAt: Date.now(),
  }
  tasks.value = [task, ...tasks.value]
  return task
}

export function updateTask(id: string, patch: Partial<Task>) {
  tasks.value = tasks.value.map((t) => (t.id === id ? { ...t, ...patch } : t))
}

export function deleteTask(id: string) {
  tasks.value = tasks.value.filter((t) => t.id !== id)
}

export function resetSettings() {
  settings.value = { ...defaultSettings }
}
