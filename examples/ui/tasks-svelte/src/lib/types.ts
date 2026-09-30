export type Priority = 'low' | 'medium' | 'high'

export interface Project {
  id: string
  name: string
  color: string
}

export interface Task {
  id: string
  projectId: string
  title: string
  notes: string
  done: boolean
  priority: Priority
  due: string | null
  createdAt: number
}

export type WeekStart = 'sunday' | 'monday'

export interface Settings {
  notifications: boolean
  defaultProjectId: string
  weekStart: WeekStart
}

export type StatusFilter = 'all' | 'active' | 'completed'
export type DueFilter = 'any' | 'overdue' | 'today' | 'week'
