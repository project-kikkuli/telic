export interface Note {
  id: string
  title: string
  body: string
  updatedAt: number
}

export type Theme = 'light' | 'dark' | 'system'
export type FontSize = 'small' | 'medium' | 'large'

export interface Settings {
  theme: Theme
  fontSize: FontSize
  autosave: boolean
  displayName: string
}

export interface User {
  email: string
}
