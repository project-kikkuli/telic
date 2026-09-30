import { defineConfig } from 'vite'

const api = process.env.SPLITTER_API ?? 'http://127.0.0.1:8787'

export default defineConfig({
  server: { proxy: { '/api': api } },
})
