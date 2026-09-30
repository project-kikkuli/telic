type Route = { name: 'project'; projectId: string } | { name: 'all' } | { name: 'settings' } | { name: 'notfound' }

function parse(hash: string): Route {
  const path = hash.replace(/^#/, '') || '/'
  if (path === '/' || path === '/all') return { name: 'all' }
  if (path === '/settings') return { name: 'settings' }
  const m = path.match(/^\/projects\/([^/]+)$/)
  if (m) return { name: 'project', projectId: decodeURIComponent(m[1]) }
  return { name: 'notfound' }
}

let current = $state<Route>(parse(location.hash))

window.addEventListener('hashchange', () => {
  current = parse(location.hash)
})

export const router = {
  get route() {
    return current
  },
}

export function navigate(path: string) {
  location.hash = path
}
