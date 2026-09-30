export function persisted<T>(key: string, initial: T) {
  let value = $state<T>(load())

  function load(): T {
    try {
      const raw = localStorage.getItem(key)
      return raw ? (JSON.parse(raw) as T) : initial
    } catch {
      return initial
    }
  }

  $effect.root(() => {
    $effect(() => {
      localStorage.setItem(key, JSON.stringify(value))
    })
  })

  return {
    get value() {
      return value
    },
    set value(v: T) {
      value = v
    },
  }
}
