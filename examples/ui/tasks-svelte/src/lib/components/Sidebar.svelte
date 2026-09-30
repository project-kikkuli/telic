<script lang="ts">
  import { addProject, projects, tasks } from '../store.svelte'
  import { navigate, router } from '../router.svelte'

  interface Props {
    open: boolean
    onclose: () => void
  }

  let { open, onclose }: Props = $props()

  let adding = $state(false)
  let newName = $state('')

  const counts = $derived.by(() => {
    const map: Record<string, number> = {}
    for (const t of tasks.value) {
      if (!t.done) map[t.projectId] = (map[t.projectId] ?? 0) + 1
    }
    return map
  })

  const activeTotal = $derived(tasks.value.filter((t) => !t.done).length)

  function submit(e: SubmitEvent) {
    e.preventDefault()
    const name = newName.trim()
    if (!name) return
    const p = addProject(name)
    newName = ''
    adding = false
    navigate(`/projects/${p.id}`)
  }

  function isActive(id: string) {
    return router.route.name === 'project' && router.route.projectId === id
  }
</script>

<aside class="sidebar" class:open aria-label="Projects">
  <div class="sidebar-header">
    <span class="brand">✔ Tasks</span>
    <button class="icon-btn close" aria-label="Close sidebar" onclick={onclose}>×</button>
  </div>
  <nav>
    <a href="#/" class:active={router.route.name === 'all'} onclick={onclose}>
      <span class="dot" style="background: var(--muted)"></span>
      All tasks
      <span class="count">{activeTotal}</span>
    </a>
    <h3>Projects</h3>
    <ul>
      {#each projects.value as p (p.id)}
        <li>
          <a href="#/projects/{p.id}" class:active={isActive(p.id)} onclick={onclose}>
            <span class="dot" style="background: {p.color}"></span>
            {p.name}
            <span class="count">{counts[p.id] ?? 0}</span>
          </a>
        </li>
      {/each}
    </ul>
    {#if adding}
      <form onsubmit={submit} class="new-project">
        <!-- svelte-ignore a11y_autofocus -->
        <input bind:value={newName} placeholder="Project name" aria-label="Project name" autofocus />
        <div class="row">
          <button class="btn btn-primary" type="submit">Add</button>
          <button class="btn" type="button" onclick={() => (adding = false)}>Cancel</button>
        </div>
      </form>
    {:else}
      <button class="link-btn add" onclick={() => (adding = true)}>+ New project</button>
    {/if}
  </nav>
  <div class="sidebar-footer">
    <a href="#/settings" class:active={router.route.name === 'settings'} onclick={onclose}>⚙ Settings</a>
  </div>
</aside>

<style>
  .sidebar {
    width: 250px;
    flex-shrink: 0;
    background: var(--surface);
    border-right: 1px solid var(--border);
    display: flex;
    flex-direction: column;
    padding: 1rem 0.75rem;
  }
  .sidebar-header {
    display: flex;
    align-items: center;
    justify-content: space-between;
    padding: 0 0.5rem 1rem;
  }
  .brand {
    font-weight: 700;
  }
  .close {
    display: none;
  }
  nav {
    flex: 1;
    overflow-y: auto;
  }
  h3 {
    font-size: 0.75rem;
    text-transform: uppercase;
    letter-spacing: 0.05em;
    color: var(--muted);
    margin: 1.25rem 0.5rem 0.5rem;
  }
  ul {
    list-style: none;
    margin: 0;
    padding: 0;
  }
  a {
    display: flex;
    align-items: center;
    gap: 0.6rem;
    padding: 0.45rem 0.5rem;
    border-radius: 6px;
    color: var(--text);
    text-decoration: none;
  }
  a:hover {
    background: var(--hover);
  }
  a.active {
    background: var(--hover);
    font-weight: 600;
  }
  .dot {
    width: 10px;
    height: 10px;
    border-radius: 50%;
  }
  .count {
    margin-left: auto;
    font-size: 0.8rem;
    color: var(--muted);
  }
  .add {
    margin: 0.5rem;
  }
  .new-project {
    padding: 0.5rem;
    display: flex;
    flex-direction: column;
    gap: 0.5rem;
  }
  .row {
    display: flex;
    gap: 0.5rem;
  }
  .sidebar-footer {
    border-top: 1px solid var(--border);
    padding-top: 0.75rem;
  }

  @media (max-width: 768px) {
    .sidebar {
      position: fixed;
      inset: 0 auto 0 0;
      z-index: 30;
      transform: translateX(-100%);
      transition: transform 0.2s ease;
      box-shadow: 4px 0 20px rgba(0, 0, 0, 0.15);
    }
    .sidebar.open {
      transform: translateX(0);
    }
    .close {
      display: block;
    }
  }
</style>
