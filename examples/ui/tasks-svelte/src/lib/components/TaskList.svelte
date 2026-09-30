<script lang="ts">
  import { addTask, projects, settings, tasks, updateTask } from '../store.svelte'
  import { formatDue, todayIso, weekRange } from '../dates'
  import { notify } from '../notify'
  import type { DueFilter, Priority, StatusFilter, Task } from '../types'

  interface Props {
    projectId: string | null
    onopen: (task: Task) => void
    onfocus: (queue: Task[]) => void
  }

  let { projectId, onopen, onfocus }: Props = $props()

  let status = $state<StatusFilter>('active')
  let priority = $state<Priority | 'any'>('any')
  let due = $state<DueFilter>('any')
  let search = $state('')
  let newTitle = $state('')

  const project = $derived(projects.value.find((p) => p.id === projectId))
  const title = $derived(projectId ? (project?.name ?? 'Unknown project') : 'All tasks')

  const visible = $derived.by(() => {
    const today = todayIso()
    const [weekStart, weekEnd] = weekRange(settings.value.weekStart)
    const q = search.trim().toLowerCase()
    const rank = { high: 0, medium: 1, low: 2 }
    return tasks.value
      .filter((t) => !projectId || t.projectId === projectId)
      .filter((t) => (status === 'all' ? true : status === 'active' ? !t.done : t.done))
      .filter((t) => priority === 'any' || t.priority === priority)
      .filter((t) => {
        if (due === 'any') return true
        if (!t.due) return false
        if (due === 'overdue') return t.due < today && !t.done
        if (due === 'today') return t.due === today
        return t.due >= weekStart && t.due <= weekEnd
      })
      .filter((t) => !q || t.title.toLowerCase().includes(q) || t.notes.toLowerCase().includes(q))
      .sort((a, b) => Number(a.done) - Number(b.done) || rank[a.priority] - rank[b.priority] || b.createdAt - a.createdAt)
  })

  const hasFilters = $derived(status !== 'active' || priority !== 'any' || due !== 'any' || search !== '')

  function clearFilters() {
    status = 'active'
    priority = 'any'
    due = 'any'
    search = ''
  }

  function submit(e: SubmitEvent) {
    e.preventDefault()
    const t = newTitle.trim()
    if (!t) return
    addTask(projectId ?? settings.value.defaultProjectId, t)
    newTitle = ''
  }

  function toggle(task: Task) {
    updateTask(task.id, { done: !task.done })
    if (!task.done) notify('Task completed', task.title)
  }

  function projectFor(id: string) {
    return projects.value.find((p) => p.id === id)
  }
</script>

<section class="task-view">
  <header class="view-header">
    <h1>
      {#if project}<span class="dot" style="background: {project.color}"></span>{/if}
      {title}
    </h1>
    <button
      class="btn"
      onclick={() => onfocus(visible.filter((t) => !t.done))}
      disabled={!visible.some((t) => !t.done)}
    >
      ⛶ Focus mode
    </button>
  </header>

  <form class="new-task" onsubmit={submit}>
    <input bind:value={newTitle} placeholder="Add a task and press Enter" aria-label="New task title" />
    <button class="btn btn-primary" type="submit" disabled={!newTitle.trim()}>Add</button>
  </form>

  <div class="filters" role="group" aria-label="Filters">
    <div class="segmented" role="radiogroup" aria-label="Status">
      {#each ['active', 'completed', 'all'] as StatusFilter[] as s}
        <button role="radio" aria-checked={status === s} class:selected={status === s} onclick={() => (status = s)}>
          {s[0].toUpperCase() + s.slice(1)}
        </button>
      {/each}
    </div>
    <select bind:value={priority} aria-label="Priority">
      <option value="any">Any priority</option>
      <option value="high">High</option>
      <option value="medium">Medium</option>
      <option value="low">Low</option>
    </select>
    <select bind:value={due} aria-label="Due date">
      <option value="any">Any due date</option>
      <option value="overdue">Overdue</option>
      <option value="today">Due today</option>
      <option value="week">Due this week</option>
    </select>
    <input type="search" bind:value={search} placeholder="Search" aria-label="Search tasks" />
    {#if hasFilters}
      <button class="link-btn" onclick={clearFilters}>Clear filters</button>
    {/if}
  </div>

  {#if visible.length === 0}
    <div class="empty">
      <p>{hasFilters ? 'No tasks match these filters.' : 'Nothing here yet. Add your first task above.'}</p>
    </div>
  {:else}
    <ul class="tasks">
      {#each visible as task (task.id)}
        {@const p = projectFor(task.projectId)}
        <li class:done={task.done}>
          <input
            type="checkbox"
            checked={task.done}
            onchange={() => toggle(task)}
            aria-label={`Mark "${task.title}" ${task.done ? 'incomplete' : 'complete'}`}
          />
          <button class="task-title" onclick={() => onopen(task)}>
            <span>{task.title}</span>
            <span class="task-meta">
              {#if !projectId && p}<span class="tag"><span class="dot" style="background: {p.color}"></span>{p.name}</span>{/if}
              {#if task.due}
                <span class="due" class:overdue={!task.done && task.due < todayIso()}>{formatDue(task.due)}</span>
              {/if}
            </span>
          </button>
          <span class="priority priority-{task.priority}">{task.priority}</span>
        </li>
      {/each}
    </ul>
  {/if}
</section>

<style>
  .task-view {
    max-width: 860px;
    margin: 0 auto;
    padding: 1.5rem;
  }
  .view-header {
    display: flex;
    align-items: center;
    justify-content: space-between;
    gap: 1rem;
  }
  h1 {
    display: flex;
    align-items: center;
    gap: 0.6rem;
    font-size: 1.6rem;
    margin: 0;
  }
  .dot {
    width: 10px;
    height: 10px;
    border-radius: 50%;
    display: inline-block;
  }
  .new-task {
    display: flex;
    gap: 0.5rem;
    margin: 1.25rem 0 1rem;
  }
  .new-task input {
    flex: 1;
  }
  .filters {
    display: flex;
    flex-wrap: wrap;
    gap: 0.5rem;
    align-items: center;
    margin-bottom: 1rem;
  }
  .filters input[type='search'] {
    flex: 1;
    min-width: 140px;
  }
  .segmented {
    display: inline-flex;
    border: 1px solid var(--border);
    border-radius: 6px;
    overflow: hidden;
  }
  .segmented button {
    font: inherit;
    font-size: 0.875rem;
    border: none;
    background: var(--bg);
    color: var(--text);
    padding: 0.4rem 0.75rem;
    cursor: pointer;
  }
  .segmented button + button {
    border-left: 1px solid var(--border);
  }
  .segmented button.selected {
    background: var(--primary);
    color: white;
  }
  .tasks {
    list-style: none;
    margin: 0;
    padding: 0;
    border: 1px solid var(--border);
    border-radius: 8px;
  }
  .tasks li {
    display: flex;
    align-items: center;
    gap: 0.75rem;
    padding: 0.6rem 0.9rem;
    border-bottom: 1px solid var(--border);
  }
  .tasks li:last-child {
    border-bottom: none;
  }
  .tasks li.done .task-title > span:first-child {
    text-decoration: line-through;
    color: var(--muted);
  }
  .task-title {
    flex: 1;
    min-width: 0;
    text-align: left;
    background: none;
    border: none;
    font: inherit;
    color: inherit;
    cursor: pointer;
    display: flex;
    flex-direction: column;
    gap: 0.15rem;
    padding: 0.2rem 0;
  }
  .task-meta {
    display: flex;
    gap: 0.6rem;
    font-size: 0.8rem;
    color: var(--muted);
  }
  .tag {
    display: inline-flex;
    align-items: center;
    gap: 0.3rem;
  }
  .due.overdue {
    color: var(--danger);
  }
  .priority {
    font-size: 0.72rem;
    text-transform: uppercase;
    letter-spacing: 0.04em;
    padding: 0.15rem 0.45rem;
    border-radius: 4px;
    background: var(--hover);
    color: var(--muted);
  }
  .priority-high {
    background: #fee2e2;
    color: #b91c1c;
  }
  .priority-medium {
    background: #fef3c7;
    color: #92400e;
  }
  .empty {
    text-align: center;
    color: var(--muted);
    padding: 3rem 1rem;
    border: 1px dashed var(--border);
    border-radius: 8px;
  }
</style>
