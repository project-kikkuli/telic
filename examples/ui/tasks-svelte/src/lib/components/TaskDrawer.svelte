<script lang="ts">
  import { untrack } from 'svelte'
  import ConfirmDialog from './ConfirmDialog.svelte'
  import { deleteTask, projects, updateTask } from '../store.svelte'
  import type { Priority, Task } from '../types'

  interface Props {
    task: Task
    onclose: () => void
  }

  let { task, onclose }: Props = $props()

  let draft = $state(untrack(() => ({ ...task })))
  let confirm = $state<'discard' | 'delete' | null>(null)

  const dirty = $derived(
    draft.title !== task.title ||
      draft.notes !== task.notes ||
      draft.priority !== task.priority ||
      draft.due !== task.due ||
      draft.projectId !== task.projectId ||
      draft.done !== task.done,
  )

  function requestClose() {
    if (dirty) confirm = 'discard'
    else onclose()
  }

  function save(e: SubmitEvent) {
    e.preventDefault()
    if (!draft.title.trim()) return
    updateTask(task.id, { ...draft, title: draft.title.trim() })
    onclose()
  }

  function onKeydown(e: KeyboardEvent) {
    if (e.key === 'Escape' && !confirm) requestClose()
  }
</script>

<svelte:window onkeydown={onKeydown} />

<div class="scrim" onclick={requestClose} aria-hidden="true"></div>
<div class="drawer" role="dialog" aria-modal="true" aria-labelledby="drawer-title">
  <header>
    <h2 id="drawer-title">Task details</h2>
    <button class="icon-btn" aria-label="Close" onclick={requestClose}>×</button>
  </header>
  <form onsubmit={save}>
    <label class="field">
      <span>Title</span>
      <input bind:value={draft.title} required />
    </label>
    <label class="checkbox">
      <input type="checkbox" bind:checked={draft.done} />
      Completed
    </label>
    <label class="field">
      <span>Project</span>
      <select bind:value={draft.projectId}>
        {#each projects.value as p (p.id)}
          <option value={p.id}>{p.name}</option>
        {/each}
      </select>
    </label>
    <div class="two-col">
      <label class="field">
        <span>Priority</span>
        <select bind:value={draft.priority}>
          {#each ['low', 'medium', 'high'] as Priority[] as p}
            <option value={p}>{p[0].toUpperCase() + p.slice(1)}</option>
          {/each}
        </select>
      </label>
      <label class="field">
        <span>Due date</span>
        <input
          type="date"
          value={draft.due ?? ''}
          onchange={(e) => (draft.due = e.currentTarget.value || null)}
        />
      </label>
    </div>
    <label class="field">
      <span>Notes</span>
      <textarea rows="6" bind:value={draft.notes} placeholder="Add details…"></textarea>
    </label>
    <footer>
      <button type="button" class="btn btn-danger" onclick={() => (confirm = 'delete')}>Delete</button>
      <span class="spacer"></span>
      {#if dirty}<span class="unsaved">Unsaved changes</span>{/if}
      <button type="button" class="btn" onclick={requestClose}>Cancel</button>
      <button type="submit" class="btn btn-primary" disabled={!dirty}>Save</button>
    </footer>
  </form>
</div>

{#if confirm === 'discard'}
  <ConfirmDialog
    title="Discard changes?"
    message="You have unsaved edits to this task. If you leave now, they'll be lost."
    confirmLabel="Discard"
    cancelLabel="Keep editing"
    danger
    oncancel={() => (confirm = null)}
    onconfirm={() => {
      confirm = null
      onclose()
    }}
  />
{:else if confirm === 'delete'}
  <ConfirmDialog
    title="Delete task?"
    message={`"${task.title}" will be permanently deleted.`}
    confirmLabel="Delete"
    danger
    oncancel={() => (confirm = null)}
    onconfirm={() => {
      deleteTask(task.id)
      confirm = null
      onclose()
    }}
  />
{/if}

<style>
  .scrim {
    position: fixed;
    inset: 0;
    background: rgba(0, 0, 0, 0.3);
    z-index: 40;
  }
  .drawer {
    position: fixed;
    top: 0;
    right: 0;
    bottom: 0;
    width: min(440px, 100%);
    background: var(--bg);
    border-left: 1px solid var(--border);
    z-index: 41;
    display: flex;
    flex-direction: column;
    box-shadow: -8px 0 30px rgba(0, 0, 0, 0.15);
    animation: slide 0.18s ease-out;
  }
  @keyframes slide {
    from {
      transform: translateX(100%);
    }
  }
  header {
    display: flex;
    align-items: center;
    justify-content: space-between;
    padding: 1rem 1.25rem;
    border-bottom: 1px solid var(--border);
  }
  h2 {
    margin: 0;
    font-size: 1.1rem;
  }
  form {
    flex: 1;
    overflow-y: auto;
    padding: 1.25rem;
    display: flex;
    flex-direction: column;
  }
  .two-col {
    display: grid;
    grid-template-columns: 1fr 1fr;
    gap: 0.75rem;
  }
  .checkbox {
    display: flex;
    gap: 0.5rem;
    align-items: center;
    margin-bottom: 1rem;
  }
  footer {
    margin-top: auto;
    display: flex;
    align-items: center;
    gap: 0.5rem;
    padding-top: 1rem;
    flex-wrap: wrap;
  }
  .spacer {
    flex: 1;
  }
  .unsaved {
    font-size: 0.8rem;
    color: var(--warning);
  }
</style>
