<script lang="ts">
  import { untrack } from 'svelte'
  import { projects, updateTask } from '../store.svelte'
  import { notify } from '../notify'
  import type { Task } from '../types'

  interface Props {
    queue: Task[]
    onexit: () => void
  }

  let { queue, onexit }: Props = $props()

  let ids = $state(untrack(() => queue.map((t) => t.id)))
  let index = $state(0)
  let seconds = $state(25 * 60)
  let running = $state(false)
  let root: HTMLDivElement

  const current = $derived(queue.find((t) => t.id === ids[index]))
  const project = $derived(projects.value.find((p) => p.id === current?.projectId))
  const mm = $derived(String(Math.floor(seconds / 60)).padStart(2, '0'))
  const ss = $derived(String(seconds % 60).padStart(2, '0'))

  $effect(() => {
    root.requestFullscreen?.().catch(() => {})
    const onFs = () => {
      if (!document.fullscreenElement) onexit()
    }
    document.addEventListener('fullscreenchange', onFs)
    return () => {
      document.removeEventListener('fullscreenchange', onFs)
      if (document.fullscreenElement) document.exitFullscreen().catch(() => {})
    }
  })

  $effect(() => {
    if (!running) return
    const t = setInterval(() => {
      if (seconds <= 1) {
        running = false
        seconds = 0
        notify('Focus session complete', current?.title)
        clearInterval(t)
      } else {
        seconds -= 1
      }
    }, 1000)
    return () => clearInterval(t)
  })

  function complete() {
    if (!current) return
    updateTask(current.id, { done: true })
    ids = ids.filter((id) => id !== current!.id)
    if (index >= ids.length) index = 0
  }

  function skip() {
    index = ids.length ? (index + 1) % ids.length : 0
  }
</script>

<svelte:window onkeydown={(e) => e.key === 'Escape' && onexit()} />

<div class="focus" bind:this={root} role="dialog" aria-modal="true" aria-label="Focus mode">
  <button class="exit btn" onclick={onexit}>Exit focus</button>
  {#if current}
    <p class="meta">
      {#if project}<span class="dot" style="background: {project.color}"></span>{project.name} ·{/if}
      Task {index + 1} of {ids.length}
    </p>
    <h1>{current.title}</h1>
    {#if current.notes}<p class="notes">{current.notes}</p>{/if}
    <div class="timer" aria-live="polite">{mm}:{ss}</div>
    <div class="controls">
      <button class="btn" onclick={() => (running = !running)}>{running ? 'Pause' : 'Start timer'}</button>
      <button class="btn" onclick={() => ((seconds = 25 * 60), (running = false))}>Reset</button>
      <button class="btn" onclick={skip} disabled={ids.length < 2}>Skip</button>
      <button class="btn btn-primary" onclick={complete}>Mark complete</button>
    </div>
  {:else}
    <h1>All clear 🎉</h1>
    <p class="notes">No active tasks left in this view.</p>
    <button class="btn btn-primary" onclick={onexit}>Back to tasks</button>
  {/if}
</div>

<style>
  .focus {
    position: fixed;
    inset: 0;
    z-index: 60;
    background: var(--focus-bg);
    color: var(--text);
    display: flex;
    flex-direction: column;
    align-items: center;
    justify-content: center;
    text-align: center;
    padding: 2rem;
  }
  .exit {
    position: absolute;
    top: 1.25rem;
    right: 1.25rem;
  }
  .meta {
    color: var(--muted);
    display: flex;
    align-items: center;
    gap: 0.4rem;
  }
  .dot {
    width: 10px;
    height: 10px;
    border-radius: 50%;
    display: inline-block;
  }
  h1 {
    font-size: clamp(1.75rem, 5vw, 3rem);
    margin: 0.5rem 0;
    max-width: 800px;
  }
  .notes {
    color: var(--muted);
    max-width: 560px;
  }
  .timer {
    font-size: clamp(3rem, 12vw, 6rem);
    font-variant-numeric: tabular-nums;
    font-weight: 300;
    margin: 1.5rem 0;
  }
  .controls {
    display: flex;
    gap: 0.5rem;
    flex-wrap: wrap;
    justify-content: center;
  }
</style>
