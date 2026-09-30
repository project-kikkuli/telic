<!--@ aim TASKS-ESCAPE: WHILE a dialog, drawer or focus session is open, the app shall let the user get back to the task list. -->
<!--@   by: escape, sidebar-closes -->
<!--@ [TASKS-ESCAPE] ui escape: always reachable screen "/" and not overlay from overlay -->
<!--@ [TASKS-ESCAPE] ui sidebar-closes: always reachable button "Open sidebar" is collapsed from button "Open sidebar" is expanded -->

<!--@ aim TASKS-SETTINGS: WHEN the user changes a setting, the app shall keep it the next time it is opened. -->
<!--@   by: default-project, week-start -->
<!--@ [TASKS-SETTINGS] ui default-project: persists combobox "Default project for new tasks" -->
<!--@ [TASKS-SETTINGS] ui week-start: persists radio "Sunday" -->

<!--@ aim TASKS-CONTROLS: The app shall never cover its navigation or a dialog's close button. -->
<!--@   by: sidebar-button-visible, settings-link-visible, close-visible -->
<!--@ [TASKS-CONTROLS] ui sidebar-button-visible: unobscured button "Open sidebar" while not overlay and not button "Open sidebar" is expanded -->
<!--@ [TASKS-CONTROLS] ui settings-link-visible: unobscured link "⚙ Settings" while not overlay and not button "Open sidebar" is collapsed -->
<!--@ [TASKS-CONTROLS] ui close-visible: unobscured button "Close" -->

<!--@ aim TASKS-DRAWER: The task drawer shall always show its Close button and its Save button, and keeping on editing shall return to it. -->
<!--@   by: drawer-close, save-visible, keep-editing -->
<!--@ [TASKS-DRAWER] ui drawer-close: never overlay "Task details" and not button "Close" -->
<!--@ [TASKS-DRAWER] ui save-visible: unobscured button "Save" -->
<!--@ [TASKS-DRAWER] ui keep-editing: always reachable overlay "Task details" and not overlay "Discard changes?" from overlay "Discard changes?" -->

<script lang="ts">
  import Sidebar from './lib/components/Sidebar.svelte'
  import TaskList from './lib/components/TaskList.svelte'
  import TaskDrawer from './lib/components/TaskDrawer.svelte'
  import SettingsPage from './lib/components/SettingsPage.svelte'
  import CookieBanner from './lib/components/CookieBanner.svelte'
  import FocusMode from './lib/components/FocusMode.svelte'
  import { router } from './lib/router.svelte'
  import { tasks } from './lib/store.svelte'
  import type { Task } from './lib/types'

  let sidebarOpen = $state(false)
  let openTaskId = $state<string | null>(null)
  let focusQueue = $state<Task[] | null>(null)

  const openTask = $derived(tasks.value.find((t) => t.id === openTaskId))
</script>

<div class="layout">
  <Sidebar open={sidebarOpen} onclose={() => (sidebarOpen = false)} />
  {#if sidebarOpen}
    <div class="sidebar-scrim" onclick={() => (sidebarOpen = false)} aria-hidden="true"></div>
  {/if}

  <main>
    <div class="topbar">
      <button class="icon-btn" aria-label="Open sidebar" aria-expanded={sidebarOpen} onclick={() => (sidebarOpen = true)}>☰</button>
      <span class="brand">✔ Tasks</span>
    </div>

    {#if router.route.name === 'all'}
      <TaskList projectId={null} onopen={(t) => (openTaskId = t.id)} onfocus={(q) => (focusQueue = q)} />
    {:else if router.route.name === 'project'}
      {#key router.route.projectId}
        <TaskList projectId={router.route.projectId} onopen={(t) => (openTaskId = t.id)} onfocus={(q) => (focusQueue = q)} />
      {/key}
    {:else if router.route.name === 'settings'}
      <SettingsPage />
    {:else}
      <section class="not-found">
        <h1>Page not found</h1>
        <a href="#/">Back to all tasks</a>
      </section>
    {/if}
  </main>
</div>

{#if openTask}
  {#key openTask.id}
    <TaskDrawer task={openTask} onclose={() => (openTaskId = null)} />
  {/key}
{/if}

{#if focusQueue}
  <FocusMode queue={focusQueue} onexit={() => (focusQueue = null)} />
{/if}

<CookieBanner />

<style>
  .layout {
    display: flex;
    min-height: 100vh;
  }
  main {
    flex: 1;
    min-width: 0;
  }
  .topbar {
    display: none;
    align-items: center;
    gap: 0.75rem;
    padding: 0.75rem 1rem;
    border-bottom: 1px solid var(--border);
  }
  .brand {
    font-weight: 700;
  }
  .sidebar-scrim {
    display: none;
  }
  .not-found {
    padding: 3rem 1.5rem;
    text-align: center;
  }
  @media (max-width: 768px) {
    .topbar {
      display: flex;
    }
    .sidebar-scrim {
      display: block;
      position: fixed;
      inset: 0;
      background: rgba(0, 0, 0, 0.3);
      z-index: 29;
    }
  }
</style>
