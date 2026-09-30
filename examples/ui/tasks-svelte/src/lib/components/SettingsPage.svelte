<script lang="ts">
  import { consent, projects, resetSettings, settings } from '../store.svelte'
  import { requestNotificationPermission } from '../notify'
  import type { WeekStart } from '../types'

  let permissionDenied = $state(false)
  let saved = $state(false)
  let savedTimer: ReturnType<typeof setTimeout>

  function flashSaved() {
    saved = true
    clearTimeout(savedTimer)
    savedTimer = setTimeout(() => (saved = false), 1500)
  }

  function update(patch: Partial<typeof settings.value>) {
    settings.value = { ...settings.value, ...patch }
    flashSaved()
  }

  async function toggleNotifications(e: Event) {
    const enabled = (e.currentTarget as HTMLInputElement).checked
    if (enabled) {
      const ok = await requestNotificationPermission()
      permissionDenied = !ok
      update({ notifications: ok })
    } else {
      permissionDenied = false
      update({ notifications: false })
    }
  }
</script>

<section class="settings">
  <header>
    <h1>Settings</h1>
    <span class="saved" aria-live="polite">{saved ? 'Saved ✓' : ''}</span>
  </header>

  <div class="card">
    <h2>Notifications</h2>
    <label class="switch">
      <input type="checkbox" checked={settings.value.notifications} onchange={toggleNotifications} />
      <span>Desktop notifications when tasks are completed or a focus session ends</span>
    </label>
    {#if permissionDenied}
      <p class="warning" role="alert">Notifications are blocked by your browser. Enable them in site settings to turn this on.</p>
    {/if}
  </div>

  <div class="card">
    <h2>Defaults</h2>
    <label class="field">
      <span>Default project for new tasks</span>
      <select value={settings.value.defaultProjectId} onchange={(e) => update({ defaultProjectId: e.currentTarget.value })}>
        {#each projects.value as p (p.id)}
          <option value={p.id}>{p.name}</option>
        {/each}
      </select>
    </label>
    <fieldset>
      <legend>Week starts on</legend>
      {#each ['sunday', 'monday'] as WeekStart[] as day}
        <label class="radio">
          <input
            type="radio"
            name="week-start"
            value={day}
            checked={settings.value.weekStart === day}
            onchange={() => update({ weekStart: day })}
          />
          {day[0].toUpperCase() + day.slice(1)}
        </label>
      {/each}
    </fieldset>
  </div>

  <div class="card">
    <h2>Privacy</h2>
    <p class="muted">
      Cookie preference: <strong>{consent.value ?? 'not set'}</strong>
    </p>
    <button class="btn" onclick={() => (consent.value = null)}>Change cookie preferences</button>
  </div>

  <button class="link-btn" onclick={() => (resetSettings(), flashSaved())}>Reset to defaults</button>
</section>

<style>
  .settings {
    max-width: 640px;
    margin: 0 auto;
    padding: 1.5rem;
  }
  header {
    display: flex;
    align-items: baseline;
    justify-content: space-between;
  }
  h1 {
    font-size: 1.6rem;
    margin: 0 0 1.25rem;
  }
  .saved {
    color: var(--success);
    font-size: 0.875rem;
  }
  .card {
    border: 1px solid var(--border);
    border-radius: 10px;
    padding: 1.1rem 1.25rem;
    margin-bottom: 1rem;
    background: var(--surface);
  }
  h2 {
    font-size: 1rem;
    margin: 0 0 0.75rem;
  }
  .switch {
    display: flex;
    gap: 0.6rem;
    align-items: flex-start;
  }
  fieldset {
    border: none;
    padding: 0;
    margin: 0;
  }
  legend {
    font-size: 0.85rem;
    color: var(--muted);
    margin-bottom: 0.4rem;
  }
  .radio {
    margin-right: 1.25rem;
  }
  .warning {
    color: var(--danger);
    font-size: 0.875rem;
    margin: 0.75rem 0 0;
  }
  .muted {
    color: var(--muted);
    margin-top: 0;
  }
</style>
