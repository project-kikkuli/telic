<script lang="ts">
  import { consent } from '../store.svelte'

  let showDetails = $state(false)
</script>

{#if consent.value === null}
  <div class="banner" role="region" aria-label="Cookie consent">
    <div class="text">
      <strong>We use cookies</strong>
      <p>
        We use local storage and optional analytics cookies to remember your preferences and improve the app.
        {#if !showDetails}
          <button class="link-btn" onclick={() => (showDetails = true)}>Learn more</button>
        {/if}
      </p>
      {#if showDetails}
        <ul>
          <li><strong>Essential:</strong> saves your tasks, projects and settings in this browser.</li>
          <li><strong>Analytics:</strong> anonymous usage stats. Off unless you accept.</li>
        </ul>
      {/if}
    </div>
    <div class="actions">
      <button class="btn" onclick={() => (consent.value = 'rejected')}>Essential only</button>
      <button class="btn btn-primary" onclick={() => (consent.value = 'accepted')}>Accept all</button>
    </div>
  </div>
{/if}

<style>
  .banner {
    position: fixed;
    left: 1rem;
    right: 1rem;
    bottom: 1rem;
    max-width: 760px;
    margin: 0 auto;
    background: var(--bg);
    border: 1px solid var(--border);
    border-radius: 12px;
    box-shadow: 0 10px 40px rgba(0, 0, 0, 0.18);
    padding: 1rem 1.25rem;
    display: flex;
    gap: 1rem;
    align-items: center;
    z-index: 35;
  }
  .text {
    flex: 1;
  }
  p {
    margin: 0.25rem 0 0;
    color: var(--muted);
    font-size: 0.9rem;
  }
  ul {
    margin: 0.5rem 0 0;
    padding-left: 1.1rem;
    font-size: 0.85rem;
    color: var(--muted);
  }
  .actions {
    display: flex;
    gap: 0.5rem;
    flex-shrink: 0;
  }
  @media (max-width: 600px) {
    .banner {
      flex-direction: column;
      align-items: stretch;
    }
    .actions > * {
      flex: 1;
    }
  }
</style>
