<script lang="ts">
  interface Props {
    title: string
    message: string
    confirmLabel?: string
    cancelLabel?: string
    danger?: boolean
    onconfirm: () => void
    oncancel: () => void
  }

  let { title, message, confirmLabel = 'Confirm', cancelLabel = 'Cancel', danger = false, onconfirm, oncancel }: Props = $props()

  let dialog: HTMLDialogElement

  $effect(() => {
    dialog.showModal()
    return () => dialog.close()
  })
</script>

<dialog
  bind:this={dialog}
  class="confirm"
  aria-labelledby="confirm-title"
  oncancel={(e) => {
    e.preventDefault()
    oncancel()
  }}
>
  <h2 id="confirm-title">{title}</h2>
  <p>{message}</p>
  <div class="actions">
    <button type="button" class="btn" onclick={oncancel}>{cancelLabel}</button>
    <button type="button" class="btn" class:btn-danger={danger} class:btn-primary={!danger} onclick={onconfirm}>
      {confirmLabel}
    </button>
  </div>
</dialog>

<style>
  .confirm {
    border: none;
    border-radius: 10px;
    padding: 1.25rem 1.5rem;
    max-width: 380px;
    width: calc(100% - 2rem);
    background: var(--bg);
    color: var(--text);
    box-shadow: 0 20px 50px rgba(0, 0, 0, 0.3);
  }
  .confirm::backdrop {
    background: rgba(0, 0, 0, 0.45);
  }
  h2 {
    margin: 0 0 0.5rem;
    font-size: 1.1rem;
  }
  p {
    margin: 0 0 1.25rem;
    color: var(--muted);
  }
  .actions {
    display: flex;
    justify-content: flex-end;
    gap: 0.5rem;
  }
</style>
