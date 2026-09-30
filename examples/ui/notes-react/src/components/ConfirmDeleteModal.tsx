import { Modal } from './Modal'

interface Props {
  noteTitle: string
  onConfirm: () => void
  onCancel: () => void
}

export function ConfirmDeleteModal({ noteTitle, onConfirm, onCancel }: Props) {
  return (
    <Modal
      title="Delete note?"
      onClose={onCancel}
      footer={
        <>
          <button className="button" onClick={onCancel}>
            Cancel
          </button>
          <button className="button button-danger" onClick={onConfirm}>
            Delete
          </button>
        </>
      }
    >
      <p>
        “{noteTitle || 'Untitled'}” will be permanently deleted. This can’t be undone.
      </p>
    </Modal>
  )
}
