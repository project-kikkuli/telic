import { Modal } from './Modal'

const shortcuts: [string, string][] = [
  ['N', 'New note'],
  ['/', 'Search notes'],
  ['Ctrl/⌘ + S', 'Save note'],
  ['Ctrl/⌘ + ,', 'Open settings'],
  ['?', 'Show this help'],
  ['Esc', 'Close dialog'],
]

export function ShortcutsDialog({ onClose }: { onClose: () => void }) {
  return (
    <Modal title="Keyboard shortcuts" onClose={onClose}>
      <table className="shortcuts">
        <tbody>
          {shortcuts.map(([keys, action]) => (
            <tr key={keys}>
              <td>
                <kbd>{keys}</kbd>
              </td>
              <td>{action}</td>
            </tr>
          ))}
        </tbody>
      </table>
    </Modal>
  )
}
