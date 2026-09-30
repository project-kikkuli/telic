//@ [BACK-HOME] ui back-home: always reachable home
//@ [SETTLE-VISIBLE] ui settle-visible: unobscured button "Settle up" while not overlay
//@ [CURRENCY-PERSISTS] ui currency-persists: persists combobox "Currency"

import { Expense } from './expense'
import { parseCents, splitEqual } from './split'
import type { int } from './split'
import { formatMoney, loadCurrency, saveCurrency, CURRENCIES } from './settings'
import { api } from './api'

type Group = { id: string; name: string; members: string[]; expenses: Expense[] }

const STATE_KEY = 'splitter.groups'
const app = document.querySelector<HTMLDivElement>('#app')!

function seed(): Group[] {
  const dinner = new Expense('e1', 'Dinner', 0, 9000, [3000, 3000, 3000], 'posted')
  const taxi = new Expense('e2', 'Taxi', 1, 2400, [800, 800, 800], 'draft')
  return [{ id: 'trip', name: 'Lisbon trip', members: ['Ana', 'Ben', 'Chi'], expenses: [dinner, taxi] }]
}

function load(): Group[] {
  const raw = localStorage.getItem(STATE_KEY)
  if (raw === null) return seed()
  const data = JSON.parse(raw) as { id: string; name: string; members: string[]; expenses: Expense[] }[]
  return data.map((g) => ({
    ...g,
    expenses: g.expenses.map((e) => new Expense(e.id, e.label, e.payer, e.amount, e.shares, e.status)),
  }))
}

let groups = load()

function save(): void {
  localStorage.setItem(STATE_KEY, JSON.stringify(groups))
}

function el<K extends keyof HTMLElementTagNameMap>(tag: K, props: Partial<HTMLElementTagNameMap[K]> = {}, ...children: (Node | string)[]): HTMLElementTagNameMap[K] {
  const node = Object.assign(document.createElement(tag), props)
  node.append(...children)
  return node
}

function link(href: string, text: string): HTMLAnchorElement {
  const a = el('a', { href }, text)
  a.addEventListener('click', (ev) => {
    ev.preventDefault()
    go(href)
  })
  return a
}

function go(path: string): void {
  history.pushState(null, '', path)
  render()
}

function header(): HTMLElement {
  return el('header', {}, el('nav', {}, link('/', 'All groups'), ' ', link('/settings', 'Settings')))
}

function toast(text: string): void {
  const t = el('div', { className: 'toast', role: 'status' }, text)
  document.body.append(t)
  setTimeout(() => t.remove(), 4000)
}

function renderGroups(): HTMLElement {
  const name = el('input', { type: 'text', name: 'group-name' })
  name.setAttribute('aria-label', 'Group name')
  const members = el('input', { type: 'text', name: 'members' })
  members.setAttribute('aria-label', 'Members, comma separated')
  const form = el('form', {}, name, members, el('button', { type: 'submit' }, 'Create group'))
  form.addEventListener('submit', (ev) => {
    ev.preventDefault()
    const people = members.value.split(',').map((m) => m.trim()).filter((m) => m !== '')
    if (name.value.trim() === '' || people.length === 0) return
    const g: Group = { id: `g${Date.now()}`, name: name.value.trim(), members: people, expenses: [] }
    groups.push(g)
    save()
    go(`/groups/${g.id}`)
  })
  const list = el('ul', {}, ...groups.map((g) => el('li', {}, link(`/groups/${g.id}`, g.name))))
  return el('main', {}, el('h1', {}, 'Groups'), list, el('h2', {}, 'New group'), form)
}

function expenseDialog(g: Group, onDone: () => void): HTMLDialogElement {
  const dlg = el('dialog', { className: 'sheet' })
  dlg.setAttribute('aria-label', 'Add expense')
  const label = el('input', { type: 'text' })
  label.setAttribute('aria-label', 'Description')
  const amount = el('input', { type: 'text', inputMode: 'decimal' })
  amount.setAttribute('aria-label', 'Amount')
  const payer = el('select', {}, ...g.members.map((m, i) => el('option', { value: String(i) }, m)))
  payer.setAttribute('aria-label', 'Paid by')
  const preview = el('p', { className: 'preview' })
  const refresh = () => {
    const cents = parseCents(amount.value)
    preview.textContent = cents === undefined ? 'Enter an amount' : splitEqual(cents, g.members.length).map((s, i) => `${g.members[i]} ${formatMoney(s, loadCurrency())}`).join(' · ')
  }
  amount.addEventListener('input', refresh)
  refresh()
  const saveBtn = el('button', { type: 'button' }, 'Save draft')
  saveBtn.addEventListener('click', async () => {
    const cents = parseCents(amount.value)
    if (cents === undefined) return
    const shares: int[] = await api.split(cents, g.members.length)
    g.expenses.push(new Expense(`e${Date.now()}`, label.value.trim() || 'Expense', Number(payer.value), cents, shares, 'draft'))
    save()
    dlg.close()
    onDone()
  })
  const cancel = el('button', { type: 'button' }, 'Cancel')
  cancel.addEventListener('click', () => dlg.close())
  dlg.append(el('h2', {}, 'Add expense'), label, amount, payer, preview, el('div', { className: 'row' }, saveBtn, cancel))
  dlg.addEventListener('close', () => dlg.remove())
  return dlg
}

function settleDialog(g: Group, onDone: () => void): HTMLDialogElement {
  const dlg = el('dialog', { className: 'sheet' })
  dlg.setAttribute('aria-label', 'Settle up')
  const list = el('ul', {}, el('li', {}, 'Working out who pays whom…'))
  const confirm = el('button', { type: 'button', disabled: true }, 'Mark all settled')
  const close = el('button', { type: 'button' }, 'Close')
  close.addEventListener('click', () => dlg.close())
  confirm.addEventListener('click', () => {
    for (const e of g.expenses) if (e.status === 'posted') e.settle()
    save()
    dlg.close()
    toast('Group settled')
    onDone()
  })
  dlg.append(el('h2', {}, 'Settle up'), list, el('div', { className: 'row' }, confirm, close))
  dlg.addEventListener('close', () => dlg.remove())
  void (async () => {
    const owed = await api.balances(g.members.length, g.expenses)
    const transfers = await api.settle(owed)
    const cur = loadCurrency()
    list.replaceChildren(
      ...(transfers.length === 0
        ? [el('li', {}, 'Everyone is square.')]
        : transfers.map((t) => el('li', {}, `${g.members[t.debtor]} pays ${g.members[t.creditor]} ${formatMoney(t.amount, cur)}`))),
    )
    confirm.disabled = !g.expenses.some((e) => e.status === 'posted')
  })()
  return dlg
}

function renderGroup(g: Group): HTMLElement {
  const cur = loadCurrency()
  const balances = el('ul', { className: 'balances' }, ...g.members.map((m) => el('li', {}, m)))
  void api.balances(g.members.length, g.expenses).then((owed) => {
    balances.replaceChildren(...g.members.map((m, i) => el('li', {}, `${m}: ${owed[i] >= 0 ? 'is owed' : 'owes'} ${formatMoney(Math.abs(owed[i]), cur)}`)))
  })
  const rows = g.expenses.map((e) => {
    const item = el('li', {}, `${e.label} · ${formatMoney(e.amount, cur)} · paid by ${g.members[e.payer]} · ${e.status}`)
    if (e.status === 'draft') {
      const post = el('button', { type: 'button' }, `Post ${e.label}`)
      post.addEventListener('click', () => {
        e.post()
        save()
        toast(`${e.label} posted`)
        render()
      })
      item.append(' ', post)
    }
    return item
  })
  const add = el('button', { type: 'button' }, 'Add expense')
  add.addEventListener('click', () => {
    const dlg = expenseDialog(g, render)
    document.body.append(dlg)
    dlg.showModal()
  })
  const settle = el('button', { type: 'button', className: 'primary' }, 'Settle up')
  settle.addEventListener('click', () => {
    const dlg = settleDialog(g, render)
    document.body.append(dlg)
    dlg.showModal()
  })
  return el(
    'main',
    {},
    el('h1', {}, g.name),
    el('h2', {}, 'Balances'),
    balances,
    el('h2', {}, 'Expenses'),
    el('ul', {}, ...rows),
    add,
    el('footer', { className: 'bar' }, settle),
  )
}

function renderSettings(): HTMLElement {
  const select = el('select', {}, ...CURRENCIES.map((c) => el('option', { value: c, selected: c === loadCurrency() }, c)))
  select.setAttribute('aria-label', 'Currency')
  select.addEventListener('change', () => saveCurrency(select.value))
  return el('main', {}, el('h1', {}, 'Settings'), el('label', {}, 'Currency ', select))
}

function render(): void {
  const path = location.pathname
  const m = /^\/groups\/([^/]+)$/.exec(path)
  let page: HTMLElement
  if (m !== null) {
    const g = groups.find((x) => x.id === m[1])
    page = g === undefined ? el('main', {}, el('h1', {}, 'No such group')) : renderGroup(g)
  } else if (path === '/settings') {
    page = renderSettings()
  } else {
    page = renderGroups()
  }
  app.replaceChildren(header(), page)
}

window.addEventListener('popstate', render)
render()
