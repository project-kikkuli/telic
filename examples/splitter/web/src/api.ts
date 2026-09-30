import type { Expense } from './expense'
import type { int } from './split'

export type Transfer = { debtor: int; creditor: int; amount: int }

async function post<T>(path: string, body: unknown): Promise<T> {
  const res = await fetch(path, { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify(body) })
  const data = await res.json()
  if (!res.ok) throw new Error(data.error)
  return data as T
}

export const api = {
  split: async (amount: int, parts: int) => (await post<{ shares: int[] }>('/api/split', { amount, parts })).shares,
  balances: async (members: int, expenses: Expense[]) =>
    (await post<{ balances: int[] }>('/api/balances', { members, expenses: expenses.map((e) => ({ payer: e.payer, shares: e.shares, status: e.status })) })).balances,
  settle: async (balances: int[]) => (await post<{ transfers: Transfer[] }>('/api/settle', { balances })).transfers,
}
