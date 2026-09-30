export const CURRENCIES = ['USD', 'EUR', 'GBP', 'INR']

const KEY = 'splitter.currency'

export function loadCurrency(): string {
  return localStorage.getItem(KEY) ?? 'USD'
}

export function saveCurrency(code: string): void {
  localStorage.setItem(KEY, code)
}

export function formatMoney(cents: number, currency: string): string {
  return new Intl.NumberFormat(undefined, { style: 'currency', currency }).format(cents / 100)
}
