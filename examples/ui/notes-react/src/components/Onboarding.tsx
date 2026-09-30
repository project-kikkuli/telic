import { useState } from 'react'

const steps = [
  { title: 'Welcome to Notes', body: 'A simple place to jot things down. Everything is stored in your browser.' },
  { title: 'Create and edit', body: 'Use the + New button or press N to start a note. Changes save automatically.' },
  { title: 'Make it yours', body: 'Pick a theme, font size and display name in Settings. Press ? any time for shortcuts.' },
]

export function Onboarding({ onFinish }: { onFinish: () => void }) {
  const [step, setStep] = useState(0)
  const current = steps[step]
  const last = step === steps.length - 1

  return (
    <div className="onboarding-overlay">
      <div className="onboarding-card" role="dialog" aria-modal="true" aria-labelledby="onboarding-title">
        <p className="onboarding-progress">
          Step {step + 1} of {steps.length}
        </p>
        <h2 id="onboarding-title">{current.title}</h2>
        <p>{current.body}</p>
        <div className="onboarding-actions">
          <button className="link-button" onClick={onFinish}>
            Skip
          </button>
          <div className="spacer" />
          {step > 0 && (
            <button className="button" onClick={() => setStep(step - 1)}>
              Back
            </button>
          )}
          <button className="button button-primary" onClick={() => (last ? onFinish() : setStep(step + 1))}>
            {last ? 'Get started' : 'Next'}
          </button>
        </div>
      </div>
    </div>
  )
}
