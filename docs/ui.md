# Checking a web app's UI

The grammar and statuses are in [contracts](contracts.md#ui-lemmas). This is
the loop.

1. **Install the driver** (once): `pip install 'telic[ui]'` and
   `playwright install chromium`.
2. **Say how to run the app.** Put a `telic.toml` next to its
   `package.json`:

   ```toml
   [ui]
   command = "npx vite --port {port} --strictPort"
   viewports = ["390x844", "1280x800"]
   ```

3. **Write the requirement and its lemmas** in any source file of the app
   (or declare the aim in `aims/ESCAPE.md`):

   ```ts
   //@ aim ESCAPE: WHILE a dialog or menu is open, the app shall let the
   //@   user return to the home screen.
   //@   by: escape
   //@ [ESCAPE] ui escape: always reachable home from overlay
   ```

4. **Run `telic check`** (or `telic aims`). The first run learns the model
   at each viewport; later runs reuse the verdicts until a file the app is
   built from changes.

5. **Read the verdict.** A refutation comes with the actions that lead to it,
   already replayed in the app:

   ```
   ✗ escape  always reachable home from overlay  app.js:3
             refuted on the learned model · at 1280x800: stuck at screen / with
             dialog "Help" open: none of its 5 actions leads to home; 4 blocked
             (covered by div.modal "Write notes.")
              1. click button "Help"
             replayed ✓ reached screen / with dialog "Help" open
   ```

   Fix the app (or the lemma) and run again. `open` means a budget stopped
   exploration or a trace did not replay: raise `max_states`/`max_depth`, or
   `ignore` the action that leads somewhere unbounded. `vacuous` means no
   reachable state made the lemma relevant: the element never rendered, or
   the overlay never opened, which is usually a wrong name in the lemma or an
   element without an accessible role.

6. **Keep it.** `telic ledger` records ui lemmas with everything else, and
   `telic ci` fails when one gets worse.

The learned model is in `.telic/ui-model-<viewport>.json` next to the app:
every state (route, overlays, controls), how to reach it, what was blocked
and why, and every transition.
