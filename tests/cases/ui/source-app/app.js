//@ aim ESCAPE: WHILE a dialog is open, the app shall let the user return to the home screen.
//@   by: escape
//@ [ESCAPE] ui escape: always reachable home from overlay

// Known-bad variants, chosen by window.BUGS: "counter" (Help traps once Next
// tip was clicked three times: nothing on screen changes), "shortcut" (a
// Shortcuts dialog that only the ? key opens, with no way out).
const bugs = new Set(window.BUGS || []);
let tip = 0;

document.getElementById("next").addEventListener("click", () => {
  tip = (tip + 1) % 4;
});

function dialog(label, closable) {
  const box = document.createElement("div");
  box.className = "modal";
  box.innerHTML = `<div role="dialog" aria-modal="true" aria-label="${label}"><p>${label}</p></div>`;
  if (closable) {
    const ok = document.createElement("button");
    ok.textContent = "Close";
    ok.addEventListener("click", () => box.remove());
    box.firstChild.append(ok);
  }
  document.body.append(box);
}

document.getElementById("help").addEventListener("click", () => dialog("Help", !(bugs.has("counter") && tip === 3)));

document.addEventListener("keydown", (e) => {
  if (e.shiftKey && e.key === "?" && !document.querySelector(".modal")) dialog("Shortcuts", !bugs.has("shortcut"));
});
