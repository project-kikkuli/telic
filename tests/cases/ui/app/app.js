//@ aim ESCAPE: WHILE a dialog or menu is open, the app shall let the user return to the home screen.
//@   by: escape
//@ [ESCAPE] ui escape: always reachable home from overlay

//@ aim SETTINGS: The app shall keep the user's settings across visits.
//@   by: dark-mode-shown, dark-mode
//@ [SETTINGS] ui dark-mode-shown: reachable checkbox "Dark mode" is enabled
//@ [SETTINGS] ui dark-mode: persists checkbox "Dark mode"

//@ aim NAV: The app shall keep its menu button visible.
//@   by: menu-visible
//@ [NAV] ui menu-visible: unobscured button "Menu" while not overlay

const bugs = new Set(window.BUGS || []);
const main = document.getElementById("main");
const notes = [];

function applyDark() {
  document.body.classList.toggle("dark", document.getElementById("dark").checked);
}

const dark = document.getElementById("dark");
dark.checked = !bugs.has("forget") && localStorage.getItem("dark") === "1";
applyDark();
dark.addEventListener("change", () => {
  localStorage.setItem("dark", dark.checked ? "1" : "0");
  applyDark();
});

const settings = document.getElementById("settings");
document.getElementById("settings-button").addEventListener("click", () => settings.showModal());
document.getElementById("settings-close").addEventListener("click", () => settings.close());

let menu = null;
const menuButton = document.getElementById("menu-button");
function closeMenu() {
  if (menu) menu.remove();
  menu = null;
  menuButton.setAttribute("aria-expanded", "false");
}
menuButton.addEventListener("click", () => {
  if (menu) return closeMenu();
  menu = document.createElement("div");
  menu.setAttribute("role", "menu");
  menu.setAttribute("aria-label", "Pages");
  for (const [label, hash] of [["Home", "#/"], ["About", "#/about"]]) {
    const item = document.createElement("button");
    item.setAttribute("role", "menuitem");
    item.textContent = label;
    item.addEventListener("click", () => { location.hash = hash; closeMenu(); });
    menu.append(item);
  }
  document.body.append(menu);
  menuButton.setAttribute("aria-expanded", "true");
});
document.addEventListener("keydown", (e) => {
  if (e.key === "Escape" && menu) closeMenu();
});

document.getElementById("help-button").addEventListener("click", () => {
  const box = document.createElement("div");
  box.className = "modal";
  box.innerHTML = '<div role="dialog" aria-modal="true" aria-label="Help"><p>Write notes.</p></div>';
  if (!bugs.has("trap")) {
    const ok = document.createElement("button");
    ok.textContent = "Got it";
    ok.addEventListener("click", () => box.remove());
    box.firstChild.append(ok);
  }
  document.body.append(box);
});

if (bugs.has("banner") && innerWidth < 600) {
  const b = document.createElement("div");
  b.className = "banner";
  b.textContent = "We use cookies";
  document.body.append(b);
}

function render() {
  main.innerHTML = "";
  if (location.hash === "#/about") {
    main.innerHTML = '<h1>About</h1><p>Jot keeps notes.</p><a href="#/">Back home</a>';
    return;
  }
  const h = document.createElement("h1");
  h.textContent = "Notes";
  const add = document.createElement("button");
  add.textContent = "Add note";
  add.addEventListener("click", () => { notes.push(`Note ${notes.length + 1}`); render(); });
  const list = document.createElement("ul");
  list.setAttribute("aria-label", "Notes");
  notes.forEach((n, i) => {
    const li = document.createElement("li");
    const del = document.createElement("button");
    del.textContent = `Delete ${n}`;
    del.addEventListener("click", () => { notes.splice(i, 1); render(); });
    li.append(n + " ", del);
    list.append(li);
  });
  main.append(h, add, list);
}
window.addEventListener("hashchange", render);
render();
