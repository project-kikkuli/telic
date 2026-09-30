//@ aim ESCAPE: WHILE a sheet or dialog is open, the app shall let the user return to the home screen.
//@   by: escape
//@ [ESCAPE] ui escape: always reachable home from overlay

//@ aim SETTINGS: The app shall keep the user's settings across launches.
//@   by: dark-mode-shown, dark-mode
//@ [SETTINGS] ui dark-mode-shown: reachable switch "Dark mode"
//@ [SETTINGS] ui dark-mode: persists switch "Dark mode"

//@ aim NAV: The app shall keep its menu button visible.
//@   by: menu-visible
//@ [NAV] ui menu-visible: unobscured button "Menu" while not overlay

import SwiftUI

// Known-bad variants, chosen at launch: -TelicBugs trap,forget,banner
let bugs = Set((UserDefaults.standard.string(forKey: "TelicBugs") ?? "").split(separator: ",").map(String.init))

@main
struct FixtureApp: App {
    var body: some Scene {
        WindowGroup { ContentView() }
    }
}

struct ContentView: View {
    @State private var help = false
    @State private var menu = false
    @State private var cookies = bugs.contains("banner")

    var body: some View {
        NavigationStack {
            List {
                NavigationLink("Settings") { SettingsView() }
                NavigationLink("About") { AboutView() }
                Button("Help") { help = true }
            }
            .navigationTitle("Home")
            .toolbar {
                ToolbarItem(placement: .topBarTrailing) {
                    Button("Menu") { menu = true }
                }
            }
            .confirmationDialog("Menu", isPresented: $menu, titleVisibility: .visible) {
                Button("Refresh") {}
            }
            .sheet(isPresented: $help) { HelpSheet() }
        }
        .overlay(alignment: .top) {
            if cookies {
                HStack {
                    Text("We use cookies")
                    Spacer()
                    Button("Accept") { cookies = false }
                }
                .padding()
                .frame(maxWidth: .infinity)
                .background(.yellow)
            }
        }
    }
}

struct SettingsView: View {
    @AppStorage("darkMode") private var saved = false
    @State private var unsaved = false

    var body: some View {
        Form {
            if bugs.contains("forget") {
                Toggle("Dark mode", isOn: $unsaved)
            } else {
                Toggle("Dark mode", isOn: $saved)
            }
        }
        .navigationTitle("Settings")
    }
}

struct AboutView: View {
    var body: some View {
        Text("A fixture for telic.")
            .navigationTitle("About")
    }
}

struct HelpSheet: View {
    @Environment(\.dismiss) private var dismiss

    var body: some View {
        NavigationStack {
            Text("Write notes.")
                .navigationTitle("Help")
                .toolbar {
                    if !bugs.contains("trap") {
                        ToolbarItem(placement: .cancellationAction) {
                            Button("Close") { dismiss() }
                        }
                    }
                }
        }
        .interactiveDismissDisabled(bugs.contains("trap"))
    }
}
