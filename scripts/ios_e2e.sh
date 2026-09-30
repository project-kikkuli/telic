#!/bin/sh
# The iOS adapter end to end on a real simulator: installs what is missing
# (a runtime, AXe), then runs the fixture app's lemmas, known-good and known-bad.
set -e
cd "$(dirname "$0")/.."
xcrun simctl help >/dev/null 2>&1 || { echo "needs Xcode: install it, then 'sudo xcode-select -s /Applications/Xcode.app'"; exit 1; }
xcrun simctl list runtimes | grep -q "^iOS" || xcodebuild -downloadPlatform iOS
command -v axe >/dev/null || brew install cameroncooke/axe/axe
sh tests/cases/ui/ios-app/build.sh
uv run --extra test pytest -q -rs tests/test_ui_ios.py "$@"
rm -rf tests/cases/ui/ios-app/build
