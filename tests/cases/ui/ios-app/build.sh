#!/bin/sh
# A SwiftUI app without an Xcode project: swiftc for the simulator, then an ad-hoc signed bundle.
set -e
cd "$(dirname "$0")"
rm -rf build/Fixture.app
mkdir -p build/Fixture.app
xcrun --sdk iphonesimulator swiftc -parse-as-library -target "$(uname -m)-apple-ios18.0-simulator" -Onone App.swift -o build/Fixture.app/Fixture
cp Info.plist build/Fixture.app/Info.plist
codesign --force --sign - build/Fixture.app
