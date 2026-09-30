#!/bin/sh
# Starts the API on PORT + 1 and the web app on PORT.
PORT=${1:-5173}
API=$((PORT + 1))
python3 ../server/app.py "$API" &
SPLITTER_API="http://127.0.0.1:$API" npx vite --port "$PORT" --strictPort --host 127.0.0.1
