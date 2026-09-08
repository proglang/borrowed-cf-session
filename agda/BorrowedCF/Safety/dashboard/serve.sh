#!/usr/bin/env bash
# Serve the dashboard locally: http://localhost:8765/dashboard.html
cd "$(dirname "$0")" && python3 gen.py && exec python3 -m http.server 8765 --bind 127.0.0.1
