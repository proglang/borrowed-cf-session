#!/usr/bin/env bash
# Surrogate-crash-proof wrapper around agda-check.sh: strips math-bold Unicode
# (which serializes as JSON surrogate pairs and crashes the agent transcript)
# to ASCII and byte-bounds the output. ALWAYS use this instead of agda-check.sh.
./agda-check.sh "$@" 2>&1 | iconv -f utf-8 -t ascii//TRANSLIT 2>/dev/null | head -c 6000
echo
