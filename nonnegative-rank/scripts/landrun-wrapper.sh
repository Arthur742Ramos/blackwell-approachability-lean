#!/usr/bin/env bash
set -euo pipefail
exec "${PALOMAR_LANDRUN_BIN:?PALOMAR_LANDRUN_BIN is required}" "$@"
