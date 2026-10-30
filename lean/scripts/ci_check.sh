#!/usr/bin/env bash
# ci_check.sh - the check GitHub runs for this folder: the final gate of check.sh (the paper is final, 0 open claims).
# Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
exec bash scripts/check.sh --final
