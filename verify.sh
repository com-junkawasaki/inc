#!/bin/bash

# Incidence Theory Verification Script
# This script verifies that all formal proofs are correct and examples run properly

set -e  # Exit on any error

echo "🧮 Incidence Theory - Verification Script"
echo "========================================"

# Check if we're in the right directory
if [ ! -f "incidence-theory/lakefile.lean" ]; then
    echo "❌ Error: Please run this script from the project root directory"
    exit 1
fi

echo "📁 Project structure check..."
if [ ! -d "incidence-theory" ]; then
    echo "❌ incidence-theory directory not found"
    exit 1
fi

echo "🔧 Lean toolchain check..."
if ! command -v lake &> /dev/null; then
    echo "❌ Lake (Lean package manager) not found. Please install Lean 4 first:"
    echo "   curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y"
    exit 1
fi

echo "🏗️  Building Lean formalization..."
cd incidence-theory
lake clean
if ! lake build; then
    echo "❌ Lean build failed"
    exit 1
fi

echo "▶️  Running examples..."
if ! lake exe incidence-theory; then
    echo "❌ Example execution failed"
    exit 1
fi

echo "📋 Verifying completion claim matrix..."
cd ..
bash scripts/verify-completion-claims.sh
bash scripts/verify-paper-theorem-index.sh
bash scripts/verify-mechanized-prior-art-audit.sh
bash scripts/verify-arxiv-manuscript.sh
bash scripts/verify-journal-package.sh
cd incidence-theory

echo "🧾 Auditing capstone axiom dependencies..."
audit_output="$(mktemp)"
trap 'rm -f "$audit_output"' EXIT
lake env lean CompletionAudit.lean >"$audit_output" 2>&1
if rg -n 'sorryAx|declaration uses .sorry.|unknown constant' "$audit_output"; then
    echo "❌ Completion capstone has an unproved or missing dependency"
    exit 1
fi
if ! awk '
  /depends on axioms:/ {
    line = $0
    sub(/^.*\[/, "", line)
    active = 1
  }
  active && $0 !~ /depends on axioms:/ { line = $0 }
  active {
    done = (line ~ /\]/)
    gsub(/[\[\],]/, " ", line)
    count = split(line, names, /[[:space:]]+/)
    for (i = 1; i <= count; i++) {
      name = names[i]
      if (name != "" && name != "propext" &&
          name != "Classical.choice" && name != "Quot.sound") {
        print "unexpected axiom dependency: " name > "/dev/stderr"
        bad = 1
      }
    }
    if (done) active = 0
  }
  END { exit bad }
' "$audit_output"; then
    echo "❌ Completion capstone exceeds the axiom allowlist"
    exit 1
fi
rm -f "$audit_output"
trap - EXIT

echo "🔎 Checking for unproved Lean declarations..."
if rg -n '^[[:space:]]*axiom[[:space:]]|^[[:space:]]*sorry([[:space:]]|$)|:=[[:space:]]*sorry([[:space:]]|$)|by[[:space:]]+sorry([[:space:]]|$)|exact[[:space:]]+sorry([[:space:]]|$)|sorryAx' \
    . -g '*.lean' -g '!**/.lake/**'; then
    echo "❌ Found an unproved Lean declaration"
    exit 1
fi

cd ..

echo "✅ All verifications passed!"
echo ""
echo "📊 Verification Summary:"
echo "   • Lean 4 formalization: ✅ Built successfully"
echo "   • Checked proofs: ✅ Verified"
echo "   • Examples: ✅ Executed successfully"
echo "   • Unproved declarations: ✅ None"
echo ""
echo "🎉 The checked Lean core is internally verified."
echo ""
echo "For more details, see:"
echo "   • README.md for theory overview"
echo "   • incidence-theory/README.md for formalization details"
echo "   • story.jsonnet for development roadmap"
