#!/bin/bash
# Remote build script for ubt-rs
# Executes build commands on the remote ARM64 build server
set -e
set -o pipefail

REMOTE_HOST="${REMOTE_HOST:-ubuntu-64@orb}"
REMOTE_PATH="${REMOTE_PATH:-ubt-rs}"

case "$1" in
  build)
    ssh "$REMOTE_HOST" "cd ~/$REMOTE_PATH && cargo build"
    ;;
  test)
    ssh "$REMOTE_HOST" "cd ~/$REMOTE_PATH && cargo test"
    ;;
  bench)
    ssh "$REMOTE_HOST" "cd ~/$REMOTE_PATH && cargo bench"
    ;;
  proofs)
    ssh "$REMOTE_HOST" "cd ~/$REMOTE_PATH/formal && eval \"\$(opam env --switch=rocq-9)\" && make proofs-core"
    ;;
  quickchick)
    ssh "$REMOTE_HOST" "cd ~/$REMOTE_PATH/formal && eval \"\$(opam env --switch=rocq-9)\" && make quickchick-ci"
    ;;
  sync)
    SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
    SRC_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
    rsync -av --exclude=target --exclude=.git "$SRC_DIR/" "$REMOTE_HOST:~/$REMOTE_PATH/"
    ;;
  *)
    echo "Usage: $0 {build|test|bench|proofs|quickchick|sync}"
    echo ""
    echo "Commands:"
    echo "  build      - Run cargo build"
    echo "  test       - Run cargo test"
    echo "  bench      - Run cargo bench"
    echo "  proofs     - Build formal proofs (Rocq/Coq)"
    echo "  quickchick - Run QuickChick property tests"
    echo "  sync       - Sync local files to remote"
    echo ""
    echo "Environment variables:"
    echo "  REMOTE_HOST - SSH host (default: ubuntu-64@orb)"
    echo "  REMOTE_PATH - Remote path relative to ~ (default: ubt-rs)"
    exit 1
    ;;
esac
