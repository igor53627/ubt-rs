# Project Agent Configuration

## Build Server

- **Remote Build**: `ubuntu-64@orb` - ARM64 Ubuntu build server for heavy compilation
- **Access**: Requires SSH key configured for the `orb` host (internal build infrastructure)
- Prefer remote builds over local builds for Rust and Rocq/Coq compilation

## Commands

Use the remote build script for all operations:

```bash
./scripts/remote-build.sh sync       # Sync local files to remote
./scripts/remote-build.sh build      # cargo build
./scripts/remote-build.sh test       # cargo test
./scripts/remote-build.sh bench      # cargo bench
./scripts/remote-build.sh proofs     # make proofs-core (Rocq)
./scripts/remote-build.sh quickchick # make quickchick-ci (property tests)
```

Or configure custom host/path:
```bash
REMOTE_HOST=user@server REMOTE_PATH=~/mypath ./scripts/remote-build.sh build
```

## Project Structure

- `src/` - Rust implementation of Unified Binary Trie
- `formal/` - Rocq/Coq formal verification
  - `formal/simulations/` - Simulation layer proofs
  - `formal/linking/` - Rust-to-Rocq linking layer
  - `formal/proofs/` - Core proofs and QuickChick tests
  - `formal/specs/` - EIP-7864 specification
