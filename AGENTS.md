# Project Agent Configuration

## Build Server

- **Primary Build**: `root@hsiao` - Primary build server with Rocq installed
- **Fallback Build**: `ubuntu-64@orb` - ARM64 Ubuntu build server for Rust compilation
- Prefer remote builds over local builds for Rust and Rocq/Coq compilation

## Commands

### Rocq/Coq Builds (on hsiao)

For linking layer and formal proofs:
```bash
rsync -av --exclude=target --exclude=.git . root@hsiao:~/ubt-rs/
ssh root@hsiao "eval \"\$(opam env)\" && cd ~/ubt-rs/formal && make linking"
```

RocqOfRust path on hsiao: `~/pse/paradigm/rocq-of-rust/RocqOfRust`

### Rust Builds (local or orb)

Use the remote build script for Rust operations:
```bash
./scripts/remote-build.sh sync       # Sync local files to remote
./scripts/remote-build.sh build      # cargo build
./scripts/remote-build.sh test       # cargo test
./scripts/remote-build.sh bench      # cargo bench
```

Or configure custom host/path:
```bash
REMOTE_HOST=user@server REMOTE_PATH=~/mypath ./scripts/remote-build.sh build
```

## Project Structure

- `src/` - Rust implementation of Unified Binary Tree
- `formal/` - Rocq/Coq formal verification
  - `formal/simulations/` - Simulation layer proofs
  - `formal/linking/` - Rust-to-Rocq linking layer
  - `formal/proofs/` - Core proofs and QuickChick tests
  - `formal/specs/` - EIP-7864 specification
