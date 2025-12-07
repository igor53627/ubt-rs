# EIP-7864 Unified Binary Tree Implementations

Status tracking for EIP-7864 (Unified Binary Tree) implementations across Ethereum clients and languages.

**EIP Status:** Draft (as of December 2025)

---

## Technical Resources

### Core Documentation
| Resource | Description |
|----------|-------------|
| [EIP-7864 Specification](https://eips.ethereum.org/EIPS/eip-7864) | Official EIP |
| [Ethereum Magicians Discussion](https://ethereum-magicians.org/t/eip-7864-ethereum-state-using-a-unified-binary-tree/22611) | Active discussion thread |
| [Binary Tree Research Notes](https://hackmd.io/@jsign/binary-tree-notes) | Sparse tree drawbacks, serialization tricks |
| [HackMD Draft EIP](https://hackmd.io/@jsign/binary-tree-draft-eip) | Early draft with implementation notes |

### Benchmarks & Performance
| Resource | Description |
|----------|-------------|
| [In-circuit Hash Benchmarks](https://hackmd.io/@han/bench-hash-in-snark) | Proving performance for different hash functions |
| [Recommended Hardware Specs](https://hackmd.io/@kevaundray/S1hUQuV4Jx) | Target proving hardware requirements |

### Related Research
| Resource | Description |
|----------|-------------|
| [Preimages File Generation](https://ethresear.ch/t/state-tree-preimages-file-generation/21651) | State conversion complexity |
| [Stateless Ethereum Book](https://stateless.fyi/trees/binary-tree.html) | Binary tree overview |

### Educational
| Resource | Description |
|----------|-------------|
| [Understanding EIP-7864](https://dev.to/zemse/understanding-eip-7864s-unified-binary-tree-36m4) | Step-by-step explanation by zemse |

---

## Existing Implementations

### Python (Reference Specification)

| Repository | Author | Status | License |
|------------|--------|--------|---------|
| [jsign/binary-tree-spec](https://github.com/jsign/binary-tree-spec) | Ignacio Hagopian (EIP author) | ✅ Complete | MIT |

**Files:**
- `tree.py` - BinaryTree class implementation
- `embedding.py` - Account encoding into tree
- `eth_types.py` - Ethereum type definitions
- `test_tree.py` - Tree tests
- `test_embedding.py` - Embedding tests

```bash
# Run tests
python -m unittest discover
```

---

### Go (go-ethereum / Geth)

| Repository | PR/Branch | Status | Version |
|------------|-----------|--------|---------|
| [ethereum/go-ethereum](https://github.com/ethereum/go-ethereum) | PR #32365 | ✅ Merged | v1.16.3+ |
| [gballet/go-ethereum](https://github.com/gballet/go-ethereum/tree/rebased-binary-trie-m5-full-path) | rebased-binary-trie-m5-full-path | 🔬 Experimental | - |

**Location in Geth:**
- `trie/bintrie/` - Binary tree implementation
- `trie/utils/` - Tree utilities

**Geth Release Notes (v1.16.3):**
> Implement EIP-7864 - binary trees #32365

---

### Rust (Community POC)

| Repository | Author | Status | Notes |
|------------|--------|--------|-------|
| [varun-doshi/eth-binary-tree](https://github.com/varun-doshi/eth-binary-tree) | varun-doshi | 🔨 In progress | Tree done, embedding pending |

**Note:** This is a minimal POC based on the Python spec. Not yet integrated into reth.

---

## Missing Implementations

### Rust (Reth / Alloy - Production)

| Repository | Status | Notes |
|------------|--------|-------|
| [paradigmxyz/reth](https://github.com/paradigmxyz/reth) | ❌ Not implemented | No official EIP-7864 support yet |
| [alloy-rs/eips](https://github.com/alloy-rs/eips) | ❌ Not implemented | EIP constants/helpers only |

**Opportunity:** Production-ready Rust implementation needed for reth client

---

### TypeScript (EthereumJS)

| Repository | Status | Notes |
|------------|--------|-------|
| [@ethereumjs/client](https://www.npmjs.com/package/@ethereumjs/client) | ❌ Not implemented | Currently supports MPT and Verkle |
| [@ethereumjs/trie](https://www.npmjs.com/package/@ethereumjs/trie) | ❌ Not implemented | MPT implementation only |

**Opportunity:** TypeScript implementation for browser/Node.js environments

---

### C# (Nethermind)

| Repository | Status | Notes |
|------------|--------|-------|
| [NethermindEth/nethermind](https://github.com/NethermindEth/nethermind) | ❌ Not implemented | No EIP-7864 branch found |

---

### Java (Besu)

| Repository | Status | Notes |
|------------|--------|-------|
| [hyperledger/besu](https://github.com/hyperledger/besu) | ❌ Not implemented | No EIP-7864 support yet |

---

### Nim (Nimbus)

| Repository | Status | Notes |
|------------|--------|-------|
| [status-im/nimbus-eth1](https://github.com/status-im/nimbus-eth1) | ❌ Not implemented | No EIP-7864 support yet |

---

## Implementation Priority

Based on client diversity and ecosystem needs:

| Priority | Language | Client | Rationale |
|----------|----------|--------|-----------|
| 🔴 High | Rust | Reth | Growing adoption, performance critical |
| 🔴 High | C# | Nethermind | Major mainnet client |
| 🟡 Medium | TypeScript | EthereumJS | Developer tooling, light clients |
| 🟡 Medium | Java | Besu | Enterprise adoption |
| 🟢 Lower | Nim | Nimbus | Smaller market share |

---

## Related EIPs
- [EIP-4762](https://eips.ethereum.org/EIPS/eip-4762) - Gas cost model / Access events
- [EIP-7612](https://eips.ethereum.org/EIPS/eip-7612) - Fork specification
- [EIP-7748](https://eips.ethereum.org/EIPS/eip-7748) - MPT data migration

**Note:** Transaction and receipt tries are NOT affected by EIP-7864.

---

## Key Design Decisions (from Eth Magicians Discussion)

### Why Non-Sparse Tree?
- Avoids complex extension node rules
- Reduces hashing for proving performance on commodity hardware
- If Poseidon2 is proven secure, sparse tree discussion may reopen

### Why BLAKE3 (for now)?
- Allows EL clients to experiment without friction
- Easy to switch to Poseidon2 later if security confirmed
- Only requires describing `32-byte → [Field]` encoding change

### Why Hash Account Addresses?
- Plain addresses are unsafe for tree keys
- At 21,000 gas cost, attackers can send ETH to any address
- This allows manipulation of tree insertions, creating long branches
- Hashing balances the tree

### Why Pack Header Fields?
- SNARK circuits need `32byte × 32byte → 32byte` primitive
- Packing nonce, balance, code_size, version into single 32-byte reduces overhead
- Minimizes bitwise operations (unfriendly to circuits)

---

## Known Limitations

### Cannot Iterate Storage Slots Per Account
- Single-layer tree loses storage scope association
- Breaks some client tooling and analysis capabilities
- Not required for protocol (block execution doesn't need iteration)

### Sync Protocol Needs Redesign
- Current SNAP sync relies on trie traversal semantics
- Two-layer structure defines storage scope for positioned account
- New design requires sync based on trie characteristics alone
- State traversal order will differ from flat state structure

### Preimages Complexity
- Key hashing is double-edged sword
- Entries lack associated preimages unless explicitly maintained
- Adds complexity to state conversion algorithm

### Scope Limitations
- Only affects L1 state tree
- L2s continue using their own tree designs
- No concurrency issues (single writer)

---

## Contributing

If you're implementing EIP-7864 in a new language or client:

1. Reference the [Python spec](https://github.com/jsign/binary-tree-spec) for correctness
2. Use test vectors from the reference implementation
3. Review [Binary Tree Research Notes](https://hackmd.io/@jsign/binary-tree-notes) for implementation tricks
4. Check [In-circuit Hash Benchmarks](https://hackmd.io/@han/bench-hash-in-snark) for performance targets
5. Join discussion at [Ethereum Magicians](https://ethereum-magicians.org/t/eip-7864-ethereum-state-using-a-unified-binary-tree/22611)
6. Submit PR to update this tracking document

---

*Last updated: December 2025*
