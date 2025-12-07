# UBT Implementation Guide for AI Agents

Supplementary implementation knowledge for EIP-7864 Unified Binary Tree, extracted from practical analysis.

## Core Concept

UBT is NOT a sparse merkle tree. It's a dynamically structured binary tree where:
- Keys are 32 bytes (256 bits)
- First 31 bytes = stem (determines which subtree)
- Last 1 byte = subindex (position within 256-leaf subtree)

## Key Insight: Stem vs MPT Path

In MPT, the `path` field excluded already-consumed nibbles. When refactoring the tree, path changes caused hash changes and edge cases.

In UBT, the `stem` is always the full 31-byte value regardless of tree depth. This means:
- Refactoring tree structure doesn't change stem values
- Hashes are stable during tree reorganization
- Simpler implementation logic

## Node Types

```rust
enum Node {
    Empty,                          // hash = 0x00...00
    Internal { left: Node, right: Node },
    Stem { stem: [u8; 31], leaves: [Option<[u8; 32]>; 256] },
    Leaf { value: [u8; 32] },       // only inside Stem subtree
}
```

## Hash Rules

```
hash(0x00 * 64) = 0x00 * 32    // special case for empty
hash(left || right) = H(left || right)
stem_hash = H(stem || 0x00 || subtree_root)
empty_hash = 0x00 * 32
```

## Tree Operations

### Insertion Algorithm

```
fn insert(root, key, value):
    stem = key[0:31]
    subindex = key[31]
    
    if root is Empty:
        return StemNode(stem, set_leaf(subindex, value))
    
    if root is StemNode:
        if root.stem == stem:
            root.leaves[subindex] = value
            return root
        else:
            // Split: create internal nodes until stems diverge
            return split_and_insert(root, stem, subindex, value)
    
    if root is Internal:
        bit = get_bit(stem, current_depth)
        if bit == 0:
            root.left = insert(root.left, key, value, depth+1)
        else:
            root.right = insert(root.right, key, value, depth+1)
        return root
```

### Split Logic

When inserting into a StemNode with different stem:
1. Find first differing bit between stems
2. Create minimal internal nodes up to that bit
3. Place both StemNodes as children

Example:
```
existing_stem = 0x00...00 (all zeros)
new_stem = 0x80...00 (first bit = 1)

Result: one InternalNode with:
  - left child: StemNode(0x00...00)
  - right child: StemNode(0x80...00)
```

## Address to Tree Key Conversion

```python
def address_to_stem(address: bytes20, tree_index: int) -> bytes31:
    address32 = b'\x00' * 12 + address  # pad to 32 bytes
    tree_idx_bytes = tree_index.to_bytes(32, 'little')
    return hash(address32 + tree_idx_bytes)[:31]

def get_tree_key(address: bytes20, tree_index: int, sub_index: int) -> bytes32:
    stem = address_to_stem(address, tree_index)
    return stem + bytes([sub_index])
```

## Account Subtree Layout

For any account, tree_index=0 gives the account subtree:

| Subindex | Content |
|----------|---------|
| 0 | Basic data (version, code_size, nonce, balance) |
| 1 | Code hash |
| 2-63 | Reserved |
| 64-127 | First 64 storage slots |
| 128-255 | First 128 code chunks |

### Basic Data Encoding (32 bytes, big-endian)

```
[0]:      version (1 byte)
[1-4]:    reserved (4 bytes)
[5-7]:    code_size (3 bytes)
[8-15]:   nonce (8 bytes)
[16-31]:  balance (16 bytes)
```

## Bytecode Chunking

Each chunk is 32 bytes:
- Byte 0: count of PUSHDATA bytes at start of this chunk
- Bytes 1-31: raw bytecode slice

### Chunking Algorithm

```python
PUSH1, PUSH32 = 0x60, 0x7f

def chunkify(code: bytes) -> list[bytes32]:
    # Pad to multiple of 31
    if len(code) % 31 != 0:
        code += b'\x00' * (31 - len(code) % 31)
    
    # Track pushdata spillover
    pushdata_remaining = [0] * (len(code) + 32)
    pos = 0
    while pos < len(code):
        opcode = code[pos]
        if 0x60 <= opcode <= 0x7f:  # PUSH1-PUSH32
            push_bytes = opcode - 0x5f
            for i in range(push_bytes):
                pushdata_remaining[pos + 1 + i] = push_bytes - i
            pos += 1 + push_bytes
        else:
            pos += 1
    
    # Build chunks
    chunks = []
    for i in range(0, len(code), 31):
        prefix = min(pushdata_remaining[i], 31)
        chunks.append(bytes([prefix]) + code[i:i+31])
    return chunks
```

### Worked Examples

**Example 1: Simple bytecode**
```
Input:  0x345f55 (3 bytes)
Output: [0x00345f55000000...00]  // prefix=0, no spillover
```

**Example 2: PUSH10 crossing chunk boundary**
```
Input: 0x...5b5b5b6911223344 | 5566778899aa5b5b...
                            ^ chunk boundary

Chunk 1: 0x00...5b5b5b69112233  // ends mid-PUSH10
Chunk 2: 0x07445566778899aa5b5b...  // prefix=7 (remaining push bytes)
```

## Storage Slot Location

```python
HEADER_STORAGE_OFFSET = 64
CODE_OFFSET = 128
MAIN_STORAGE_OFFSET = 256**31

def storage_key(address: bytes20, slot: int) -> bytes32:
    if slot < 64:  # First 64 in account subtree
        return get_tree_key(address, 0, HEADER_STORAGE_OFFSET + slot)
    else:  # Rest spread across tree
        pos = MAIN_STORAGE_OFFSET + slot
        tree_index = pos // 256
        sub_index = pos % 256
        return get_tree_key(address, tree_index, sub_index)
```

## Code Chunk Location

```python
def code_chunk_key(address: bytes20, chunk_id: int) -> bytes32:
    pos = CODE_OFFSET + chunk_id
    tree_index = pos // 256
    sub_index = pos % 256
    return get_tree_key(address, tree_index, sub_index)
```

First 128 chunks (chunk_id 0-127): in account subtree (subindex 128-255)
Remaining chunks: spread across tree by tree_index

## Proof Size Comparison

| Tree Type | Proof Size Formula | For N=2^24 |
|-----------|-------------------|------------|
| Binary (k=2) | 32 × 1 × log₂(N) | 768 bytes |
| Quad (k=4) | 32 × 3 × log₄(N) | 1152 bytes |
| Hex (k=16) | 32 × 15 × log₁₆(N) | 2880 bytes |

Binary is optimal for proof size.

## Implementation Checklist

- [ ] Node types: Empty, Internal, Stem, Leaf
- [ ] Hash function with empty special case
- [ ] Stem extraction from 32-byte key
- [ ] Tree insertion with stem splitting
- [ ] Address to tree key conversion
- [ ] Account data packing/unpacking
- [ ] Bytecode chunking with PUSH tracking
- [ ] Storage slot routing (first 64 vs main)
- [ ] Code chunk routing (first 128 vs main)
- [ ] Merkle proof generation
- [ ] Merkle proof verification

## Test Vectors

### Empty Tree
```
root_hash = 0x0000000000000000000000000000000000000000000000000000000000000000
```

### Single Insertion
```
key = 0x0000000000000000000000000000000000000000000000000000000000000001
value = 0x0000000000000000000000000000000000000000000000000000000000000001
stem = 0x000000000000000000000000000000000000000000000000000000000000
subindex = 0x01
```

### Two Insertions (Causing Split)
```
key1 = 0x0000...0001 (stem=0x00...00, subindex=1)
key2 = 0x8000...0000 (stem=0x80...00, subindex=0)

Tree structure:
  Internal
  ├─ left: StemNode(0x00...00)
  └─ right: StemNode(0x80...00)
```

## References

- EIP-7864: https://eips.ethereum.org/EIPS/eip-7864
- EIP-4762: Access events
- EIP-7612: Fork specification
- EIP-7748: MPT migration
