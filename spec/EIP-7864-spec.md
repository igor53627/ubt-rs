# EIP-7864: Unified Binary Tree - Formal Specification

**Version:** 1.0.0  
**Based on:** [EIP-7864](https://eips.ethereum.org/EIPS/eip-7864)  
**Authors:** Formal specification derived from EIP-7864 by Vitalik Buterin et al.

---

## 1. Preliminaries

### 1.1 Notation

| Symbol | Description |
|--------|-------------|
| $\mathbb{B}$ | Set of bytes $\{0, 1, \ldots, 255\}$ |
| $\mathbb{B}^n$ | Byte strings of length $n$ |
| $\mathbb{B}^*$ | Byte strings of arbitrary length |
| $\mathbb{B}^{32}$ | 32-byte values (256 bits) |
| $\mathbb{B}^{31}$ | 31-byte stems (248 bits) |
| $\|x\|$ | Length of byte string $x$ |
| $x \cdot y$ | Concatenation of byte strings |
| $x[i]$ | $i$-th byte of $x$ (0-indexed) |
| $x[i:j]$ | Bytes from index $i$ to $j-1$ |
| $\mathbf{0}^n$ | $n$ zero bytes |
| $H: \mathbb{B}^* \to \mathbb{B}^{32}$ | Cryptographic hash function |

### 1.2 Constants

$$
\begin{aligned}
\text{STEM\_LEN} &= 31 \\
\text{SUBINDEX\_BITS} &= 8 \\
\text{STEM\_SUBTREE\_WIDTH} &= 256 = 2^8 \\
\text{BASIC\_DATA\_LEAF\_KEY} &= 0 \\
\text{CODE\_HASH\_LEAF\_KEY} &= 1 \\
\text{HEADER\_STORAGE\_OFFSET} &= 64 \\
\text{CODE\_OFFSET} &= 128 \\
\text{MAIN\_STORAGE\_OFFSET} &= 2^{248}
\end{aligned}
$$

---

## 2. Tree Structure

### 2.1 Keys

A **tree key** $k \in \mathbb{B}^{32}$ is decomposed into:

$$
k = (\text{stem}, \text{subindex}) \quad \text{where} \quad 
\begin{cases}
\text{stem} = k[0:31] \in \mathbb{B}^{31} \\
\text{subindex} = k[31] \in \mathbb{B}
\end{cases}
$$

Keys with the same stem are **co-located** in a 256-value subtree.

### 2.2 Node Types

The tree consists of four node types:

$$
\text{Node} ::= \text{Empty} \mid \text{Internal}(L, R) \mid \text{Stem}(s, L, R) \mid \text{Leaf}(v)
$$

Where:
- $\text{Empty}$: Represents an empty subtree
- $\text{Internal}(L, R)$: Internal branching node with left child $L$ and right child $R$
- $\text{Stem}(s, L, R)$: Stem node with stem $s \in \mathbb{B}^{31}$ and children for 256-value subtree
- $\text{Leaf}(v)$: Leaf node containing value $v \in \mathbb{B}^{32}$

### 2.3 Hash Function

**Definition (Hash with Zero Special Case):**

$$
\mathcal{H}(x) = 
\begin{cases}
\mathbf{0}^{32} & \text{if } x = \mathbf{0}^{|x|} \\
H(x) & \text{otherwise}
\end{cases}
$$

Where $H$ is the underlying hash function (BLAKE3 in reference implementation, final TBD).

### 2.4 Node Hashing (Merkleization)

**Definition (Node Hash):**

$$
\text{hash}(n) = 
\begin{cases}
\mathbf{0}^{32} & \text{if } n = \text{Empty} \\
\mathcal{H}(\text{hash}(L) \cdot \text{hash}(R)) & \text{if } n = \text{Internal}(L, R) \\
\mathcal{H}(s \cdot \mathbf{0}^1 \cdot \mathcal{H}(\text{hash}(L) \cdot \text{hash}(R))) & \text{if } n = \text{Stem}(s, L, R) \\
\mathcal{H}(v) & \text{if } n = \text{Leaf}(v)
\end{cases}
$$

**Lemma 2.1 (Empty Subtree Hash):** For any empty subtree, $\text{hash}(\text{Empty}) = \mathbf{0}^{32}$.

**Lemma 2.2 (Hash Determinism):** The hash of a tree is uniquely determined by its contents.

---

## 3. Tree Operations

### 3.1 Path Traversal

For a stem $s \in \mathbb{B}^{31}$, the **bit path** is:

$$
\text{bit}(s, i) = \left\lfloor \frac{s[\lfloor i/8 \rfloor]}{2^{7 - (i \mod 8)}} \right\rfloor \mod 2
\quad \text{for } i \in \{0, \ldots, 247\}
$$

Traversal follows MSB-first ordering.

### 3.2 Lookup

**Definition (Get):**

$$
\text{get}(T, k) = 
\begin{cases}
\bot & \text{if } T = \text{Empty} \\
\text{get}(L, k) & \text{if } T = \text{Internal}(L, R) \land \text{bit}(k.\text{stem}, d) = 0 \\
\text{get}(R, k) & \text{if } T = \text{Internal}(L, R) \land \text{bit}(k.\text{stem}, d) = 1 \\
\text{values}[k.\text{subindex}] & \text{if } T = \text{Stem}(s, L, R) \land s = k.\text{stem} \\
\bot & \text{if } T = \text{Stem}(s, L, R) \land s \neq k.\text{stem}
\end{cases}
$$

Where $d$ is the current depth and $\text{values}$ is the sparse map within the stem node.

### 3.3 Insertion

**Definition (Insert):**

Given tree $T$, key $k$, and value $v$:

$$
\text{insert}(T, k, v) = T'
$$

Where $T'$ is constructed by:

1. If $T = \text{Empty}$: Create $\text{Stem}(k.\text{stem}, \_, \_)$ with $v$ at subindex $k.\text{subindex}$
2. If $T = \text{Stem}(s, L, R)$ and $s = k.\text{stem}$: Update value at subindex
3. If $T = \text{Stem}(s, L, R)$ and $s \neq k.\text{stem}$: 
   - Find first differing bit $b = \text{firstDiff}(s, k.\text{stem})$
   - Create internal nodes to separate the two stems
4. If $T = \text{Internal}(L, R)$: Recursively insert into appropriate child

**Invariant 3.1 (Minimal Internal Nodes):** The tree contains the minimum number of internal nodes necessary to distinguish all stems.

### 3.4 Deletion

**Definition (Delete):**

$$
\text{delete}(T, k) = \text{insert}(T, k, \mathbf{0}^{32})
$$

Setting a value to zero is equivalent to deletion.

---

## 4. State Embedding

### 4.1 Key Derivation

**Definition (Binary Tree Key):**

For address $a \in \mathbb{B}^{20}$ and input key $\kappa \in \mathbb{B}^{32}$:

$$
\text{TreeKey}(a, \kappa) = (\text{stem}, \text{subindex})
$$

Where:
$$
\begin{aligned}
h &= \text{SHA256}(\mathbf{0}^{12} \cdot a \cdot \kappa[0:31]) \\
\text{stem} &= h[0:31] \\
\text{subindex} &= \kappa[31]
\end{aligned}
$$

### 4.2 Account Data Layout

For account at address $a$:

| Data | Input Key $\kappa$ | Subindex |
|------|-------------------|----------|
| Basic Data | $\mathbf{0}^{31} \cdot 0$ | 0 |
| Code Hash | $\mathbf{0}^{31} \cdot 1$ | 1 |
| Reserved | $\mathbf{0}^{31} \cdot i$ for $i \in [2, 63]$ | $i$ |
| Storage Slot $i$ (for $i < 64$) | $\mathbf{0}^{31} \cdot (64 + i)$ | $64 + i$ |
| Code Chunk $i$ (for $i < 128$) | $\mathbf{0}^{31} \cdot (128 + i)$ | $128 + i$ |

### 4.3 Basic Data Leaf Format

The basic data leaf ($\text{subindex} = 0$) contains:

$$
\text{BasicData} = \text{version} \cdot \text{reserved} \cdot \text{codeSize} \cdot \text{nonce} \cdot \text{balance}
$$

| Field | Bytes | Offset | Size |
|-------|-------|--------|------|
| version | 0 | 0 | 1 |
| reserved | 1-4 | 1 | 4 |
| codeSize | 5-7 | 5 | 3 |
| nonce | 8-15 | 8 | 8 |
| balance | 16-31 | 16 | 16 |

**Encoding:**
$$
\text{encode}(n, b, c) = \mathbf{0}^1 \cdot \mathbf{0}^4 \cdot \text{BE}_3(c) \cdot \text{BE}_8(n) \cdot \text{BE}_{16}(b)
$$

Where $\text{BE}_k(x)$ is the $k$-byte big-endian encoding of $x$.

### 4.4 Storage Slot Keys

**Definition (Storage Key):**

For storage slot $\sigma \in \mathbb{B}^{32}$:

$$
\text{StorageKey}(a, \sigma) = 
\begin{cases}
\text{TreeKey}(a, \mathbf{0}^{31} \cdot (64 + \sigma[31])) & \text{if } \sigma[0:31] = \mathbf{0}^{31} \land \sigma[31] < 64 \\
\text{TreeKey}(a, 1 \cdot \sigma[0:31] \cdot \sigma[31]) & \text{otherwise}
\end{cases}
$$

The first case handles header storage (slots 0-63 co-located with account).
The second case uses main storage offset ($1 \cdot \ldots$ represents $2^{248}$).

### 4.5 Code Chunk Keys

**Definition (Code Chunk Key):**

For chunk number $c \in \mathbb{N}$:

$$
\text{CodeChunkKey}(a, c) = \text{TreeKey}(a, \kappa_c)
$$

Where $\kappa_c[24:32] = \text{LE}_8(128 + c)$ (little-endian).

---

## 5. Code Chunkification

### 5.1 Chunk Format

Each code chunk is 32 bytes:

$$
\text{Chunk} = \text{pushdata\_count} \cdot \text{code}[0:31]
$$

Where:
- $\text{pushdata\_count} \in [0, 31]$: Number of leading bytes that are PUSHDATA
- $\text{code}$: 31 bytes of actual bytecode

### 5.2 Chunkification Algorithm

**Definition (ChunkifyCode):**

Given bytecode $B \in \mathbb{B}^*$:

$$
\text{ChunkifyCode}(B) = [C_0, C_1, \ldots, C_{n-1}]
$$

Where $n = \lceil |B| / 31 \rceil$ and each chunk $C_i$ is computed as:

1. $C_i.\text{code} = B[31i : \min(31(i+1), |B|)]$ (padded with zeros)
2. $C_i.\text{pushdata\_count} = $ number of leading bytes that are PUSHDATA from previous chunk's PUSH instruction

**PUSH Opcodes:**
$$
\text{pushSize}(\text{op}) = 
\begin{cases}
\text{op} - 0x5F & \text{if } 0x60 \leq \text{op} \leq 0x7F \\
0 & \text{otherwise}
\end{cases}
$$

---

## 6. Invariants and Properties

### 6.1 Tree Invariants

**Invariant 6.1 (Well-Formedness):**
A UBT $T$ is well-formed iff:
1. All internal nodes have exactly two children
2. All stem nodes have stems of length 31
3. All leaf values are 32 bytes
4. No two stem nodes share the same stem

**Invariant 6.2 (Minimal Depth):**
For any two stems $s_1 \neq s_2$ in tree $T$, they are separated at depth $d$ where $d = \min\{i : \text{bit}(s_1, i) \neq \text{bit}(s_2, i)\}$.

### 6.2 Hash Properties

**Property 6.1 (Collision Resistance):**
Under the assumption that $H$ is collision-resistant:
$$
\Pr[\text{hash}(T_1) = \text{hash}(T_2) \land T_1 \neq T_2] \approx 0
$$

**Property 6.2 (Determinism):**
$$
\forall T. \text{hash}(T) = \text{hash}(T)
$$

**Property 6.3 (Order Independence):**
For any sequence of insertions $[(k_1, v_1), \ldots, (k_n, v_n)]$ and any permutation $\pi$:
$$
\text{hash}(\text{insertAll}(T, [(k_1, v_1), \ldots])) = \text{hash}(\text{insertAll}(T, [(k_{\pi(1)}, v_{\pi(1)}), \ldots]))
$$

### 6.3 Correctness Properties

**Property 6.4 (Get-Insert):**
$$
\text{get}(\text{insert}(T, k, v), k) = v \quad \text{if } v \neq \mathbf{0}^{32}
$$

**Property 6.5 (Get-Insert-Other):**
$$
\text{get}(\text{insert}(T, k, v), k') = \text{get}(T, k') \quad \text{if } k \neq k'
$$

**Property 6.6 (Delete-Get):**
$$
\text{get}(\text{delete}(T, k), k) = \bot
$$

---

## 7. Proof Size Analysis

### 7.1 Merkle Proof Size

For a tree with $N$ stems, the expected proof size for a single key is:

$$
\text{ProofSize}(N) \approx 32 \cdot \log_2(N) + 31 + 32 \cdot 8
$$

Components:
- $32 \cdot \log_2(N)$: Sibling hashes on path to stem
- $31$: Stem value
- $32 \cdot 8$: Proof within 256-value subtree

### 7.2 Comparison with MPT

| Tree Type | Arity | Proof Size Formula |
|-----------|-------|-------------------|
| MPT (Hexary) | 16 | $15 \cdot 32 \cdot \log_{16}(N)$ |
| UBT (Binary) | 2 | $1 \cdot 32 \cdot \log_2(N)$ |

For $N = 2^{32}$:
- MPT: $\approx 3840$ bytes
- UBT: $\approx 1024$ bytes

---

## 8. References

1. [EIP-7864: Ethereum state using a unified binary tree](https://eips.ethereum.org/EIPS/eip-7864)
2. [EIP-7612: Verkle state transition via overlay tree](https://eips.ethereum.org/EIPS/eip-7612)
3. [EIP-4762: Statelessness gas cost changes](https://eips.ethereum.org/EIPS/eip-4762)
4. [go-ethereum bintrie implementation](https://github.com/ethereum/go-ethereum/tree/master/trie/bintrie)

---

## Appendix A: Type Definitions (Rust)

```rust
type Stem = [u8; 31];
type SubIndex = u8;
type Value = [u8; 32];

struct TreeKey {
    stem: Stem,
    subindex: SubIndex,
}

enum Node {
    Empty,
    Internal { left: Box<Node>, right: Box<Node> },
    Stem { stem: Stem, left: Box<Node>, right: Box<Node>, values: HashMap<SubIndex, Value> },
    Leaf { value: Value },
}
```

## Appendix B: Hash Function Candidates

| Function | Out-of-Circuit | In-Circuit | Post-Quantum | Status |
|----------|---------------|------------|--------------|--------|
| BLAKE3 | Excellent | Good | Yes | Reference |
| Keccak | Good | Moderate | Yes | Candidate |
| Poseidon2 | Moderate | Excellent | Yes | Candidate |
