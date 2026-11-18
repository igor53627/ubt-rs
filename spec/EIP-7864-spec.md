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

A leaf is **present** when the subtree of its stem node holds $\text{Leaf}(v)$ at its subindex, for every $v \in \mathbb{B}^{32}$, including $v = \mathbf{0}^{32}$. A leaf is **absent** when that position is $\text{Empty}$. A present leaf with the value $\mathbf{0}^{32}$ and an absent leaf are different.

### 2.3 Hash Function

**Definition (Pair Hash with Zero Special Case):**

For a 64-byte input $x \in \mathbb{B}^{64}$:

$$
\mathcal{H}(x) = 
\begin{cases}
\mathbf{0}^{32} & \text{if } x = \mathbf{0}^{64} \\
H(x) & \text{otherwise}
\end{cases}
$$

Where $H$ is the underlying hash function (BLAKE3 in reference implementation, final TBD).

The zero rule holds for the 64-byte input only. This input is the pair of child hashes of an internal node or of a node in the 256-value subtree, or the input $s \cdot \mathbf{0}^1 \cdot r$ of a stem node.

**Definition (Leaf Hash):**

For a present leaf with the value $v \in \mathbb{B}^{32}$:

$$
\mathcal{H}_{\text{leaf}}(v) = H(v) \quad \text{for every } v \text{, including } v = \mathbf{0}^{32}
$$

There is no zero rule for the 32-byte input of a leaf. A present leaf with the value $\mathbf{0}^{32}$ hashes to $H(\mathbf{0}^{32})$, which is not $\mathbf{0}^{32}$ (for SHA-256 it is `66687aad...0d5f2925`). An absent leaf is an empty subtree and contributes $\mathbf{0}^{32}$ without a call of $H$.

This is the rule of go-ethereum `trie/bintrie`. Versions of this specification before the zero-value change applied the zero rule to every all-zero input, so that a leaf with the value $\mathbf{0}^{32}$ had the hash of an absent leaf.

### 2.4 Node Hashing (Merkleization)

**Definition (Node Hash):**

$$
\text{hash}(n) = 
\begin{cases}
\mathbf{0}^{32} & \text{if } n = \text{Empty} \\
\mathcal{H}(\text{hash}(L) \cdot \text{hash}(R)) & \text{if } n = \text{Internal}(L, R) \\
\mathcal{H}(s \cdot \mathbf{0}^1 \cdot \mathcal{H}(\text{hash}(L) \cdot \text{hash}(R))) & \text{if } n = \text{Stem}(s, L, R) \\
\mathcal{H}_{\text{leaf}}(v) = H(v) & \text{if } n = \text{Leaf}(v)
\end{cases}
$$

**Lemma 2.1 (Empty Subtree Hash):** For any empty subtree, $\text{hash}(\text{Empty}) = \mathbf{0}^{32}$.

**Lemma 2.2 (Hash Determinism):** The hash of a tree is uniquely determined by its contents.

**Lemma 2.3 (Zero Leaf Is Not Empty):** $\text{hash}(\text{Leaf}(\mathbf{0}^{32})) = H(\mathbf{0}^{32})$ and $\text{hash}(\text{Empty}) = \mathbf{0}^{32}$. The two are different unless $H(\mathbf{0}^{32}) = \mathbf{0}^{32}$, which does not hold for SHA-256 or BLAKE3.

A stem node holds one present leaf or more (Invariant 6.1). Insertion creates a stem node with one leaf, and deletion removes a stem node with its last leaf (Section 3.4).

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

$\text{values}[i] = \bot$ for an absent leaf, and $\text{values}[i] = v$ for a present leaf with the value $v$. So $\text{get}$ returns $\bot$ for an absent leaf and $\mathbf{0}^{32}$ for a present leaf with the value $\mathbf{0}^{32}$.

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

The value $v$ is stored as a present leaf for every $v$, including $v = \mathbf{0}^{32}$. An insertion of $\mathbf{0}^{32}$ does not remove the leaf or the stem node.

**Invariant 3.1 (Minimal Internal Nodes):** The tree contains the minimum number of internal nodes necessary to distinguish all stems.

### 3.4 Deletion

**Definition (Delete):**

Given tree $T$ and key $k$:

$$
\text{delete}(T, k) = T'
$$

Where $T'$ is constructed by:

1. If $T$ has no stem node with the stem $k.\text{stem}$: $T' = T$
2. Otherwise: Remove the leaf at subindex $k.\text{subindex}$ of that stem node. The position becomes $\text{Empty}$, and the leaf is absent
3. If the stem node has no present leaf left: Remove the stem node, and remove the internal nodes that are no longer necessary to distinguish the stems that remain (Invariant 3.1)

After a deletion the key is in the state "never written": $\text{get}(\text{delete}(T, k), k) = \bot$.

**Definition (Zero Write):**

$$
\text{zeroWrite}(T, k) = \text{insert}(T, k, \mathbf{0}^{32})
$$

A zero write is not a deletion. It leaves a present leaf with the value $\mathbf{0}^{32}$, and it keeps the stem node. The zero write is the go-ethereum way to delete: `DeleteStorage` and `DeleteAccount` of go-ethereum `trie/bintrie` write $\mathbf{0}^{32}$, and go-ethereum has no operation that removes a leaf or a stem node. A zero write and a deletion give different trees, and different root hashes under the assumptions of Property 6.7.

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

Where $\kappa_c[23:31] = \text{BE}_8(\text{stem\_index})$ (big-endian) and $\kappa_c[31] = \text{subindex}$.

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
5. Every stem node holds one present leaf or more

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
\text{get}(\text{insert}(T, k, v), k) = v
$$

The property holds for every $v$, including $v = \mathbf{0}^{32}$.

**Property 6.5 (Get-Insert-Other):**
$$
\text{get}(\text{insert}(T, k, v), k') = \text{get}(T, k') \quad \text{if } k \neq k'
$$

**Property 6.6 (Delete-Get):**
$$
\text{get}(\text{delete}(T, k), k) = \bot
$$

Deletion is a removal of the leaf, for every value that the leaf holds, including $\mathbf{0}^{32}$. It does not change other keys:
$$
\text{get}(\text{delete}(T, k), k') = \text{get}(T, k') \quad \text{if } k \neq k'
$$

If the leaf at $k$ is the last present leaf of its stem node, $\text{delete}(T, k)$ has no stem node with the stem $k.\text{stem}$. If $\text{get}(T, k) = \bot$, a deletion after an insertion restores the tree:
$$
\text{delete}(\text{insert}(T, k, v), k) = T \quad \text{if } \text{get}(T, k) = \bot
$$

**Property 6.7 (Zero Write):**
$$
\text{get}(\text{insert}(T, k, \mathbf{0}^{32}), k) = \mathbf{0}^{32} \neq \bot = \text{get}(\text{delete}(T, k), k)
$$

A zero write leaves a present leaf, and a deletion leaves no leaf, so the two lookups are different for every $T$. The trees $\text{insert}(T, k, \mathbf{0}^{32})$ and $\text{delete}(T, k)$ are also different. Their root hashes are different with overwhelming probability under two assumptions:

1. Property 6.1 (collision resistance of $H$)
2. An output of $H$ is $\mathbf{0}^{32}$ only with negligible probability

The second assumption is necessary because $\text{delete}(T, k)$ can be the empty tree. Its hash is the constant $\mathbf{0}^{32}$ of Section 2.4, which is not an output of $H$, so Property 6.1 does not cover it. The all-zero pair of Section 2.3 has the hash $\mathbf{0}^{32}$ by rule and is not part of the assumption.

$$
\Pr[\text{hash}(\text{insert}(T, k, \mathbf{0}^{32})) = \text{hash}(\text{delete}(T, k))] \approx 0
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
    // An entry of `values` is a present leaf, also when its value is zero.
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
