/-
  ArmadaLean.Token — the token a note holds, as a symbolic identity.

  A token is an ERC-20 contract. The protocol identifies it by its address
  (`TokenData.tokenAddress`, PoolTypes.sol:71-75). The contract feeds the
  zero-extended address to Poseidon as the note's token id (`_getTokenID`,
  TransactModule.sol:449-454: `bytes32(uint256(uint160(tokenAddress)))`). That cast
  is an encoding. This model does not represent it.

  `Token` wraps an address `Term` (`ArmadaLean.Poseidon`). The type has decidable
  equality and no arithmetic. Audit finding P-1
  (armada-laconic `labbook/2026-10-26-pool-layout-audit.md`) records the earlier
  `token : Nat` and why it went.
-/
import ArmadaLean.Poseidon

/-- A token, identified by its contract address. The address is a symbolic term, the
    same convention as every other address in this project (`ArmadaLean.PoolOwned`,
    module comment on address terms). -/
structure Token where
  address : Term
  deriving DecidableEq

/-- `_getTokenID` (TransactModule.sol:449-454): the term the circuit hashes into a
    note commitment for this token. For an ERC-20 token it is the address itself. -/
def tokenId (t : Token) : Term := t.address

/-- Two tokens with the same id are the same token. -/
theorem tokenId_inj {t₁ t₂ : Token} (h : tokenId t₁ = tokenId t₂) : t₁ = t₂ := by
  cases t₁; cases t₂; simp_all [tokenId]
