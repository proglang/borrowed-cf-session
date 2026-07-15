## Proposal for handling local and remote splits

### local splits

Instead of the lsplit primitive, we introduce a different primitive that
combines the splitting and the elimination of the resulting ordered pair.

let-split x → d in e₂

The assumption is that x is a variable that evaluates to a channel.
The let-split binds a new channel name d.
The typing rule for let-split:
(We use `;` for combining session types and `;;` for ordered assumptions.)


Δ ⊢ x : R; S
Γ (x : R ;; d : S) ⊢ e₂ : T | ε
------------------------------------
Γ(Δ) ⊢ let-split x → d in e₂ : T | ε


Operationally, `let-split x → d in []` is (part of) an evaluation context.
It fires when its subject is dropped as in:

let-split c → d in 𝓔[ drop c ] ⟶ 𝓔[ * ] [d := c]

### remote splits (as in the tex-priorities-compositional draft)

ν (b₁ c b₂) d* ... 𝓔[ rsplit c ] ...
⟶
ν (b₁ c c′ b₂) d* ... 𝓔[ c ⊗ c′ ] ...

Instead of having every operation check for a remote borrow, this is done by
new operations acquire and release. The point of acquire is that it checks
if c is in front of the stack and blocks, otherwise. The release operation
pops the ν-abstraction stack.

ν (c c*) d*. 𝓔[ acquire c ]
⟶
ν (c c*) d*. 𝓔[ c ]

ν (c c*) d*. 𝓔[ release c ]
⟶
ν (c*) d*. 𝓔[ * ]

