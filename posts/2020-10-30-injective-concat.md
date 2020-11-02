---
pagetitle: Injective ByteString `concat` in Agda
---

# Injective ByteString `concat` in Agda

## The Problem

  This little post arises from a small exercise we've done while at Oracle Labs,
when we (myself, Mark Moir, Harold Carr and Lisandra Silva) were working on 
formal verification of authenticated data structures and needed to reason
about the hash of certain compound structs. It is often
the case one needs to combine two or more values and feed the result
to a hash function. For the sake of this discussion, say we are writing some
Haskell function `hashL` that is supposed to combine a list of `ByteString`s 
into a finite length bitstring in a _collision resistant_ fashion. 
We say a hash function `h` is collision resistant iff it 
is computationally infeasible to find two distinct 
inputs `x` and `y` such that `h x == h y`.

In the remainder of this post we'll assume `hash` is a 
collision resistant hash function and will explore how to construct
a function `hashL` that receives a list and produces a hash.
The final objective is to construct `hashL` to be 
collision resistant.

A bad first approximation for `hashL` could be:

~~~~ { .haskell }
hashL :: [ByteString] -> Hash
hashL bs = hash (concat bs)
~~~~

Even though `hash` is itself collision resistant, since `concat` is _not_
injective, we can easily show `hashL` is not collision resistant:

```haskell
hashL ["abc", "de"] == hash (concat ["abc" , "de"])
                    == hash (concat ["ab" , "cde"])
                    == hashL ["ab", "cde"]
```

Using a field separator will not save us. Since the input `ByteString`s can
contain any character, one of the inputs might contain the separator itself.
For example, take:

```haskell
hashL bs = hash (concat $ intersperse ";" bs)
```

It is still the case that `hashL` is not collision resistant: `hashL
["a;b", "c"]` yields the same result as `hashL ["a", "b;c"]`.

The main issue is the non-injective `concat` function,
given `concat xs == concat ys`, is is not necessarily the
case that `xs == ys`. If we use some injective function `encode`
instead of concat, and define `hashL` as `hash . encode` we
can show that finding a collision for `hashL` requires
finding a collision for `hash`.

## Encoding `[ByteString]`

In practice, the `encode` function is often some variant of 
`DER` from the [ASN.1](http://luca.ntop.org/Teaching/Appunti/asn1.html) standards.
Encoding a value `x` with `DER` can be thought of as something like: `concat [ tagTypeOf x , length (toByteString x) , toByteString x ]`. Take Haskell's `Data.Serialize.encode`, for
example, which does something similar for encoding
[lists](http://hackage.haskell.org/package/cereal-0.5.8.1/docs/src/Data.Serialize.html#line-478):
it prefixes the length of the list before encoding its elements, for example:

```haskell
encode :: [ByteString] -> ByteString
encode as = encodeWord64 (length as) ++ concatMap encodeS as
  where encodeS s = encodeWord64 (B.length s) ++ s
```

The `encode` function above will work just fine in practice as long as
no bytestring in the input list exceeds the maximum size, in this
case, `2^64`. This means that to prove injectivity of this method
we would need to constrain all inputs to encode to less than the
maximum number of bytes, otherwise the function is _not_ injective.
This is at least a little inconvenient. 

In fact, we will be switching to Agda for disussing the injevtivity proof,
we also assume some Agda (or any other depentently typed language) experience
from the reader. Let us warm up with the necessary definitions to talk
about `ByteString`s, defined as a list of bytes:

```agda
data Bit : Set where
  I O : Bit

ByteString : Set
ByteString = List (Vec Bit 8)

BitString : Set
BitString = List Bit
```

The DER approach mentioned above would yield an injectivity lemma
modulo some constraint on the lengths of the inputs. It could be
captured by someting like the following Agda type:

```agda
    (xs ys : List ByteString) 
  → All (\ x → length x < MaxLen) xs
  → All (\ y → length y < MaxLen) ys
  → encode xs == encode ys
  → xs == ys
```

The type above reads "for all lists `xs` and `ys` such that all elements
of `xs` (resp. `ys`) have length smaller than `MaxLen`, `encode` is injective".
Using this to reason about complex usages of `encode` will quickly become
intractable as we would have to keep carrying proofs about the lengths
of the input bytestrings.

As it turns out, there is an easier option. We can encode the list 
structure, with codes for `(:)` and `[]`, directly. 
This can be thought of as something like `toJSON`, for example. 
Instead of dealing with complex formats, we will add two bits for every
byte in the original input. These two bits will distinguish three situations,
observed in the `toBitString-tag` Agda function below.

```agda
toBitString-tag : ByteString → BitString
toBitString-tag []       = O ∷ O ∷ []
toBitString-tag (b ∷ bs) = I ∷ O ∷ Vec-toList b ++ toBitString-tag' bs 

toBitString-tag' : ByteString → BitString
toBitString-tag' = map (\ x →  I ∷ I ∷ x)
```

Finally, the `encode` function can be given by:

```agda
encode : List ByteString -> BitString
encode = concat ∘ List-map toBitString-tag
```

But why is it injective? How do we prove it? 
Let us calculate what would it take to have `encode` produce two 
equal results for different lists. We start with:

```
encode ([a] ∷ c) ≡ encode ([b₀ , b₁] ∷ d)
```

Which is definitionally equal to:

```
toBitString-tag [a] ++ encode c ≡ toBitString-tag [b₀ , b₁] ++ encode d
```

Another definitional equality, reducing `toBitString-tag`, yields:

```
1 0 a₀ ⋯  a₇ ++ encode c ≡ 1 0 b₀₀ ⋯  b₀₇ 1 1 b₁₀ ⋯ b₁₇ ++ encode d
```

Since `++` is injective for same-length prefixes -- if `xs ++ ys == ws ++ zs` and
`length xs == length ws`, then `xs == ws` and `ys == zs` -- the equality above
holds if and only if:

1. `aᵢ ≡ b₀ᵢ` for `i <- [0..7]`
2. `encode c ≡ 1 1 b₁₀ ⋯ b₁₇ ++ encode d`

Note however, that whatever the input, `encode` will always yield
a bitstring with `10` at the head, hence, it is impossible for (2)
above to hold. This is good: we've sketched a proof that 
`encode ([a] ∷ c) ≡ encode ([b₀ , b₁] ∷ d)` is impossible based on the
invariant that `encode x` always starts with `10` and by reasoning
over `xs ++ ys == ws ++ zs`. This gives us the blueprint we need to
move towards an Agda proof.

The Agda proof relies heavily on reasoning about 
about `xs ++ ys == ws ++ zs`, where we infer that
`xs` is a prefix of `ws` or vice-versa.
In Agda, we write that a list is a prefix of another through the datatype below:

```agda
data _≺_ {a}{A : Set a} : List A → List A → Set where
  z≺n : ∀{xs}      → [] ≺ xs
  s≺s : ∀{x xs ys} → xs ≺ ys → (x ∷ xs) ≺ (x ∷ ys)
```
        
A value of type `xs ≺ ys` represents a proof that `xs` is a prefix
of `ys`. In other words, there exists `zs` such that `xs ++ zs = ys`.
Moreover, we can extract the `zs` directly from the proof:

```agda
≺-drop : ∀{a}{A : Set a}{xs ys : List A} → xs ≺ ys → List A
≺-drop {ys = ys} z≺n = ys
≺-drop (s≺s a)       = ≺-drop a
```

Next, we capture this reasoning over the hypothesis that some `xs ++ ys`
coincides with some `ws ++ zs` through a universal property:

```agda
++-≺ : ∀{a}{A : Set a}(xs ws : List A){ys zs : List A}
     → xs ++ ys ≡ ws ++ zs
     → Σ (xs ≺ ws) (λ prf → ≺-drop prf ++ zs ≡ ys)
     ⊎ Σ (ws ≺ xs) (λ prf → ≺-drop prf ++ ys ≡ zs)
```

Note that besides returning whether `xs` is a prefix of `ws` or vice-versa,
we additionally return a universal characterization for `ys` (resp `zs`).
The proof of `++-≺` is a straightforward induction on both `xs` and `ws`.

Next, we need a proof that if `toBitString-tag a` is a prefix of
`toBitString-tag b`, then either `a = b` or the suffix of `toBitString-tag b`
that arises from removing the prefix `toBitString-tag a`
starts with `11`:

```agda
toBitString-tag-≺
  : ∀{a b}
  → (a≺bbs : toBitString-tag a ≺ toBitString-tag b)
  → a ≡ b ⊎ ∃[ tail ] (≺-drop a≺bbs ≡ I ∷ I ∷ tail)
```

Proving `toBitString-tag-≺` above requires two lemmas. One about
how `xs ++ ys ≺ ws ++ zs` implies `ys ≺ zs` when `length xs == length ws`.
The second one is exactly like `toBitString-tag-≺` but concerns the
auxiliary `toBitString-tag'` function.

The observation that `encode` never starts with `11` is trivial to prove:

```agda
encode-[]⊎tf : ∀ as {bs} → true ∷ true ∷ bs ≢ encode as
encode-[]⊎tf ([] ∷ as) ()
encode-[]⊎tf ((_ ∷ _) ∷ as) () 
```

Finally, we have all the necesary tools to prove that `encode` is injective.

```agda
encode-inj : ∀ xs ys → encode xs ≡ encode ys → xs ≡ ys
```

The proof goes by induction on `xs` and `ys`, as expected.
             
```agda
encode-inj (a ∷ as) (b ∷ bs) hyp 
  with ++-≺ (toBitString-tag a) (toBitString-tag b) hyp
...| inj₁ (a≺b , prf) 
  with toBitString-tag-≺ a≺b 
...| inj₁ refl = cong (a ∷_) (encode-inj as bs ...)
...| inj₂ (tail , aux) rewrite aux = ⊥-elim (encode-[]⊎tf as prf)
encode-inj (a ∷ as) (b ∷ bs) hyp 
   | inj₂ (b≺a , prf) = -- symmetric
```

## Wrapping it up

If you come accross the need to use a hash function to combine multiple
values and, moreover, you need to rely on collision resistance of this
construction, make sure you reason carefully about how you are 
writing this. 

All in all, this was a fun Agda excercise and illustrates well the process
of solving a problems with Agda. We first find the relations we
need, then encode them in suitable datatypes (list prefixes in our case)
and only then go on to actually proving things.


