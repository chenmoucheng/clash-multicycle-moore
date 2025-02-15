# clash-multicycle-moore

A multicycle module has the form

`(KnownNat d, 1 <= d) => DSignal dom m Bool -> DSignal dom m a -> DSignal dom (m + d + l) b`.

Assumptions:

  1. Input `Bool` is asserted in clock cycle `m` and will be ingored until on or after clock cycle `m + d + l`.

  2. Input `a` can be taken in unbuffered from clock cycle `m` to `m + d - 1`.

     - In particular, this means that an external buffer is necessary if `a` needs to remain unchanged during these clock cycles.

  3. Output `b` will be valid and remain unchanged on or after clock cycle `m + d + l` until the next trigger.

     - However, there is no guarantee what output `b` shall be before it becomes valid on clock cycle `m + d + l`.
