# clash-multicycle-moore

A multicycle module has the form

`(KnownNat d, 1 <= d) => DSignal dom m Bool -> DSignal dom m i -> DSignal dom (m + d + l) o`.

Assumptions:

  1. Input `Bool` is asserted in clock cycle `m` and will be ingored until on or after clock cycle `m + d + l`.

  2. Input `i` can be taken in unbuffered from clock cycle `m` to `m + d - 1`.

     - In particular, this means that an external buffer is necessary if `i` needs to remain unchanged during these clock cycles.

  3. Output `o` will be valid and remain unchanged on or after clock cycle `m + d + l` until the next trigger.

     - However, there is no guarantee what output `o` shall be before it becomes valid on clock cycle `m + d + l`.
