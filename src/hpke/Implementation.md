# hacspec implementation considerations
When defining HPKE in hacspec there are a number of considerations that have an
impact on the way the code looks.

The hacspec code is as close to the RFC pseudocode as possible.
But some changes are necessary.

### Randomness
hacspec does not allow to draw randomness.
It is therefore necessary to pass in randomness every time it is needed.

This approach is pretty close to the way this would be implemented in native Rust
where a random-number generator is passed in and used to generate randomness.

### Configuration Parameters
The HPKE RFC makes most of the configuration implicit to the functions rather than
passing the algorithm identifiers around.
Because the hacspec implementation has to know which algorithm to pick, this is
of course not possible here.

HPKE hacspec functions take either an [`HPKEConfig`] object with all algorithms
in it or the specific algorithm identifier needed for the operation.

### Naming
The HPKE RFC uses, in some cases, names that are impossible to use in hacspec
because they are keywords or contain illegal characters.
Further does hacspec not support member functions.

We therefore replace `.` in function calls such as `Context.Export` with an underscore,
i.e. write `Context_Export`.
Keywords such as `open` are replaced with a semantically equivalent, i.e. `HpkeOpen`.

### Secret bytes
hacspec has the notion of secret integers that can't be used for certain operations
and should enforce secret-independent computation time.

For simplicity the hacspec HPKE implementation uses secret bytes everywhere even
if not necessary, e.g. for cipher texts.

### Errors
While the RFC defines a set of errors it does not always define which errors
are raised.
For example, it leaves open whether implementations convert errors from the
Diffie-Hellman operations into KEM errors (`EncapError`/`DecapError`) or not.

With the specific implementation in hacspec here the errors are clearly defined.
