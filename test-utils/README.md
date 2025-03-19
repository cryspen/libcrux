# `libcrux-test-utils`

This crate contains tools for testing, tracing, profiling and benchmarking.

## Tracing (`tracing`)

This module provides tools for annotating functions such that calls are traced.
That means that whenever the function is called and when it returns, an entry
is written to the specified trace.

Usually, that trace will be a static variable with interior mutability. If in
doubt, define it something like this:

In this example we use `cfg` and `cfg_attr` to ensure that the tracing only runs
during testing. In many cases one might want to also restrict this to only trace
if a certain feature is enabled. This can be done using the same mechanism.

```rust
#[cfg(test)]
use std::sync::LazyLock;

#[cfg(test)]
static TRACE: LazyLock<MutexTrace<&'static str, Instant>> =
    LazyLock::new(|| MutexTrace::default());
```

The `MutexTrace` can be defined and used as a static variable without unsafe, but,
depending on the setting, my introduce too much overhead. Any type that implements
`Trace` works.

Then, annotate a function like this:

```rust
#[cfg_attr(test, libcrux_macros::trace_span("some_traced_function", TRACE))]
fn this_function_is_traced() {
  // ...
}
```

The macro is called `trace_span` because it traces a start and end, identified
by a label. The type of the label can be chosen generically, here it is
`&'static str`. There also are on-the-fly tracing facilities.

After the code in question ran, the trace can be inspected. Due to the use
of  interior mutability, there is no generic way to get a reference to the
inner slice; therefore, it is easiest to just clone it.

```rust
println!((*TRACE).clone().report());
```
