use std::{
    ops::Deref,
    time::{Duration, Instant},
};

use libcrux_test_utils::tracing::{EventType, MutexTrace, RefCellTrace, Trace};

#[test]
fn test_refcell_trace_entries() {
    let trace = RefCellTrace::<&str, Instant>::default();

    {
        let _handle = trace.emit_span("test block");
        std::thread::sleep(Duration::from_millis(3));
    }

    let entries = trace.entries();
    let [open, close] = entries.deref() else {
        panic!("got wrong number of entries")
    };

    assert_eq!(open.ty, EventType::SpanOpen);
    assert_eq!(open.label, "test block");

    assert_eq!(close.ty, EventType::SpanClose);
    assert_eq!(close.label, "test block");

    assert!(open.at < close.at);
}

#[test]
fn test_mutex_trace_report() {
    test_trace_report(&MutexTrace::default());
}
#[test]
fn test_refcell_trace_report() {
    test_trace_report(&RefCellTrace::default());
}

#[test]
fn test_nested_mutex_trace_report() {
    test_nested_trace_report(&MutexTrace::default());
}
#[test]
fn test_nested_refcell_trace_report() {
    test_nested_trace_report(&RefCellTrace::default());
}

fn test_trace_report(trace: &(impl Clone + Trace<Label = &'static str, TimeStamp = Instant>)) {
    {
        let _handle = trace.emit_span("test block");
        std::thread::sleep(Duration::from_millis(3));
    }

    let entries = trace.clone().report();
    let [open, close] = entries.as_slice() else {
        panic!("got wrong number of entries")
    };

    assert_eq!(open.ty, EventType::SpanOpen);
    assert_eq!(open.label, "test block");

    assert_eq!(close.ty, EventType::SpanClose);
    assert_eq!(close.label, "test block");

    assert!(open.at < close.at);
}

fn test_nested_trace_report(
    trace: &(impl Clone + Trace<Label = &'static str, TimeStamp = Instant>),
) {
    {
        let _handle = trace.emit_span("outer block");
        std::thread::sleep(Duration::from_millis(3));

        let _handle2 = trace.emit_span("inner block");
        std::thread::sleep(Duration::from_millis(2));
    }

    let entries = trace.clone().report();
    let [open_outer, open_inner, close_inner, close_outer] = entries.as_slice() else {
        panic!("got wrong number of entries")
    };

    assert_eq!(open_outer.ty, EventType::SpanOpen);
    assert_eq!(open_inner.ty, EventType::SpanOpen);

    assert_eq!(open_outer.label, "outer block");
    assert_eq!(open_inner.label, "inner block");

    assert_eq!(close_inner.label, "inner block");
    assert_eq!(close_outer.label, "outer block");

    assert_eq!(close_inner.ty, EventType::SpanClose);
    assert_eq!(close_outer.ty, EventType::SpanClose);

    assert!(open_outer.at < open_inner.at);
    assert!(open_inner.at < close_inner.at);
    assert!(close_inner.at < close_outer.at);
}
