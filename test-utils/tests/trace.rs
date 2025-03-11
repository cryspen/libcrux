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

    let run_time = close.at - open.at;
    assert!(run_time.as_micros() > 2500);
    assert!(run_time.as_micros() < 3500);
}

#[test]
fn test_mutex_trace_report() {
    test_trace_report(&MutexTrace::default());
}
#[test]
fn test_refcell_trace_report() {
    test_trace_report(&RefCellTrace::default());
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

    let run_time = close.at - open.at;
    assert!(run_time.as_micros() > 2500);
    assert!(run_time.as_micros() < 3500);
}
