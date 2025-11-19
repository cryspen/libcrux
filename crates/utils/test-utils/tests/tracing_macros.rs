use std::{
    sync::LazyLock,
    thread::sleep,
    time::{Duration, Instant},
};

use libcrux_test_utils::tracing::{trace_span, EventType, MutexTrace, Trace as _, TraceEvent};

mod str_labels {

    use super::*;

    static TRACE_STR: LazyLock<MutexTrace<&'static str, Instant>> =
        LazyLock::new(|| MutexTrace::default());

    #[trace_span("maybe_slow", TRACE_STR)]
    fn maybe_slow_str() {
        sleep(Duration::from_millis(10));
    }

    #[test]
    fn test_tracing_str() {
        maybe_slow_str();

        let [open, close]: [TraceEvent<_, _>; 2] =
            (*TRACE_STR).clone().report().try_into().unwrap();

        assert_eq!(open.ty, EventType::SpanOpen);
        assert_eq!(open.label, "maybe_slow");

        assert_eq!(close.ty, EventType::SpanClose);
        assert_eq!(close.label, "maybe_slow");

        assert!(open.at < close.at);
    }
}

mod enum_labels {
    use super::*;

    #[derive(Clone, Debug, PartialEq, Eq)]
    enum Label {
        MaybeSlow,
    }

    static TRACE_ENUM: LazyLock<MutexTrace<Label, Instant>> =
        LazyLock::new(|| MutexTrace::default());

    #[trace_span(Label::MaybeSlow, TRACE_ENUM)]
    fn maybe_slow_enum() {
        sleep(Duration::from_millis(10));
    }

    #[test]
    fn test_tracing_enum() {
        maybe_slow_enum();

        let [open, close]: [TraceEvent<_, _>; 2] =
            (*TRACE_ENUM).clone().report().try_into().unwrap();

        assert_eq!(open.ty, EventType::SpanOpen);
        assert_eq!(open.label, Label::MaybeSlow);

        assert_eq!(close.ty, EventType::SpanClose);
        assert_eq!(close.label, Label::MaybeSlow);

        assert!(open.at < close.at);
    }
}
