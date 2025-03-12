use std::{
    thread::sleep,
    time::{Duration, Instant},
};

use libcrux_test_utils::tracing::{EventType, MutexTrace, Trace as _, TraceEvent};

mod str_labels {

    use super::*;

    lazy_static::lazy_static! {
        static ref TRACE_STR: MutexTrace<&'static str, Instant> = Default::default();
    }

    #[libcrux_macros::trace_span("maybe_slow", TRACE_STR)]
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

        let run_time = close.at - open.at;
        assert!(run_time.as_micros() > 9300);
        assert!(run_time.as_micros() < 10700);
    }
}

mod enum_labels {
    use super::*;

    #[derive(Clone, Debug, PartialEq, Eq)]
    enum Label {
        MaybeSlow,
    }

    lazy_static::lazy_static! {
        static ref TRACE_ENUM: MutexTrace<Label, Instant> = Default::default();
    }

    #[libcrux_macros::trace_span(Label::MaybeSlow, TRACE_ENUM)]
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

        let run_time = close.at - open.at;
        assert!(run_time.as_micros() > 9300);
        assert!(run_time.as_micros() < 10700);
    }
}
