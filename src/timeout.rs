use std::time::{Duration, Instant};
use std::{
    fmt,
    future::Future,
    pin::Pin,
    task::{Context, Poll, Waker},
};

#[derive(Default)]
pub struct PendingOnce {
    polled: bool,
}

impl Future for PendingOnce {
    type Output = ();

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
        if self.polled {
            Poll::Ready(())
        } else {
            self.polled = true;
            cx.waker().wake_by_ref();
            Poll::Pending
        }
    }
}

/// Pending once to check the timeout
pub fn pending_once() -> PendingOnce {
    PendingOnce::default()
}

pub fn call_with_timeout<T>(
    timelimit: Duration,
    f: impl Future<Output = T>,
) -> Result<T, TimeoutError> {
    let start = Instant::now();
    let mut boxed = Box::pin(f);
    let mut cx = Context::from_waker(Waker::noop());

    loop {
        match boxed.as_mut().poll(&mut cx) {
            Poll::Ready(result) => return Ok(result),
            Poll::Pending => {
                let elapsed = start.elapsed();
                if elapsed > timelimit {
                    return Err(TimeoutError { elapsed });
                }
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TimeoutError {
    elapsed: Duration,
}

impl fmt::Display for TimeoutError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Timeout after {:?}", self.elapsed)
    }
}

impl std::error::Error for TimeoutError {}
