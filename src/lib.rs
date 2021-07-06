// Copyright 2020 Quentin De Coninck
//
// Distributed under MIT license.
//! A minimal crate to play with Instant based on UNIX epoch.
//!
//! The standard library provides Instant and Duration structures to measure
//! elapsed time. This is fine for most use cases, but the Instant structure
//! voluntary hides its implementation to keep its semantics. This crate exposes
//! its time base to the UNIX Epoch (1st January 1970 at 0:00).
//!
//! The exposed API tries to mimic as much as possible the `std::time` one for
//! the related `Instant` structures, such that passing from these to the ones
//! of this crate would be as seamless as possible (as it actually uses
//! `std::time` under the hood).
//!
//! This crate should only be used to compute local time. It is thus not
//! appropriate for timezone computations, playing with dates,...

use std::time::SystemTime;
use std::time::Duration;
use std::ops::{Add, AddAssign, Sub, SubAssign};
use std::fmt;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

#[cfg(feature = "rkyv")]
use rkyv::{Archive, Deserialize as RkyvDeserialize, Serialize as RkyvSerialize};

/// An precise instant relative to the UNIX epoch, with nanosecond precision.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "rkyv", derive(Archive, RkyvDeserialize, RkyvSerialize))]
pub struct Instant {
    secs: u64,
    nanos: u32,
}

impl Instant {
    /// Creates an `Instant` at the specified seconds and nanoseconds after the
    /// UNIX epoch.
    ///
    /// # Examples
    ///
    /// ```
    /// use unix_time::Instant;
    ///
    /// let instant = Instant::at(42, 182870024);
    /// assert_eq!(format!("{:?}", instant), "Instant { secs: 42, nanos: 182870024 }");
    /// ```
    pub fn at(secs: u64, nanos: u32) -> Self {
        Self { secs, nanos }
    }

    /// Returns an instant corresponding to "now".
    pub fn now() -> Self {
        let since_epoch = SystemTime::now()
            .duration_since(SystemTime::UNIX_EPOCH)
            .expect("SystemTime before UNIX epoch?!?");
        Self::at(since_epoch.as_secs(), since_epoch.subsec_nanos())
    }

    /// Returns the number of _whole_ seconds that spaces `self` from the UNIX
    /// epoch.
    ///
    /// The returned value does not include the fractional (nanosecond) part of
    /// the duration, which can be obtained using [`subsec_nanos`].
    ///
    /// # Examples
    ///
    /// ```
    /// use unix_time::Instant;
    ///
    /// let duration = Instant::at(5, 730023852);
    /// assert_eq!(duration.secs(), 5);
    /// ```
    ///
    /// To determine the total number of seconds represented by the `Duration`,
    /// use `secs` in combination with [`subsec_nanos`]:
    ///
    /// ```
    /// use unix_time::Instant;
    ///
    /// let instant = Instant::at(5, 730023852);
    ///
    /// assert_eq!(5.730023852,
    ///            instant.secs() as f64
    ///            + instant.subsec_nanos() as f64 * 1e-9);
    /// ```
    ///
    /// [`subsec_nanos`]: Instant::subsec_nanos
    pub fn secs(&self) -> u64 {
        self.secs
    }

    /// Returns the fractional part that spaces `self` from the UNIX epoch in
    /// nanoseconds.
    ///
    /// This method does _not_ return the total duration since the UNIX epoch in
    /// nanoseconds. The returned number always represents a fractional portion
    /// of a second (i.e., it is less than one billion).
    ///
    /// # Examples
    ///
    /// ```
    /// use unix_time::Instant;
    ///
    /// let instant = Instant::at(5, 10_000_000);
    /// assert_eq!(instant.secs(), 5);
    /// assert_eq!(instant.subsec_nanos(), 10_000_000);
    /// ```
    pub fn subsec_nanos(&self) -> u32 {
        self.nanos
    }

    /// Returns `Some(t)` where `t` is the time `self + duration` if `t` can be
    /// represented as `Instant` (which means it's inside the bounds of the
    /// underlying data structure), `None` otherwise.
    pub fn checked_add(&self, duration: Duration) -> Option<Instant> {
        let d: Duration = (*self).into();
        d.checked_add(duration).map(|x| x.into())
    }

    /// Returns `Some(t)` where `t` is the time `self - duration` if `t` can be
    /// represented as `Instant` (which means it's inside the bounds of the
    /// underlying data structure), `None` otherwise.
    pub fn checked_sub(&self, duration: Duration) -> Option<Instant> {
        let d: Duration = (*self).into();
        d.checked_sub(duration).map(|x| x.into())
    }

    /// Returns the amount of time elapsed from another instant to this one,
    /// or None if that instant is later than this one.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use unix_time::Instant;
    /// use std::time::Duration;
    /// use std::thread::sleep;
    ///
    /// let now = Instant::now();
    /// sleep(Duration::new(1, 0));
    /// let new_now = Instant::now();
    /// println!("{:?}", new_now.checked_duration_since(now));
    /// println!("{:?}", now.checked_duration_since(new_now)); // None
    /// ```
    pub fn checked_duration_since(&self, earlier: Instant) -> Option<Duration> {
        let d: Duration = (*self).into();
        d.checked_sub(earlier.into())
    }

    /// Returns the amount of time elapsed from another instant to this one.
    ///
    /// # Panics
    ///
    /// This function will panic if `earlier` is later than `self`.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::time::Duration;
    /// use unix_time::Instant;
    /// use std::thread::sleep;
    ///
    /// let now = Instant::now();
    /// sleep(Duration::new(1, 0).into());
    /// let new_now = Instant::now();
    /// println!("{:?}", new_now.duration_since(now));
    /// ```
    pub fn duration_since(&self, earlier: Instant) -> Duration {
        self.checked_duration_since(earlier).expect("supplied instant is later than self")
    }

    /// Returns the amount of time elapsed from another instant to this one,
    /// or zero duration if that instant is later than this one.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::time::Duration;
    /// use unix_time::Instant;
    /// use std::thread::sleep;
    ///
    /// let now = Instant::now();
    /// sleep(Duration::new(1, 0));
    /// let new_now = Instant::now();
    /// println!("{:?}", new_now.saturating_duration_since(now));
    /// println!("{:?}", now.saturating_duration_since(new_now)); // 0ns
    /// ```
    pub fn saturating_duration_since(&self, earlier: Instant) -> Duration {
        self.checked_duration_since(earlier).unwrap_or(Duration::new(0, 0))
    }

    /// Returns the amount of time elapsed since this instant was created.
    ///
    /// # Panics
    ///
    /// This function may panic if the current time is earlier than this
    /// instant, which is something that can happen if an `Instant` is
    /// produced synthetically.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::thread::sleep;
    /// use std::time::Duration;
    /// use unix_time::Instant;
    ///
    /// let instant = Instant::now();
    /// let three_secs = Duration::from_secs(3);
    /// sleep(three_secs);
    /// assert!(instant.elapsed() >= three_secs);
    /// ```
    pub fn elapsed(&self) -> Duration {
        Instant::now() - *self
    }
}

impl From<Instant> for Duration {
    fn from(i: Instant) -> Duration {
        Duration::new(i.secs, i.nanos)
    }
}

impl From<Duration> for Instant {
    fn from(d: Duration) -> Instant {
        Instant::at(d.as_secs(), d.subsec_nanos())
    }
}

impl Add<Duration> for Instant {
    type Output = Instant;

    /// # Panics
    ///
    /// This function may panic if the resulting point in time cannot be represented by the
    /// underlying data structure. See [`Instant::checked_add`] for a version without panic.
    fn add(self, other: Duration) -> Instant {
        self.checked_add(other).expect("overflow when adding duration to instant")
    }
}

impl AddAssign<Duration> for Instant {
    fn add_assign(&mut self, other: Duration) {
        *self = *self + other;
    }
}

impl Sub<Duration> for Instant {
    type Output = Instant;

    fn sub(self, other: Duration) -> Instant {
        self.checked_sub(other).expect("overflow when subtracting duration from instant")
    }
}

impl SubAssign<Duration> for Instant {
    fn sub_assign(&mut self, other: Duration) {
        *self = *self - other;
    }
}

impl Sub<Instant> for Instant {
    type Output = Duration;

    fn sub(self, other: Instant) -> Duration {
        self.duration_since(other)
    }
}

impl fmt::Debug for Instant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Instant {{ secs: {}, nanos: {} }}", self.secs, self.nanos)
    }
}