//! Wilson 95% confidence intervals (NFR-1115).
//!
//! Uses the score-interval formula directly, *not* the
//! Agresti–Coull approximation, per `NFR-1115`. The off-by-`1/2`
//! discrepancy from Agresti–Coull would invalidate cross-platform
//! replication (`TEST-1193`).

/// `z` at 95% (two-sided): `1.959963984540054`.
const Z_95: f64 = 1.959_963_984_540_054;

/// Wilson score interval for a binomial proportion at 95% confidence.
///
/// Returns `(lower, upper)`. For `trials == 0`, returns `(0.0, 1.0)`
/// (the maximally uninformative interval).
///
/// Numerical stability: bounded to `[0.0, 1.0]` after the formula
/// is applied, so floating-point underflow at extreme rates does
/// not yield negative or super-unit bounds.
pub fn wilson_ci(successes: u64, trials: u64) -> (f64, f64) {
    if trials == 0 {
        return (0.0, 1.0);
    }
    let n = trials as f64;
    let p = successes as f64 / n;
    let z = Z_95;
    let z2 = z * z;
    let denom = 1.0 + z2 / n;
    let centre = (p + z2 / (2.0 * n)) / denom;
    let half = (z / denom) * ((p * (1.0 - p) / n + z2 / (4.0 * n * n)).sqrt());
    let lower = (centre - half).max(0.0);
    let upper = (centre + half).min(1.0);
    (lower, upper)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn approx(a: f64, b: f64, eps: f64) -> bool {
        (a - b).abs() < eps
    }

    /// `NFR-1115` corner: `(n=10, p=0.5)` should give a wide interval
    /// around `0.5` with the score formula. Reference values from
    /// the score-interval formula directly (NOT Agresti–Coull).
    #[test]
    fn wilson_ci_n10_p0_5() {
        let (lo, hi) = wilson_ci(5, 10);
        assert!(approx(lo, 0.236_593_090_5, 1e-9), "lo = {lo}");
        assert!(approx(hi, 0.763_406_909_5, 1e-9), "hi = {hi}");
        // Symmetry property: at p = 0.5 the interval is symmetric about 0.5.
        assert!(approx(lo + hi, 1.0, 1e-12), "lo + hi = {}", lo + hi);
    }

    /// `NFR-1115` corner: `(n=1000, p=0.43)` — the calibration target
    /// in `REQ-1150`.
    #[test]
    fn wilson_ci_n1000_p0_43() {
        let (lo, hi) = wilson_ci(430, 1000);
        assert!(approx(lo, 0.399_640_919_9, 1e-9), "lo = {lo}");
        assert!(approx(hi, 0.460_894_826_3, 1e-9), "hi = {hi}");
    }

    #[test]
    fn wilson_ci_extremes() {
        let (lo, hi) = wilson_ci(0, 100);
        assert!(lo >= 0.0);
        assert!(hi > 0.0 && hi < 0.05);
        let (lo, hi) = wilson_ci(100, 100);
        assert!(lo > 0.95 && lo <= 1.0);
        assert!(hi <= 1.0);
        let (lo, hi) = wilson_ci(0, 0);
        assert_eq!((lo, hi), (0.0, 1.0));
    }

    #[test]
    fn wilson_ci_bounded() {
        for t in [10u64, 100, 1000] {
            for s in 0..=t {
                let (lo, hi) = wilson_ci(s, t);
                assert!((0.0..=1.0).contains(&lo), "lo={lo} s={s} t={t}");
                assert!((0.0..=1.0).contains(&hi), "hi={hi} s={s} t={t}");
                assert!(lo <= hi, "lo={lo} hi={hi} s={s} t={t}");
            }
        }
    }
}
