# Actual modified Bessel product kernel: pending P4

Accepted980/facade153/auditPASS/174 records unchanged. New BesselProductKernel.lean has3 public statements and3 independent literal target types, immutable final shared bundle PASS standard3. Disclosure permission for this exact single source and prompt is requested separately from the three-file full-kernel bundle. Neither permission is inferred from earlier source approvals; no new Qoder request is sent yet.

The proof reuses the already accepted modifiedBesselI_nat_ofReal_eq_realSeries, which derives from the actual complex modifiedBesselI definition. For nonnegative x,lambda, the REAL PART of I_q(2sqrt(x*lambda)) equals sqrt(x)^q sqrt(lambda)^q times the entire positive coefficient series. This includes zero scalar arguments and q=0, with literal0^0 conventions, and does not divide by a potentially zero power.

For matrices, the actual real-part Bessel-product kernel factors into positive row/column powers and the full series kernel. For strictly increasing POSITIVE x and lambda, its determinant is strictly positive, including empty dimension. This is full noncentral-rank kernel positivity. It does not prove partial-rank central-column positivity, candidate normalization or an actual Wishart joint density.

Seed2026102803:104 calibrated scalar/Bessel/matrix controls precede source. Actual first leaf and immutable final leaf/checker all exit0. Final source SHA256:3606812f82d97ea95144bdb7181e9f83b622a4f42dacc097fc605d1081e054ca. Numerical calibration is NOT proof; the formal bridge uses the established scalar series and row/column determinant identities.

[需人工审查] Scalar normalization and real-part convention, root-factor powers, row/column orientation, eventual noncentral density and original-paper mapping. FullLake/Linux independent kernel NOT_RUN. Frozen publications unchanged. User hard stop03:47:51UTC.
