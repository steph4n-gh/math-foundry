"""Empirical Falsification Sieve Package (M2).

Provides two-tier empirical falsification:
- Tier 1: InstanceDatabase (cached extremal instances)
- Tier 2: CEGARSieve & Z3Sieve (SMT constraint synthesis)
- EmpiricalSieveRunner (unified orchestrator)
- CounterexampleCertificate, SieveResult, and Verifier
"""

from __future__ import annotations

from autonomous_math.sieve.cegar import CEGARSieve
from autonomous_math.sieve.certificates import (
    CounterexampleCertificate,
    CounterexampleCertificateVerifier,
    SieveResult,
    build_c5_counterexample_certificate,
)
from autonomous_math.sieve.instance_db import InstanceDatabase
from autonomous_math.sieve.z3_sieve import EmpiricalSieveRunner, Z3Sieve

__all__ = [
    "InstanceDatabase",
    "CEGARSieve",
    "Z3Sieve",
    "EmpiricalSieveRunner",
    "CounterexampleCertificate",
    "CounterexampleCertificateVerifier",
    "SieveResult",
    "build_c5_counterexample_certificate",
]
