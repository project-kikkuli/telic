Adversarial programs from a soundness review of telic. Each file contains at
least one function whose contract is **false** for the real Python/JavaScript
program, built to exploit a specific gap: block scoping, list aliasing,
mutation through calls, shadowed builtins, integrality inference, `or` on
non-booleans, unbound locals, `@mirrors` ignoring exceptions, and so on.
`tests/test_soundness.py` requires that none of those functions is reported
`proved`. Only the helper functions listed there, whose contracts are true,
may be.
