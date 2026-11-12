# Security policy

## Reporting a vulnerability

Report vulnerabilities privately through GitHub:
[Report a vulnerability](https://github.com/OpenJML/OpenJML/security/advisories/new)
(the **Security** tab of this repository). Please do not open a public issue.

You will receive an acknowledgment within 14 days. Fixes are made in the next release, and its release
notes identify the vulnerability fixed.

## Scope

OpenJML runs locally, on source code and specifications the user chooses. A vulnerability is, for example,
a way for crafted input (Java/JML source, `.jml` specification files, LSP messages) to execute code, read or
write files beyond what the user asked for, or exhaust resources outside OpenJML itself; or a weakness in
the runtime library (`jmlruntime.jar`) that is linked into programs compiled with `--rac`.

An unsound verification result (OpenJML reporting that a property holds when it does not) is a serious
bug but not a vulnerability; report it as an ordinary [issue](https://github.com/OpenJML/OpenJML/issues).

Only the latest release is supported.
