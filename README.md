## pg_ladybug
<p align="center">
  <a href="https://github.com/timescale/pgspot/blob/main/LICENSE"><img alt="License: PostgreSQL" src="https://img.shields.io/github/license/timescale/pgspot"></a>
</p>

Static C code checker for postgres API

pg_ladybug checks C code using the postgres API for problematic patterns. It is implemented as a clang-tidy plugin.

pg_ladybug checks for the following patterns:

- passing large int into Bitmapset
- missing assignment for return value of Bitmapset functions

## PostgresChecker

Uses the Clang Static Analyzer framework to find use-after-ftee bugs for code using the postgres API.

For more information see the bachelor thesis added as a pdf here.

## Installation

```
apt-get install llvm-19 llvm-19-dev clang-19 libclang-19-dev clang-tidy-19
git clone https://github.com/timescale/pg_ladybug
cd pg_ladybug
cmake -S . -B build
make -C build
sudo make -C build install
```

## Requirements

- clang
- clang-tidy
- llvm

### Usage

#### pg_ladybug

Verify checks are present:
```
clang-tidy --load=/usr/local/lib/libPostgresCheck.so --checks='-*,postgres-*' --list-checks
Enabled checks:
    postgres-bitmapset
```

```
% clang-tidy --load /usr/local/lib/libPostgresCheck.so --checks='-*,postgres-*' file.c
2 warnings and 2 errors generated.
Error while processing file.c.
file.c:224:30: error: potential wrong function argument. bms_add_member called with datatype Oid [postgres-bitmapset-member]
  224 |                 uncompressed_attrs_found = bms_add_member(uncompressed_attrs_found, ladybug_test);
      |                                            ^
file.c:227:30: error: potential wrong function argument. bms_add_member called with datatype Oid [postgres-bitmapset-member]
  227 |                 uncompressed_attrs_found = bms_add_member(uncompressed_attrs_found, ladybug_test);
      |                                            ^
Suppressed 2 warnings (2 in non-user code).
Use -header-filter=.* to display errors from all non-system headers. Use -system-headers to display errors from system headers as well.
```
#### PostgresChecker

Verify:
```
clang-19 -cc1 -load /usr/local/lib/libPostgresChecker.so -analyzer checker-help | grep postgres
```

Usage:
```
clang-19 --analyze -Xclang -load -Xclang /usr/local/lib/libPostgresChecker.so -Xclang -analyzer-checker=postgres.PostgresChecker file.c
```
