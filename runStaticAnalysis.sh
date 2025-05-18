#!/bin/bash
clang-19 --analyze -Xclang -load -Xclang /usr/local/lib/libPostgresChecker.so -Xclang -analyzer-checker=postgres.PostgresChecker $1
