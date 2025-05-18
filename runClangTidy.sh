#!/bin/bash
clang-tidy-19 --load=/usr/local/lib/libPostgresCheck.so --checks='-*,postgres-*' $1
