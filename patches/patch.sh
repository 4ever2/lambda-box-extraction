#!/usr/bin/env bash

patch -p1 -N --silent --dry-run < patches/int.patch 2>/dev/null
if [ $? -eq 0 ]; then
  patch -p1 < patches/int.patch
fi
