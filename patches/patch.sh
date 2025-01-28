#!/usr/bin/env bash

patch -p0 -N --silent --dry-run < patches/int.patch 2>/dev/null
if [ $? -eq 0 ]; then
  patch -p0 < patches/int.patch
fi
