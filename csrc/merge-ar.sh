#!/usr/bin/env bash
# NOTE: not POSIX-sh; uses bash associative arrays.
# Merges several static archives into one, preserving every member even when
# basenames collide (Lean module paths flatten to the same basename, so
# `ar x` silently loses members). Usage: merge-ar.sh out.a in1.a [in2.a ...]
set -euo pipefail
out=$1; shift
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
members=$work/m
mkdir -p "$members"
n=0
for archive in "$@"; do
    tag=$(basename "$archive" | tr -c 'A-Za-z0-9' '_')
    tag=${tag%.a}
    if ar t "$archive" > "$work/list.txt" 2>/dev/null && [ -s "$work/list.txt" ]; then
        # Archives may contain many members sharing one basename (Lean module
        # paths flatten). Use ar's N modifier (x only) to address each.
        declare -A seen=()
        mkdir -p "$work/x"
        while IFS= read -r m; do
            key="$m"
            local_i=${seen[$key]:-0}
            seen[$key]=$((local_i + 1))
            (cd "$work/x" && ar xN $((local_i + 1)) "$archive" "$m")
            mv "$work/x/$m" "$members/${tag}_${n}.o"
            n=$((n + 1))
        done < "$work/list.txt"
    else
        # plain object file, not an archive
        cp "$archive" "$members/${tag}_${n}.o"
        n=$((n + 1))
    fi
done
rm -f "$out"
ar rcs "$out" "$members"/*.o
echo "merged $n members into $out"
