#!/usr/bin/env bash
set -euo pipefail

ROOT="${1:-.}"
ROOT="${ROOT%/}"

echo 'digraph agda_dependencies {'
echo '  rankdir=LR;'
echo '  node [shape=box];'

# ----------------------------------------------------------------------
# Discover modules
# ----------------------------------------------------------------------

declare -A modules
declare -A files

while IFS= read -r -d '' file; do
    rel="${file#"$ROOT"/}"
    module="${rel%.agda}"
    module="${module//\//.}"

    modules["$module"]=1
    files["$module"]="$file"
done < <(find "$ROOT" -type f -name '*.agda' -print0)

# ----------------------------------------------------------------------
# DOT helpers
# ----------------------------------------------------------------------

# Turn an arbitrary directory path into a safe DOT identifier.
cluster_id() {
    local path="$1"
    printf '%s' "$path" |
        sed 's/[^A-Za-z0-9_]/_/g'
}

# Escape a string for use as a DOT quoted string.
dot_escape() {
    printf '%s' "$1" |
        sed 's/\\/\\\\/g; s/"/\\"/g'
}

# ----------------------------------------------------------------------
# Build the directory tree
# ----------------------------------------------------------------------

declare -A dirs
dirs["."]=1

for module in "${!modules[@]}"; do
    file="${files[$module]}"
    rel="${file#"$ROOT"/}"

    dir="${rel%/*}"

    if [[ "$dir" == "$rel" ]]; then
        dir="."
    fi

    # Add every parent directory.
    while [[ "$dir" != "." ]]; do
        dirs["$dir"]=1
        dir="${dir%/*}"

        [[ "$dir" == */* ]] || dir="."
    done
done

# Return the immediate child directories of a directory.
child_dirs() {
    local parent="$1"
    local dir

    for dir in "${!dirs[@]}"; do
        [[ "$dir" == "$parent" ]] && continue

        if [[ "$parent" == "." ]]; then
            if [[ "$dir" != */* ]]; then
                printf '%s\n' "$dir"
            fi
        else
            if [[ "$dir" == "$parent/"* ]]; then
                local rest="${dir#"$parent"/}"

                if [[ "$rest" != */* ]]; then
                    printf '%s\n' "$dir"
                fi
            fi
        fi
    done | sort
}

# ----------------------------------------------------------------------
# Emit a directory cluster recursively
# ----------------------------------------------------------------------

emit_cluster() {
    local dir="$1"
    local indent="$2"

    local id
    id=$(cluster_id "$dir")

    if [[ "$dir" == "." ]]; then
        echo "${indent}subgraph cluster_root {"
        echo "${indent}  label=\"$(dot_escape "$ROOT")\";"
    else
        local label="${dir##*/}"

        echo "${indent}subgraph cluster_$id {"
        echo "${indent}  label=\"$(dot_escape "$label")\";"
    fi

    # Files directly in this directory.
    for module in "${!modules[@]}"; do
        local file="${files[$module]}"
        local rel="${file#"$ROOT"/}"
        local module_dir="${rel%/*}"

        [[ "$module_dir" == "$rel" ]] && module_dir="."

        [[ "$module_dir" == "$dir" ]] || continue

        local name="${rel##*/}"
        name="${name%.agda}"

        printf '%s  "%s" [label="%s"];\n' \
            "$indent" \
            "$module" \
            "$(dot_escape "$name")"
    done

    # Nested directories.
    while IFS= read -r child; do
        [[ -n "$child" ]] || continue
        emit_cluster "$child" "$indent  "
    done < <(child_dirs "$dir")

    echo "${indent}}"
}

emit_cluster "." "  "

# ----------------------------------------------------------------------
# Emit dependency edges
# ----------------------------------------------------------------------

for module in "${!modules[@]}"; do
    file="${files[$module]}"

    sed 's/--.*//' "$file" |
    sed -nE \
        's/^[[:space:]]*(open[[:space:]]+)?import[[:space:]]+([A-Za-z_][A-Za-z0-9_.]*).*/\2/p' |
    while IFS= read -r imported; do

        # Only local BorrowedCF modules.
        if [[ "$imported" == "BorrowedCF" || "$imported" == BorrowedCF.* ]]; then

            # Only emit edges to modules we actually discovered.
            if [[ -n "${modules[$imported]+x}" ]]; then
                printf '  "%s" -> "%s";\n' "$module" "$imported"
            fi

        fi
    done
done

echo '}'
