#!/usr/bin/env fish

function __progress_build_info -a total current -d "Build string showing completion info"
    set -l char_diff (math (string length $total) - (string length $current))

    set -l padding
    if test $char_diff -gt 0
        set padding (string repeat -n $char_diff " ")" "
    else
        set padding " "
    end

    echo ":: "$padding" "$current" / "$total" "
end

function print_progress -a total current -d "Print one state of progress bar"
    set -l done_ratio (math $current / $total)

    set -l info_str (__progress_build_info $total $current)

    set -l width (math (tput cols) - (string length $info_str))
    set -l n_done (math "floor("$done_ratio" * "$width")")

    echo -ne $info_str
    echo -ne (string repeat -n $n_done "█")
    echo -ne (string repeat -n (math $width - $n_done) "—")
end

function get_proto_history_json --argument-names owner repo
    # Initialize an empty JSON object
    set -l json_output "{}"

    # Step 1: Search for .proto files and extract their paths
    set -l proto_files (gh search code --repo=$owner/$repo "extension:proto" --limit=1000 --json=path --jq '.[].path')
    set -l nproto (count $proto_files)
    echo "Found $nproto proto files in $owner/$repo"

    # Step 2: For each .proto file, fetch its commit history
    for idx in (seq 1 $nproto)
        set -l file $proto_files[$idx]
        # Fetch commit hashes for the file as a JSON array
        set -l commit_hashes (gh api -H "Accept: application/vnd.github.v3+json" "/repos/$owner/$repo/commits?path=$file" --jq '[.[].sha]')

        # Use jq to escape the file path and build the JSON object
        set json_output (echo "$json_output" | jq --arg file "$file" --argjson hashes "$commit_hashes" '. + {($file): $hashes}')
        print_progress $nproto $idx
        echo -ne '\r'
        sleep 2
    end
    echo -ne "\n\n"

    # Output the JSON
    echo "$json_output" | jq > "$owner-$repo.json"
end

get_proto_history_json $argv[1] $argv[2]
