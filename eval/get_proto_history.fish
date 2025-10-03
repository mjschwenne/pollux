#!/usr/bin/env fish

# Set the repository owner and name
set -l owner "mjschwenne"
set -l repo "grackle"

# Step 1: Search for .proto files and extract their paths
set -l proto_files (gh search code --repo=$owner/$repo "extension:proto" --json=path --jq '.[].path')

# Step 2: For each .proto file, fetch its commit history
for file in $proto_files
    echo "Commit history for $file:"
    gh api -H "Accept: application/vnd.github.v3+json" "/repos/$owner/$repo/commits?path=$file" --jq '.[].sha'
    echo "---"
end
