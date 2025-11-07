# Loads data from a directory of parquet files 
# 
# Reads all parquet files in a directory and 
# concatenates them together. 
#
# Files should all have the same schema.
export def "pollux-nu load-data" [dir: string] {
    let files = glob ./($dir | path basename)/*.parquet
    let df = $files 
    | reduce --fold (polars open ($files | first)) {|file, acc|
        $acc | polars concat (polars open $file)
    }
    $df
}

def json-top-n [n=20: int, api=false: bool] {
    if $api {
        polars with-column ((polars col owner) + "/" + (polars col repo) | polars as NAME) 
        | polars select NAME
    } else {
        polars get repository
    }
    | polars value-counts 
    | polars sort-by count -r [true]
    | polars first $n
}

# Reports top N repositories by number of files with JSON tags 
#
# Dataframe schema should one of these sets of schema:
# 1. - owner 
#    - repo
# 2. - repository
# 
# Dataframe is piped in, i.e. $df | pollux-nu json top-n 20
export def "pollux-nu json top-n" [
    n=20: int # Number of repos to truncate at
    --api (-a) # If present, use owner/repo columns else use repository column
] {
    json-top-n $n $api
    | polars collect
}

# Reports the total number of files with GO JSON tags in the top N repositories
#
# Dataframe schema should one of these sets of schema:
# 1. - owner 
#    - repo
# 2. - repository
# 
# Dataframe is piped in, i.e. $df | pollux-nu json count-files-top-n 20
export def "pollux-nu json count-files-top-n" [
    n = 20: int # Number of repos to truncate at
    --api (-a) # If present, use owner/repo columns else use repository column
] {
    json-top-n $n $api
    | polars sum 
    | polars get count
    | polars collect
}

# Reports the total number of repos in the dataframe 
# 
# Dataframe schema should one of these sets of schema:
# 1. - owner 
#    - repo
# 2. - repository
#
# Dataframe is piped in, i.e. $df | pollux-nu json count-repos
export def "pollux-nu json count-repos" [
    --api (-a) # If present, use owner/repo columns else use repository column
] {
    if $api {
        polars with-column ((polars col owner) + "/" + (polars col repo) | polars as NAME) 
        | polars select NAME
    } else {
        polars get repository
    }
    | polars unique 
    | polars select (polars len)
    | polars collect
}

export def pollux-nu [] {}
