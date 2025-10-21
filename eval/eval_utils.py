import subprocess
import requests
import time

PROTO_REPOS = [
    ("googleapis", "googleapis"),
    ("googleapis", "google-cloud-go"),
    ("colinmarc", "hdfs"),
    ("protocolbuffers", "protobuf"),
    ("protocolbuffers", "protobuf-go"),
    ("google", "protobuf.dart"),
    ("bufbuild", "buf"),
    ("go-kratos", "kratos"),
    ("cloudwego", "kitex"),
    ("twitchtv", "twirp"),
    ("asynkron", "protoactor-go"),
    ("samchon", "typia"),
    ("uber", "prototool"),
    ("streamdal", "plumber"),
    ("google", "rejoiner"),
]


def locate_pollux() -> str:
    """
    Locates the pollux binary on the system.

    Returns:
        str: Path to the pollux binary, or empty string if not found.
    """
    try:
        w = subprocess.run(
            ["which", "pollux"],
            check=True,
            capture_output=True,
            text=True,
        )
        return w.stdout.strip()
    except subprocess.CalledProcessError as e:
        print(f"Error finding pollux binary: {e}")

    return ""


def paginated_github_query(
    url: str, headers: dict[str, str], per_page: int = 100
) -> list[dict[str, str]]:
    """
    Generic function to handle paginated GitHub API queries.
    Limited to 1000 total results by GitHub Search API.

    Args:
        url: Base URL for the GitHub API endpoint.
        headers: Headers to include in the request.
        per_page: Number of items to fetch per page.

    Returns:
        List of all items from all pages (max 1000 items).
    """
    page = 1

    paginated_url = f"{url}&per_page={per_page}&page={page}"
    response = requests.get(paginated_url, headers=headers)
    response.raise_for_status()
    all_items = [response.json()]

    while "next" in response.links:
        page += 1
        time.sleep(6)  # Sleep to avoid rate limiting of 10 requests per minute

        paginated_url = f"{url}&per_page={per_page}&page={page}"
        response = requests.get(paginated_url, headers=headers)
        response.raise_for_status()
        items = response.json()

        all_items.append(items)

    return all_items
