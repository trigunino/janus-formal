from __future__ import annotations

import argparse

from janus_lab.data import DATA_URLS, ensure_default_data


def main() -> None:
    parser = argparse.ArgumentParser(description="Download public Janus Lab datasets.")
    parser.add_argument("--force", action="store_true", help="overwrite existing files")
    args = parser.parse_args()

    paths = ensure_default_data(force=args.force)
    for key, path in paths.items():
        print(f"{key}: {path} <- {DATA_URLS[key]}")


if __name__ == "__main__":
    main()
