#!/usr/bin/env python3
"""Serve generated review artifacts without allowing stale browser caches."""

from __future__ import annotations

import argparse
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer


class NoCacheHandler(SimpleHTTPRequestHandler):
    def end_headers(self) -> None:
        self.send_header("Cache-Control", "no-store")
        super().end_headers()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--bind", default="0.0.0.0")
    parser.add_argument("--directory", required=True)
    parser.add_argument("port", type=int)
    arguments = parser.parse_args()
    handler = lambda *args, **kwargs: NoCacheHandler(  # noqa: E731
        *args, directory=arguments.directory, **kwargs
    )
    with ThreadingHTTPServer((arguments.bind, arguments.port), handler) as server:
        print(f"Serving {arguments.directory} on {arguments.bind}:{arguments.port}")
        try:
            server.serve_forever()
        except KeyboardInterrupt:
            pass


if __name__ == "__main__":
    main()
