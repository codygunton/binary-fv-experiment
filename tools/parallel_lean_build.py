#!/usr/bin/env python3
"""Compile a fixed Lean module set in dependency order and in parallel."""

from __future__ import annotations

import argparse
import concurrent.futures
import os
from pathlib import Path
import shlex
import subprocess
import sys


def read_manifest(path: Path) -> dict[str, tuple[Path, Path, tuple[str, ...]]]:
    modules: dict[str, tuple[Path, Path, tuple[str, ...]]] = {}
    for line_number, raw_line in enumerate(path.read_text().splitlines(), 1):
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) not in (3, 4):
            raise ValueError(f"{path}:{line_number}: expected 3 or 4 tab-separated fields")
        module, source, output = fields[:3]
        if module in modules:
            raise ValueError(f"{path}:{line_number}: duplicate module {module}")
        options = tuple(shlex.split(fields[3])) if len(fields) == 4 else ()
        modules[module] = (Path(source), Path(output), options)
    return modules


def direct_imports(source: Path) -> set[str]:
    imports: set[str] = set()
    for raw_line in source.read_text().splitlines():
        line = raw_line.strip()
        if line.startswith("import "):
            imports.update(line.removeprefix("import ").split())
    return imports


def compile_module(
    lean: str, module: str, spec: tuple[Path, Path, tuple[str, ...]], log_dir: Path
) -> tuple[str, str]:
    source, output, options = spec
    output.parent.mkdir(parents=True, exist_ok=True)
    command = [lean, *options, "-o", str(output), str(source)]
    completed = subprocess.run(command, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = completed.stdout
    (log_dir / f"{module}.log").write_text(log)
    if completed.returncode != 0:
        raise RuntimeError(f"{module} failed with exit code {completed.returncode}\n{log}")
    return module, log


def build(manifest: Path, jobs: int, lean: str, log_dir: Path) -> None:
    modules = read_manifest(manifest)
    log_dir.mkdir(parents=True, exist_ok=True)
    dependencies = {
        module: direct_imports(spec[0]).intersection(modules)
        for module, spec in modules.items()
    }
    pending = set(modules)
    completed: set[str] = set()
    running: dict[concurrent.futures.Future[tuple[str, str]], str] = {}

    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as executor:
        while pending or running:
            ready = sorted(
                module for module in pending if dependencies[module].issubset(completed)
            )
            while ready and len(running) < jobs:
                module = ready.pop(0)
                pending.remove(module)
                future = executor.submit(
                    compile_module, lean, module, modules[module], log_dir
                )
                running[future] = module

            if not running:
                blocked = ", ".join(
                    f"{module} <- {sorted(dependencies[module] - completed)}"
                    for module in sorted(pending)
                )
                raise RuntimeError(f"dependency cycle or missing completion: {blocked}")

            done, _ = concurrent.futures.wait(
                running, return_when=concurrent.futures.FIRST_COMPLETED
            )
            for future in done:
                module = running.pop(future)
                try:
                    _, log = future.result()
                except Exception:
                    for other in running:
                        other.cancel()
                    raise
                if log:
                    sys.stdout.write(log)
                print(f"compiled {module}", flush=True)
                completed.add(module)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--jobs", type=int, default=os.cpu_count() or 1)
    parser.add_argument("--lean", default="lean")
    parser.add_argument("--log-dir", type=Path, default=Path("lean-build-logs"))
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    try:
        build(args.manifest, args.jobs, args.lean, args.log_dir)
    except (OSError, ValueError, RuntimeError) as error:
        print(error, file=sys.stderr)
        raise SystemExit(1) from error


if __name__ == "__main__":
    main()
