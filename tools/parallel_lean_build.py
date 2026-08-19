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
import threading


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


def module_source(source_root: Path, module: str) -> Path:
    return source_root.joinpath(*module.split(".")).with_suffix(".lean")


def manifest_dependencies(
    source: Path,
    modules: dict[str, tuple[Path, Path, tuple[str, ...]]],
    source_root: Path | None,
) -> set[str]:
    dependencies: set[str] = set()
    pending = list(direct_imports(source))
    visited: set[str] = set()
    while pending:
        imported = pending.pop()
        if imported in visited:
            continue
        visited.add(imported)
        if imported in modules:
            dependencies.add(imported)
            continue
        if source_root is None:
            continue
        imported_source = module_source(source_root, imported)
        if imported_source.is_file():
            pending.extend(direct_imports(imported_source))
    return dependencies


def compile_module(
    lean: str,
    module: str,
    spec: tuple[Path, Path, tuple[str, ...]],
    log_dir: Path,
    stop: threading.Event,
) -> tuple[str, str]:
    source, output, options = spec
    output.parent.mkdir(parents=True, exist_ok=True)
    command = [lean, *options, "-o", str(output), str(source)]
    process = subprocess.Popen(
        command, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT
    )
    while True:
        if stop.is_set():
            process.terminate()
            log, _ = process.communicate()
            raise RuntimeError(f"{module} canceled after another module failed\n{log}")
        try:
            log, _ = process.communicate(timeout=0.05)
            break
        except subprocess.TimeoutExpired:
            continue
    (log_dir / f"{module}.log").write_text(log)
    if process.returncode != 0:
        raise RuntimeError(f"{module} failed with exit code {process.returncode}\n{log}")
    return module, log


def build(
    manifest: Path, jobs: int, lean: str, log_dir: Path, source_root: Path | None = None
) -> None:
    modules = read_manifest(manifest)
    log_dir.mkdir(parents=True, exist_ok=True)
    dependencies = {
        module: manifest_dependencies(spec[0], modules, source_root)
        for module, spec in modules.items()
    }
    pending = set(modules)
    completed: set[str] = set()
    running: dict[concurrent.futures.Future[tuple[str, str]], str] = {}
    stop = threading.Event()

    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as executor:
        while pending or running:
            ready = sorted(
                module for module in pending if dependencies[module].issubset(completed)
            )
            while ready and len(running) < jobs:
                module = ready.pop(0)
                pending.remove(module)
                future = executor.submit(
                    compile_module, lean, module, modules[module], log_dir, stop
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
                    stop.set()
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
    parser.add_argument("--source-root", type=Path)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    try:
        build(args.manifest, args.jobs, args.lean, args.log_dir, args.source_root)
    except (OSError, ValueError, RuntimeError) as error:
        print(error, file=sys.stderr)
        raise SystemExit(1) from error


if __name__ == "__main__":
    main()
