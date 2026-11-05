#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
"""Replay the primary Gohberg–Krupnik interval coverage with explicit evidence logs.

Version 0.20 — release maintainer — 20261028 07:23 ET. Keep local compute policy in the outer launcher so the mathematical runner remains portable.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
Original programs are immutable. A replay includes cheap tests before coverage.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys


def timestamp():
    return datetime.now(timezone.utc).isoformat()


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def release_metadata(value, field=None):
    """Use documented release aliases when metadata is first serialized."""
    if field == "argv":
        return ["python", *value[1:]]
    if field == "executable":
        return "python"
    if field == "module_paths":
        return {name: "python-environment/" + name for name in value}
    if isinstance(value, dict):
        return {key: release_metadata(item, key) for key, item in value.items()}
    if isinstance(value, list):
        return [release_metadata(item, field) for item in value]
    if isinstance(value, str):
        root = str(Path(__file__).resolve().parent)
        if field == "cwd":
            return "."
        if field in ("stdout", "stderr"):
            path = Path(value)
            if path.is_relative_to(root):
                return str(path.relative_to(root))
            return "run-output/" + path.name
        value = value.replace(root, ".").replace(str(Path(sys.prefix)), "python-environment")
        if "/home/" in value or "/tmp/" in value:
            raise ValueError("An unsupported absolute metadata path was refused")
        return value
    return value


def write_json(path, value):
    path.write_text(json.dumps(release_metadata(value), indent=2) + "\n", encoding="utf-8")


def check_file(root, entry, path_key):
    path = (root / entry[path_key]).resolve()
    if not path.is_relative_to(root.resolve()):
        raise ValueError(f"Manifest path escapes packet: {path}")
    data = path.read_bytes()
    if (len(data) != entry["bytes"]
            or hashlib.sha256(data).hexdigest() != entry["sha256"]
            or hashlib.md5(data).hexdigest() != entry["md5"]):
        raise ValueError(f"Manifest mismatch: {path}")
    return {"file": entry[path_key], "sha256": entry["sha256"]}


def verify_manifests(root):
    files = []
    for filename, path_key in (("MANIFEST.json", "file"),
                               ("SUPPLEMENTAL_MANIFEST.json", "path")):
        manifest = json.loads((root / filename).read_text())
        files.extend(check_file(root, entry, path_key) for entry in manifest["files"])
    if len({entry["file"] for entry in files}) != len(files):
        raise ValueError("Duplicate frozen file paths in manifests")
    return files


def child_environment(dependencies):
    environment = os.environ.copy()
    for name in ("PYTHONPATH", "PYTHONHOME", "PYTHONOPTIMIZE"):
        environment.pop(name, None)
    environment.update(dependencies["thread_environment"])
    environment.update(PYTHONNOUSERSITE="1", PYTHONUNBUFFERED="1")
    return environment


def environment_record(interpreter, environment):
    source = (
        "import sys,json,flint,numpy,scipy,mpmath,importlib.metadata as md; "
        "print(json.dumps({'versions': {'python':sys.version.split()[0],"
        "'python-flint':flint.__version__,'FLINT':flint.__FLINT_VERSION__,"
        "**{name:md.version(name) for name in ('mpmath','numpy','scipy')}},"
        "'executable':sys.executable,'assertions_enabled':__debug__,"
        "'module_paths':{name:module.__file__ for name,module in "
        "(('flint',flint),('numpy',numpy),('scipy',scipy),('mpmath',mpmath))}}))"
    )
    result = subprocess.run([interpreter, "-u", "-B", "-c", source],
                            env=environment, capture_output=True, text=True, check=True)
    return json.loads(result.stdout)


def validate_result(returncode, stdout, stderr, markers):
    if returncode != 0:
        raise ValueError(f"Child exited {returncode}")
    if re.search(r"NOT [Pp][Rr][Oo][Vv][Ee][Dd]|PROVED \(BAD\)|ACCEPTED \(BAD\)|"
                 r"controls BAD|UNEXPECTED|FAILED cell|Traceback", stdout + stderr):
        raise ValueError("Unexpected failure or bad-control marker")
    for marker in markers:
        if re.search(marker, stdout, re.MULTILINE) is None:
            raise ValueError(f"Missing required success/control marker: {marker}")


def job(name, script, arguments, markers):
    return {"name": name, "script": script, "arguments": arguments, "markers": markers}


def cheap_jobs():
    return [
        job("wide_chord_controls", "certify_wide_chord.py", ["--test"],
            [r"Both false-claim controls rejected\."]),
        job("wide_chord_witnesses", "certify_wide_chord.py", ["--verify"],
            [r'"both_strict_bounds_certified": true', r'"precision_bits": 160']),
        job("negative_omega_test", "programs/omega_negative.py",
            ["--test"], [r"^tests passed$"]),
        job("boundary_bulk_test", "programs/boundary_bulk.py",
            ["--test"], [r"^tests done$"]),
        job("boundary_sliver_test", "programs/boundary_sliver.py",
            ["--test"], [r"^tests passed$"]),
        job("strip_corner_test", "programs/strip_corner.py",
            ["--mode", "test"], [r"TEST Et0 = closed form: True;", r"vanish .*: True;",
                                 r"at 3 points: True"]),
        job("strip_bulk_test", "programs/strip_bulk.py",
            ["--test"], [r"^tests passed$"]),
    ]


def coverage_jobs():
    jobs = [
        job("negative_omega", "programs/omega_negative.py", [],
            [r"CLAIM Gamma < 0 on \[1\.001, 1\.2336025\]: PROVED",
             r"CONTROL Gamma .*: refused \(good\)"]),
        job("positive_omega_root", "programs/omega_positive.py", [],
            [r"CLAIM Omega' > 0 .*: PROVED", r"CLAIM Omega > 0 .*: PROVED",
             r"CONTROL 1 .*: refused \(good\)", r"CONTROL 2 .*: refused \(good\)",
             r"^RESULT: both claims PROVED, controls refused$"]),
        job("local_threshold_root", "programs/local_threshold.py", [],
            [r"unique simple root p_c in \[9480393/7812500, 242698061/200000000\]",
             r"^LEMMA P_c: PROVED$"]),
    ]
    for index, (lower, upper) in enumerate((("1.000001", "1.00001"),
                                           ("1.00001", "1.0001"),
                                           ("1.0001", "1.2134")), start=1):
        arguments = ["--p-lo", lower, "--p-hi", upper, "--cells", "100", "--max-depth", "24"]
        marker = rf"^\(ii\) on p in \[{re.escape(lower)}, {re.escape(upper)}\].*: PROVED h"
        jobs.append(job(f"boundary_bulk_{index}", "programs/boundary_bulk.py",
                        arguments, [marker]))
    jobs.extend([
        job("boundary_sliver", "programs/boundary_sliver.py", [],
            [r"CLAIM g < 0 .*: PROVED", r"CLAIM 1 - lam_loc.*: PROVED",
             r"CONTROL s = 1/50 .*: refused \(good\)",
             r"CONTROL p in .*: refused \(good\)"]),
        job("corner_control_c1", "programs/strip_corner.py",
            ["--mode", "control_c1", "--max-depth", "24"],
            [r"CONTROL control_c1: .* -> REFUSED \(good\)"]),
        job("corner_control_c2", "programs/strip_corner.py",
            ["--mode", "control_c2", "--max-depth", "24"],
            [r"CONTROL control_c2: .* -> REFUSED \(good\)"]),
        job("strip_corner", "programs/strip_corner.py",
            ["--mode", "certify", "--max-depth", "24"],
            [r"^EDGES \(certified lower ends\):", r"^MIDDLE: .*'refused': 0",
             r"^CORNER CLAIM: PROVED$"]),
        job("strip_bulk_main", "programs/strip_bulk.py",
            ["--corner", "main", "--max-boxes", "3000000"],
            [r"^REGION A .*s-tails PROVED .*middle .* PROVED",
             r"^REGION B .*s-tails PROVED .*middle .* PROVED",
             r"CONTROL 1 .*: refused \(good\)", r"CONTROL 2 .*: refused \(good\)",
             r"^CLAIM g > 0 .*corner 'main'.*: PROVED; controls good$"]),
    ])
    return jobs


def runner_self_test(interpreter, environment):
    validate_result(0, "CONTROL: refused (good)\n", "", [r"refused \(good\)"])
    rejected = 0
    for code, output, markers in ((1, "PROVED", ["PROVED"]),
                                   (0, "", ["PROVED"]),
                                   (0, "PROVED (BAD)", ["PROVED"])):
        try:
            validate_result(code, output, "", markers)
        except ValueError:
            rejected += 1
    result = subprocess.run([interpreter, "-c", "import sys; print('PROVED'); sys.exit(7)"],
                            env=environment, capture_output=True, text=True)
    try:
        validate_result(result.returncode, result.stdout, result.stderr, ["PROVED"])
    except ValueError:
        rejected += 1
    if rejected != 4:
        raise AssertionError("Runner accepted a failed child or missing/bad marker")
    return {"false_success_cases_rejected": rejected, "expected_control_refusal_accepted": True}


def execute_job(root, output, interpreter, environment, specification):
    metadata_path = output / f"{specification['name']}.json"
    stdout_path = output / f"{specification['name']}.stdout.log"
    stderr_path = output / f"{specification['name']}.stderr.log"
    command = [interpreter, "-u", "-B", specification["script"], *specification["arguments"]]
    record = dict(specification, argv=command, cwd=str(root), started=timestamp(), status="RUNNING")
    write_json(metadata_path, record)
    print(f"START {specification['name']}", flush=True)
    try:
        with stdout_path.open("w") as stdout, stderr_path.open("w") as stderr:
            result = subprocess.run(command, cwd=root, env=environment, stdout=stdout, stderr=stderr)
        record["returncode"] = result.returncode
        validate_result(result.returncode, stdout_path.read_text(), stderr_path.read_text(), specification["markers"])
        record["status"] = "PASS"
    except Exception as error:
        record.update(status="FAILED", error=str(error))
        raise
    finally:
        record.update(ended=timestamp(), stdout=str(stdout_path), stderr=str(stderr_path))
        write_json(metadata_path, record)
    print(f"PASS {specification['name']}", flush=True)
    return record


def execute_run(arguments):
    root = Path(__file__).resolve().parent
    output = Path(arguments.output_dir).absolute()
    output.mkdir(parents=True, exist_ok=False)
    summary = {"version": "0.20", "project": "gohberg-krupnik-2003-sharpness", "started": timestamp(), "status": "RUNNING",
               "mode": "replay" if arguments.replay else "test", "jobs": [], "runner_sha256": digest(Path(__file__))}
    summary_path = output / "SUMMARY.json"
    write_json(summary_path, summary)
    try:
        dependencies = json.loads((root / "REPLAY_DEPENDENCIES.json").read_text())
        environment = child_environment(dependencies)
        observed = environment_record(str(Path(arguments.python).absolute()), environment)
        summary["environment"] = observed
        if observed["versions"] != dependencies["versions"] or not observed["assertions_enabled"]:
            raise ValueError("Interpreter dependency versions or assertion setting differ from the pinned record")
        summary["frozen_files"] = verify_manifests(root)
        summary["support_hashes"] = {name: digest(root / name) for name in
                                    ("MANIFEST.json", "SUPPLEMENTAL_MANIFEST.json",
                                     "REPLAY_DEPENDENCIES.json", "certify_wide_chord.py")}
        summary["thread_environment"] = dependencies["thread_environment"]
        summary["analytic_inputs"] = dependencies["analytic_inputs"]
        summary["runner_tests"] = runner_self_test(observed["executable"], environment)
        for specification in cheap_jobs() + (coverage_jobs() if arguments.replay else []):
            verify_manifests(root)
            summary["jobs"].append(execute_job(root, output, observed["executable"], environment, specification))
            verify_manifests(root)
            if any(digest(root / name) != checksum for name, checksum in summary["support_hashes"].items()):
                raise ValueError("A support input changed during the run")
            write_json(summary_path, summary)
        summary["status"] = "PASS"
        summary["primary_coverage_complete"] = bool(arguments.replay)
        print(f"{summary['mode'].upper()} PASS: {summary_path}", flush=True)
        return 0
    except Exception as error:
        summary.update(status="FAILED", error=str(error), primary_coverage_complete=False)
        print(f"FAILED: {error}; evidence: {summary_path}", file=sys.stderr, flush=True)
        return 1
    finally:
        summary["ended"] = timestamp()
        write_json(summary_path, summary)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--test", action="store_true")
    mode.add_argument("--replay", action="store_true")
    parser.add_argument("--python", required=True, help="Explicit interpreter with the pinned dependencies")
    parser.add_argument("--output-dir", required=True, help="New directory; existing paths are refused")
    return execute_run(parser.parse_args())


if __name__ == "__main__":
    sys.exit(main())
