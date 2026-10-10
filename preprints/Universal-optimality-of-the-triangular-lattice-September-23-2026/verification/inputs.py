"""Strict integrity binding for the public triangular-energy certificate.

The manifest binds a reviewed source release; it does not authenticate authorship
or prove that the mathematical formulas agree with the numerical programs.
"""
import argparse
from contextlib import contextmanager
import hashlib
import importlib
import importlib.metadata
import json
import platform
import re
import stat
from pathlib import Path

ARTICLE_IDENTIFIER = "Universal-optimality-of-the-triangular-lattice-September-23-2026"
SCHEMA = "triangular-energy-certificate-inputs-v1"
SEMANTICS = "integrity-only; numerical formulas are encoded in the checked programs"
FORMULA_PATHS = (
    "build/main.tex", "build/macros.tex", "build/references.bib",
    "build/sections/01-uniform-gaussian-theorem.tex",
    "build/sections/02-cardinal-fourier.tex",
    "build/sections/03-quadrature-finite-data.tex",
    "build/sections/04-exact-interpolation.tex",
    "build/sections/05-global-signs.tex",
    "build/sections/06-gaussian-energy-transfer.tex",
    "build/sections/07-shifted-mixtures.tex",
    "build/sections/08-renormalized-jellium.tex",
    "build/sections/08-arithmetic-verification.tex",
    "build/sections/09-conditional-floor-verification.tex",
)
CHECKER_PATHS = (
    "verification/arithmetic_bounds.py", "verification/inputs.py",
    "verification/numeric_balls.py", "verification/requirements.txt",
)
EXPECTED_COUNTS = {"bernstein": 37310, "tail": 10}
PYTHON_FLINT_VERSION = "0.9.0"
MAX_MANIFEST_BYTES = 65536
MAX_ANCHOR_BYTES = 16 * 1024 * 1024
ARTICLE_ROOT = Path(__file__).absolute().parents[1]
DEFAULT_MANIFEST = ARTICLE_ROOT / "verification/CERTIFICATE-INPUTS.json"


class IntegrityError(ValueError):
    """A source binding or runtime requirement was not satisfied."""


def _keys(value, expected, label):
    if type(value) is not dict or set(value) != set(expected):
        raise IntegrityError(f"{label}: expected exactly the documented fields")


def _object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise IntegrityError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _constant(value):
    raise IntegrityError(f"non-finite JSON constant: {value}")


def _regular_path(path):
    """Require a regular file and no symlink in its lexical ancestor chain."""
    path = Path(path).expanduser().absolute()
    if ".." in path.parts:
        raise IntegrityError("parent traversal is not permitted in an input path")
    chain = list(reversed(path.parents)) + [path]
    for component in chain:
        try:
            mode = component.lstat().st_mode
        except OSError as error:
            raise IntegrityError(f"cannot inspect input component: {error}") from error
        if stat.S_ISLNK(mode):
            raise IntegrityError("symlinked input files or ancestors are not permitted")
        if component != path and not stat.S_ISDIR(mode):
            raise IntegrityError("an input ancestor is not a directory")
    if not stat.S_ISREG(mode):
        raise IntegrityError("input must be a regular file")
    return path


def _read(path, maximum):
    path = _regular_path(path)
    try:
        with path.open("rb") as stream:
            data = stream.read(maximum + 1)
    except OSError as error:
        raise IntegrityError(f"cannot read input: {error}") from error
    if len(data) > maximum:
        raise IntegrityError("input exceeds its documented size limit")
    return data


def _records(records, expected, root, label):
    if type(records) is not list or len(records) != len(expected):
        raise IntegrityError(f"{label}: wrong anchor count")
    seen = set()
    for record in records:
        _keys(record, ("path", "bytes", "sha256"), label)
        name = record["path"]
        if (type(name) is not str or not name or name.startswith("/")
                or "\\" in name or any(p in ("", ".", "..") for p in name.split("/"))):
            raise IntegrityError(f"{label}: anchor path is not normalized relative POSIX")
        if name not in expected or name in seen:
            raise IntegrityError(f"{label}: duplicate or unexpected anchor path")
        seen.add(name)
        size, digest = record["bytes"], record["sha256"]
        if type(size) is not int or not 0 < size <= MAX_ANCHOR_BYTES:
            raise IntegrityError(f"{label}: bytes must be a positive bounded integer")
        if type(digest) is not str or re.fullmatch(r"[0-9a-f]{64}", digest) is None:
            raise IntegrityError(f"{label}: sha256 must be 64 lowercase hexadecimal digits")
        data = _read(root / name, MAX_ANCHOR_BYTES)
        if len(data) != size or hashlib.sha256(data).hexdigest() != digest:
            raise IntegrityError(f"source integrity mismatch: {name}")
    if seen != set(expected):
        raise IntegrityError(f"{label}: incomplete anchor set")
    return sorted(records, key=lambda record: record["path"])


def validate_inputs(manifest_path=None):
    """Validate exact anchors under the root fixed by this helper's location."""
    path = DEFAULT_MANIFEST if manifest_path is None else Path(manifest_path)
    raw = _read(path, MAX_MANIFEST_BYTES)
    try:
        manifest = json.loads(raw.decode("utf-8"), object_pairs_hook=_object,
                              parse_constant=_constant)
    except IntegrityError:
        raise
    except (UnicodeError, ValueError, RecursionError) as error:
        raise IntegrityError(f"invalid bounded UTF-8 JSON manifest: {error}") from error
    _keys(manifest, ("schema", "article_identifier", "formula_sources",
                     "checker_sources", "expected_counts", "formula_binding_semantics"),
          "manifest")
    if manifest["schema"] != SCHEMA or manifest["article_identifier"] != ARTICLE_IDENTIFIER:
        raise IntegrityError("manifest schema or article identifier mismatch")
    if manifest["formula_binding_semantics"] != SEMANTICS:
        raise IntegrityError("manifest formula-binding semantics mismatch")
    counts = manifest["expected_counts"]
    _keys(counts, EXPECTED_COUNTS, "expected_counts")
    if any(type(counts[key]) is not int or counts[key] != value
           for key, value in EXPECTED_COUNTS.items()):
        raise IntegrityError("expected comparison counts mismatch")
    formulas = _records(manifest["formula_sources"], FORMULA_PATHS, ARTICLE_ROOT,
                        "formula_sources")
    checkers = _records(manifest["checker_sources"], CHECKER_PATHS, ARTICLE_ROOT,
                        "checker_sources")
    absolute = path.expanduser().absolute()
    try:
        input_name = absolute.relative_to(ARTICLE_ROOT).as_posix()
    except ValueError:
        input_name = None
    return {
        "schema": SCHEMA,
        "article_identifier": ARTICLE_IDENTIFIER,
        "input_path": input_name,
        "input_location": "article-relative" if input_name else "external override",
        "input_sha256": hashlib.sha256(raw).hexdigest(),
        "formula_sources": formulas,
        "checker_sources": checkers,
        "expected_counts": dict(EXPECTED_COUNTS),
        "formula_binding_semantics": SEMANTICS,
    }


def require_python_flint():
    """Check both installed-distribution and imported-library versions."""
    try:
        installed = importlib.metadata.version("python-flint")
    except importlib.metadata.PackageNotFoundError as error:
        raise IntegrityError("install python-flint==0.9.0 from requirements.txt") from error
    if installed != PYTHON_FLINT_VERSION:
        raise IntegrityError(f"python-flint==0.9.0 required; installed version is {installed}")
    try:
        library = importlib.import_module("flint")
    except ImportError as error:
        raise IntegrityError(f"cannot import python-flint: {error}") from error
    actual = getattr(library, "__version__", None)
    if actual != PYTHON_FLINT_VERSION:
        raise IntegrityError(f"python-flint==0.9.0 required; imported version is {actual}")
    return actual


def parse_options(description, argv=None, *, reject_optimized=False):
    parser = argparse.ArgumentParser(description=description)
    parser.add_argument("--input", type=Path, default=DEFAULT_MANIFEST,
                        help="public source-binding manifest (default: %(default)s)")
    parser.add_argument("--output-dir", type=Path,
                        default=ARTICLE_ROOT / "build/verification",
                        help="fresh output directory; existing result files are refused")
    options = parser.parse_args(argv)
    if reject_optimized and not __debug__:
        parser.error("Python optimization disables certificate assertions; rerun without -O or -OO")
    try:
        options.binding = validate_inputs(options.input)
        # Source validation precedes the numerical dependency import and outputs.
        options.python_flint_version = require_python_flint()
    except IntegrityError as error:
        parser.error(str(error))
    return options


def run_metadata(options, program, precision_bits):
    return {
        **options.binding,
        "program_path": f"verification/{program}",
        "verifier_sha256": next(item["sha256"] for item in options.binding["checker_sources"]
                                if item["path"] == f"verification/{program}"),
        "python_version": platform.python_version(),
        "python_implementation": platform.python_implementation(),
        "python_flint_version": options.python_flint_version,
        "precision_bits": precision_bits,
    }


def recheck_inputs(options):
    if validate_inputs(options.input) != options.binding:
        raise IntegrityError("source binding changed during verification; no success record written")


def create_output(options, names):
    """Reserve output files exclusively, refusing symlink ancestors and conflicts.

    Empty reserved JSON files are not certificates. JSON is filled only after all
    checks succeed; a failed run may leave its diagnostic log and empty JSON.
    """
    directory = options.output_dir.expanduser().absolute()
    if ".." in directory.parts:
        raise IntegrityError("parent traversal is not permitted in an output path")
    for component in list(reversed(directory.parents)) + [directory]:
        try:
            mode = component.lstat().st_mode
        except FileNotFoundError:
            continue
        if stat.S_ISLNK(mode) or not stat.S_ISDIR(mode):
            raise IntegrityError("output path must use directories without symlinks")
    directory.mkdir(parents=True, exist_ok=True)
    handles = {}
    try:
        for name in names:
            handles[name] = (directory / name).open("x", encoding="utf-8")
    except Exception:
        for name, handle in handles.items():
            handle.close()
            (directory / name).unlink()
        raise
    return handles


@contextmanager
def managed_output(options, names, result_name):
    """Discard the result JSON if computation, reporting or file closing fails."""
    files = create_output(options, names)
    completed = False
    try:
        yield files
        for stream in files.values():
            stream.close()
        completed = True
    finally:
        for stream in files.values():
            try:
                stream.close()
            except OSError:
                pass
        if not completed:
            Path(files[result_name].name).unlink(missing_ok=True)
