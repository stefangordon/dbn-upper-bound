"""Fast packaging checks; no numerical or Lean calculation is repeated."""
import importlib.util
from pathlib import Path
import re
import tempfile
import unittest
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]


def module(name, relative):
    spec = importlib.util.spec_from_file_location(name, ROOT / relative)
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


manifest = module("release_test_manifest", "scripts/manifest.py")
paper = module("release_test_paper", "scripts/build_paper.py")


def markdown_links(text):
    # Exclude verbatim commands and display mathematics: products such as
    # [f(x)-f(y)](x-y) are mathematics rather than Markdown links.
    text = re.sub(r"(?ms)^(`{3,}|~{3,})[^\n]*\n.*?^\1[ \t]*$", "", text)
    text = re.sub(r"\$\$.*?\$\$", "", text, flags=re.S)
    return re.findall(r"(?<!!)\[[^\]\n]+\]\(([^\s)]+)\)", text)


class ReleaseContentsTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.names = manifest.release_files()

    def test_relative_documentation_links_resolve_inside_release(self):
        problems = []
        released = set(self.names)
        for name in self.names:
            if not name.endswith(".md"):
                continue
            path = ROOT / name
            for target in markdown_links(path.read_text()):
                parsed = urlsplit(target.strip("<>"))
                if parsed.scheme or parsed.netloc or not parsed.path:
                    continue
                resolved = (path.parent / unquote(parsed.path)).resolve()
                if not resolved.is_relative_to(ROOT):
                    problems.append((name, target, "escapes repository"))
                    continue
                relative = resolved.relative_to(ROOT).as_posix()
                if not resolved.is_file() or (relative not in released and relative != "MANIFEST.json"):
                    problems.append((name, target, "missing release file"))
        self.assertEqual(problems, [])

    def test_no_private_machine_paths_in_released_text(self):
        pattern = re.compile(r"(?:/home/|/Users/|/jobs/|/root/)[A-Za-z0-9_.-]+/")
        problems = []
        for name in self.names:
            if name.endswith(".pdf"):
                continue
            if pattern.search((ROOT / name).read_text()):
                problems.append(name)
        self.assertEqual(problems, [])

    def test_required_workflows_and_sources_are_in_inventory(self):
        expected = {
            ".github/workflows/verify.yml", ".github/workflows/lean.yml", "Dockerfile",
            ".github/workflows/pages.yml", "docs/index.html",
            "verify.py", "requirements.txt", "lean/Audit.lean", "lean/lake-manifest.json",
            "manuscript/main.md", "manuscript/analytic-estimates.md",
            "manuscript/computational-estimates.md", "manuscript/source-boxes.md",
            "manuscript/references.md", "manuscript/preamble.tex",
            "certificate/data/barriers.json", "certificate/data/old-M3a-wall.json",
            "support/head/data/matrix.txt", "support/head/generate-matrix.c",
            "support/source/boxes.json", "support/fields/data/boundary-geometry.json",
        }
        self.assertTrue(expected.issubset(self.names), expected - set(self.names))

    def test_printed_source_table_matches_exact_catalog(self):
        self.assertEqual((ROOT / "manuscript/source-boxes.md").read_text(), paper.source_table())

    def test_browser_and_download_links_are_distinct(self):
        links = markdown_links((ROOT / "README.md").read_text())
        browser = "https://stefangordon.github.io/dbn-upper-bound/dbn-upper-bound.pdf"
        download = "https://github.com/stefangordon/dbn-upper-bound/releases/latest/download/dbn-upper-bound.pdf"
        self.assertIn(browser, links)
        self.assertIn(download, links)
        self.assertLess(links.index(browser), links.index(download))

    def test_pages_entrypoint_targets_the_canonical_pdf(self):
        entry = (ROOT / "docs/index.html").read_text()
        target = "dbn-upper-bound.pdf"
        self.assertTrue((ROOT / "output/pdf" / target).is_file())
        self.assertIn('content="0; url=' + target + '"', entry)
        self.assertEqual(set(re.findall(r'href="([^"]+)"', entry)), {target})


class InventoryBoundaryTests(unittest.TestCase):
    def test_build_and_environment_caches_are_excluded(self):
        with tempfile.TemporaryDirectory(prefix="dbn-release-test-") as directory:
            root = Path(directory)
            for excluded in [".git", ".lake", ".venv", ".ruff_cache", "__pycache__", "build"]:
                path = root / excluded / "unreleased.json"
                path.parent.mkdir()
                path.write_text("{}")
            (root / "README.md").write_text("Release fixture\n")
            workflow = root / ".github/workflows/check.yml"
            workflow.parent.mkdir(parents=True)
            workflow.write_text("name: check\n")
            self.assertEqual(manifest.release_files(root), [".github/workflows/check.yml", "README.md"])

    def test_symlinks_cannot_import_external_contents(self):
        with tempfile.TemporaryDirectory(prefix="dbn-release-test-") as directory:
            root = Path(directory)
            (root / "real.md").write_text("Fixture\n")
            (root / "linked.md").symlink_to(root / "real.md")
            with self.assertRaisesRegex(ValueError, "not symlinks"):
                manifest.release_files(root)

    def test_unclassified_payloads_are_rejected(self):
        with tempfile.TemporaryDirectory(prefix="dbn-release-test-") as directory:
            root = Path(directory)
            (root / "unexpected.bin").write_bytes(b"fixture")
            with self.assertRaisesRegex(ValueError, "unclassified release file"):
                manifest.release_files(root)


if __name__ == "__main__":
    unittest.main()
