"""Extract one sample per upper traversal branch and a two-child subtree."""

import argparse
from pathlib import Path
import shutil
import subprocess
from tempfile import TemporaryDirectory

from extract_rank7_corner_sample import insert


def instrument(source):
    source = insert(
        source, "enum class Test", "struct ReplaySampleComplete {};\n\nenum class Test"
    )
    source = insert(
        source,
        "        if ((payment-debit).lo>0) return Test::Weighted;",
        r"""        const Bounds margin = payment-debit;
        if (margin.lo > 0) {
            static bool emitted_weighted_margin = false;
            if (!emitted_weighted_margin) {
                std::cout << "WEIGHTED " << u.lo << ' ' << u.hi << ' '
                          << margin.lo << ' ' << margin.hi << '\n';
                emitted_weighted_margin = true;
            }
            return Test::Weighted;
        }""",
    )
    source = insert(
        source,
        "        std::vector<Node> pending{{initial,0}};",
        r"""        std::vector<Node> pending{{initial,0}};
        std::array<bool,5> sampled{};
        std::optional<Node> candidate;
        int child_leaves = 0;
        bool subtree_found = false;
        const auto print_box = [](const TailBox& box) {
            for (const Bounds& b : box) std::cout << ' ' << b.lo << ' ' << b.hi;
        };""",
    )
    source = insert(
        source,
        "            if (result!=Test::Unknown) {",
        r"""            const auto category = contracted ? static_cast<unsigned>(result) : 4;
            const bool fresh = !std::exchange(sampled[category], true);
            if (fresh) {
                std::cout << "NODE " << category << ' ' << node.depth;
                print_box(node.box);
                if (contracted) print_box(*contracted);
                std::cout << '\n';
            }
            if (result != Test::Unknown && candidate && node.depth == candidate->depth + 1) {
                if (++child_leaves == 2 && !subtree_found) {
                    std::cout << "SUBTREE " << candidate->depth;
                    print_box(candidate->box);
                    std::cout << '\n';
                    subtree_found = true;
                }
            }
            if (subtree_found && std::all_of(sampled.begin(), sampled.end(), [](bool v) { return v; }))
                throw ReplaySampleComplete{};
            if (result!=Test::Unknown) {""",
    )
    source = insert(
        source,
        "            const Bounds z=(*contracted)[axis];",
        r"""            if (fresh) std::cout << "AXIS " << axis << '\n';
            if (!subtree_found) {
                candidate = node;
                child_leaves = 0;
            }
            const Bounds z=(*contracted)[axis];""",
    )
    source = insert(
        source,
        "    catch (const std::exception& error)",
        "    catch (const fourth_tie::ReplaySampleComplete&) { return 0; }\n"
        "    catch (const std::exception& error)",
    )
    return "#include <utility>\n" + source


def extract(compiler):
    project = Path(__file__).resolve().parents[1]
    with TemporaryDirectory(prefix="rank7-upper-replay-") as temp:
        scratch = Path(temp)
        shutil.copy2(project / "verify_rank7_equal_fifth_sixth.cpp", scratch)
        source = (project / "verify_rank7_fourth_tie_bilinear.cpp").read_text(encoding="utf-8")
        (scratch / "sample.cpp").write_text(instrument(source), encoding="utf-8")
        subprocess.run(
            [compiler, "-std=c++20", "-O3", "-Wall", "-Wextra", "sample.cpp", "-o", "sample.exe"],
            cwd=scratch,
            check=True,
        )
        result = subprocess.run(
            [str(scratch / "sample.exe"), "144", "145", "256"],
            cwd=scratch,
            check=True,
            capture_output=True,
            text=True,
        )
    lines = [row for row in result.stdout.splitlines() if row.startswith(("NODE ", "AXIS ", "WEIGHTED ", "SUBTREE "))]
    nodes = {int(row.split()[1]) for row in lines if row.startswith("NODE ")}
    if nodes != set(range(5)) or len(lines) != 8:
        raise ValueError("Expected each branch, a split axis, a weighted margin, and a full subtree")
    return lines


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cxx", default="g++")
    options = parser.parse_args()
    print("\n".join(extract(options.cxx)))


if __name__ == "__main__":
    main()

