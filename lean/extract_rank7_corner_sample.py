"""Export an accepted bilinear leaf that needs mixed weights in [144/256, 145/256]."""

import argparse
from pathlib import Path
import shutil
import subprocess
from tempfile import TemporaryDirectory


def insert(source, anchor, replacement):
    if source.count(anchor) != 1:
        raise ValueError(f"Expected one source anchor: {anchor!r}")
    return source.replace(anchor, replacement)


def instrument(source):
    source = insert(
        source, "enum class Test", "struct SampleComplete {};\n\nenum class Test"
    )
    source = insert(
        source,
        "    unsigned done=0;",
        """    unsigned done=0;
    std::array<std::array<std::array<I64,4>,4>,6> sample{};
    std::array<std::array<Bounds,3>,6> parameters{};""",
    )
    source = insert(
        source,
        "                    if (works) done|=1u<<j;",
        """                    if (works) {
                        done |= 1u << j;
                        parameters[j] = {f, u, w};
                        for (int tail = 0; tail < 4; ++tail) {
                            sample[j][tail] = {
                                m[tail][j][0], m[tail][j][1],
                                m[tail][j+1][0], m[tail][j+1][1]
                            };
                        }
                    }""",
    )
    source = insert(
        source,
        "                if (done==63) return Test::Corners;",
        """                if (done==63) {
                    bool uses_mixed_weights = false;
                    for (const auto &sector : sample) {
                        for (const auto &corner : sector) {
                            const bool first = corner[0] > 0 && corner[2] > 0;
                            const bool second = corner[1] > 0 && corner[3] > 0;
                            uses_mixed_weights |= !first && !second;
                        }
                    }
                    if (!uses_mixed_weights) return Test::Corners;
                    std::cout << "SAMPLE\\n";
                    for (const Bounds &b : box) std::cout << b.lo << ' ' << b.hi << '\\n';
                    for (unsigned sector = 0; sector < 6; ++sector) {
                        for (const Bounds &b : parameters[sector]) {
                            std::cout << b.lo << ' ' << b.hi << ' ';
                        }
                        std::cout << '\\n';
                        for (const auto &corner : sample[sector]) {
                            std::cout << corner[0] << ' ' << corner[1] << ' '
                                      << corner[2] << ' ' << corner[3] << '\\n';
                        }
                    }
                    throw SampleComplete{};
                }""",
    )
    return insert(
        source,
        "    catch (const std::exception& error)",
        "    catch (const fourth_tie::SampleComplete&) { return 0; }\n"
        "    catch (const std::exception& error)",
    )


def extract(compiler):
    project = Path(__file__).resolve().parents[1]
    with TemporaryDirectory(prefix="rank7-corner-sample-") as temp:
        scratch = Path(temp)
        shutil.copy2(project / "verify_rank7_equal_fifth_sixth.cpp", scratch)
        reference = project / "verify_rank7_fourth_tie_bilinear.cpp"
        source = reference.read_text(encoding="utf-8")
        (scratch / "sample.cpp").write_text(instrument(source), encoding="utf-8")
        subprocess.run(
            [compiler, "-std=c++20", "-O3", "sample.cpp", "-o", "sample.exe"],
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
    _, marker, payload = result.stdout.partition("SAMPLE\n")
    if not marker:
        raise ValueError("The C++ traversal did not find a mixed-weight box")
    rows = payload.strip().splitlines()
    values = [tuple(map(int, row.split())) for row in rows]
    if [len(row) for row in values] != [2] * 5 + ([6] + [4] * 4) * 6:
        raise ValueError("Unexpected box, parameter, or corner table shape")
    return values


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cxx", default="g++")
    args = parser.parse_args()
    for row in extract(args.cxx):
        print(" ".join(map(str, row)))


if __name__ == "__main__":
    main()
