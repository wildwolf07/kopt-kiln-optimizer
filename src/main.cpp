// main.cpp - the kopt command line.
//
//   kopt IN.kir --machine MACHINE.cfg [--profile PROFILE.prof] -o OUT.kir
//
// Developer modes (not used by the judges):
//   kopt --sim PROG.kir --machine M.cfg [--input FILE.in]       run + count cycles
//   kopt --check ORIG.kir OPT.kir --machine M.cfg [--input FILE.in] [--random N]
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <sstream>
#include <string>

#include "kir.h"
#include "optimizer.h"
#include "sim.h"

using namespace kopt;

namespace {

bool readFile(const std::string &path, std::string &out) {
    std::ifstream f(path, std::ios::binary);
    if (!f) return false;
    std::ostringstream ss;
    ss << f.rdbuf();
    out = ss.str();
    return true;
}

bool writeFile(const std::string &path, const std::string &data) {
    std::ofstream f(path, std::ios::binary | std::ios::trunc);
    if (!f) return false;
    f << data;
    return static_cast<bool>(f);
}

[[noreturn]] void die(const std::string &msg) {
    fprintf(stderr, "kopt: %s\n", msg.c_str());
    exit(2);
}

bool parseLit32(const std::string &tok, uint32_t &v) {
    char *end = nullptr;
    const char *s = tok.c_str();
    bool neg = (*s == '-');
    if (neg) s++;
    long long n = (s[0] == '0' && s[1] == 'x') ? strtoll(s + 2, &end, 16) : strtoll(s, &end, 10);
    if (!end || *end) return false;
    if (neg) n = -n;
    v = static_cast<uint32_t>(n);
    return true;
}

// Parse an .in file (args / mem / vin lines, '#' comments).
bool parseInput(const std::string &text, Input &in, std::string &err) {
    std::istringstream ss(text);
    std::string line;
    while (std::getline(ss, line)) {
        size_t h = line.find('#');
        if (h != std::string::npos) line.resize(h);
        std::istringstream ls(line);
        std::string kw;
        if (!(ls >> kw)) continue;
        std::vector<uint32_t> vals;
        std::string tok;
        while (ls >> tok) {
            uint32_t v;
            if (!parseLit32(tok, v)) { err = "bad number '" + tok + "'"; return false; }
            vals.push_back(v);
        }
        if (kw == "args") in.args = vals;
        else if (kw == "mem" && vals.size() >= 2) in.segments.push_back({vals[0], std::vector<uint32_t>(vals.begin() + 1, vals.end())});
        else if (kw == "vin" && vals.size() >= 2) {
            auto &q = in.vin[vals[0]];
            q.insert(q.end(), vals.begin() + 1, vals.end());
        } else { err = "bad input line: " + line; return false; }
    }
    return true;
}

Program loadProgram(const std::string &path) {
    std::string text, err;
    if (!readFile(path, text)) die("cannot read " + path);
    Program p;
    if (!parseProgram(text, p, err)) die(path + ": " + err);
    return p;
}

Machine loadMachine(const std::string &path) {
    std::string text, err;
    if (!readFile(path, text)) die("cannot read " + path);
    Machine m;
    if (!parseMachine(text, m, err)) die(path + ": " + err);
    return m;
}

const char *describe(const RunResult &r) {
    static std::string s;
    if (r.status == Status::RET) s = "RET " + std::to_string(r.value);
    else if (r.status == Status::TIMEOUT) s = "TIMEOUT";
    else if (r.trap == TrapKind::DIV_BY_ZERO) s = "TRAP div_by_zero";
    else if (r.trap == TrapKind::BAD_ADDRESS) s = "TRAP bad_address";
    else s = "TRAP explicit(" + std::to_string(r.value) + ")";
    return s.c_str();
}

int simMode(int argc, char **argv) {
    std::string prog, machine, input;
    for (int i = 2; i < argc; i++) {
        std::string a = argv[i];
        if (a == "--machine" && i + 1 < argc) machine = argv[++i];
        else if (a == "--input" && i + 1 < argc) input = argv[++i];
        else prog = a;
    }
    Program p = loadProgram(prog);
    Machine m = machine.empty() ? Machine() : loadMachine(machine);
    Input in;
    if (!input.empty()) {
        std::string t, err;
        if (!readFile(input, t) || !parseInput(t, in, err)) die("bad input " + input + " " + err);
    }
    in.args.resize(p.params.size(), 0);
    SimProgram sp(p);
    RunResult r = sp.run(in, 5000000, true);
    printf("%s cycles=%llu steps=%llu instrs=%zu regs=%d", describe(r),
           static_cast<unsigned long long>(r.status == Status::TIMEOUT ? 0 : sp.cycles(r.trace, m)),
           static_cast<unsigned long long>(r.steps), sp.size(), sp.numRegs());
    if (r.status != Status::TIMEOUT) {
        SimProgram::Breakdown b = sp.breakdown(r.trace, m);
        printf(" taken=%llu fence=%llu data=%llu slot=%llu spills=%llu icache=%llu",
               (unsigned long long)b.takenJumps, (unsigned long long)b.fenceStall, (unsigned long long)b.dataStall,
               (unsigned long long)b.slotStall, (unsigned long long)b.spillTouches, (unsigned long long)b.icacheMisses);
    }
    printf("\n");
    return 0;
}

int checkMode(int argc, char **argv) {
    std::string orig, opt, machine, input;
    int nrandom = 100;
    for (int i = 2; i < argc; i++) {
        std::string a = argv[i];
        if (a == "--machine" && i + 1 < argc) machine = argv[++i];
        else if (a == "--input" && i + 1 < argc) input = argv[++i];
        else if (a == "--random" && i + 1 < argc) nrandom = atoi(argv[++i]);
        else if (orig.empty()) orig = a;
        else opt = a;
    }
    Program po = loadProgram(orig), pn = loadProgram(opt);
    SimProgram so(po), sn(pn);
    std::vector<Input> inputs;
    if (!input.empty()) {
        Input in;
        std::string t, err;
        if (!readFile(input, t) || !parseInput(t, in, err)) die("bad input " + input);
        inputs.push_back(in);
    }
    auto gen = generateInputs(static_cast<int>(po.params.size()), nrandom, 0x5eed);
    inputs.insert(inputs.end(), gen.begin(), gen.end());
    for (size_t i = 0; i < inputs.size(); i++) {
        RunResult a = so.run(inputs[i], 200000, false);
        if (a.status == Status::TIMEOUT) continue;
        RunResult b = sn.run(inputs[i], 20 * a.steps + 1000, false);
        std::string d = compareRuns(a, b);
        if (!d.empty()) {
            printf("MISMATCH input %zu: %s (orig %s", i, d.c_str(), describe(a));
            printf(", opt %s)\n", describe(b));
            return 1;
        }
    }
    printf("OK %zu inputs\n", inputs.size());
    return 0;
}

}  // namespace

int main(int argc, char **argv) {
    if (argc >= 2 && std::string(argv[1]) == "--sim") return simMode(argc, argv);
    if (argc >= 2 && std::string(argv[1]) == "--check") return checkMode(argc, argv);

    std::string in, out, machine, profile;
    for (int i = 1; i < argc; i++) {
        std::string a = argv[i];
        if (a == "--machine" && i + 1 < argc) machine = argv[++i];
        else if (a == "--profile" && i + 1 < argc) profile = argv[++i];
        else if (a == "-o" && i + 1 < argc) out = argv[++i];
        else if (in.empty() && !a.empty() && a[0] != '-') in = a;
        else die("unexpected argument '" + a + "'");
    }
    if (in.empty() || out.empty() || machine.empty())
        die("usage: kopt IN.kir --machine MACHINE.cfg [--profile PROFILE.prof] -o OUT.kir");

    std::string inText;
    if (!readFile(in, inText)) die("cannot read " + in);
    Program prog;
    std::string err;
    if (!parseProgram(inText, prog, err)) die(in + ": " + err);
    Machine m = loadMachine(machine);
    std::string profText;
    if (!profile.empty() && !readFile(profile, profText)) profText.clear();  // a bad profile is only a hint

    Options opt;
    opt.verbose = getenv("KOPT_VERBOSE") != nullptr;
    opt.strict = getenv("KOPT_STRICT") != nullptr;
    std::string result = optimizeProgram(inText, prog, m, profText, opt);
    if (!writeFile(out, result)) die("cannot write " + out);
    return 0;
}
