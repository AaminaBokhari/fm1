import { useState, useEffect } from "react";
import { AlertCircle, CheckCircle2, Code2, Terminal, Zap } from "lucide-react";
import SimpleGraph from "./SimpleGraph";
import { generateCFG, parseProgram } from "../../utils/parser";
import { convertToSSA, optimizeSSA } from "../../utils/ssaConverter";
import { 
  generateVerificationSMT, 
  generateEquivalenceSMT,
  checkVerification, 
  checkEquivalence 
} from "../../utils/smtGenerator";
import { formatSSA, formatSMT } from "../../utils/formatter";

export default function ProgramVerification() {
  const [mode, setMode] = useState("verification"); // verification or equivalence
  const [program1, setProgram1] = useState(
    "x := 3;\nif (x < 5) {\n  y := x + 1;\n} else {\n  y := x - 1;\n}\nassert(y > 0);"
  );
  const [program2, setProgram2] = useState("x := 3;\ny := x + 1;\nassert(y > 0);");
  const [unrollDepth, setUnrollDepth] = useState(3);
  const [ssaForm1, setSsaForm1] = useState("");
  const [ssaForm2, setSsaForm2] = useState("");
  const [smtCode, setSmtCode] = useState("");
  const [verificationResult, setVerificationResult] = useState(null);
  const [counterexamples, setCounterexamples] = useState([]);
  const [validExamples, setValidExamples] = useState([]);
  const [optimizedSSA1, setOptimizedSSA1] = useState("");
  const [optimizedSSA2, setOptimizedSSA2] = useState("");
  const [loading, setLoading] = useState(false);
  const [cfgData, setCfgData] = useState(null);
  const [activeTab, setActiveTab] = useState("ssa");

  // Process the program when the analyze button is clicked
  const analyzePrograms = async () => {
    setLoading(true);

    try {
      // Parse the programs
      const ast1 = parseProgram(program1);
      let ast2 = null;
      if (mode === "equivalence") {
        ast2 = parseProgram(program2);
      }

      // Convert to SSA form
      const ssaResult1 = convertToSSA(ast1);
      setSsaForm1(formatSSA(ssaResult1.ssa));
      setOptimizedSSA1(formatSSA(optimizeSSA(ssaResult1.ssa)));

      let ssaResult2 = null;
      if (ast2) {
        ssaResult2 = convertToSSA(ast2);
        setSsaForm2(formatSSA(ssaResult2.ssa));
        setOptimizedSSA2(formatSSA(optimizeSSA(ssaResult2.ssa)));
      }

      // Generate control flow graph data
      setCfgData(generateCFG(ast1));

      // Generate SMT constraints
      const smt =
        mode === "verification"
          ? generateVerificationSMT(ssaResult1.ssa, unrollDepth)
          : generateEquivalenceSMT(ssaResult1.ssa, ssaResult2.ssa, unrollDepth);

      setSmtCode(formatSMT(smt));

      // Run SMT solver
      if (mode === "verification") {
        const result = await checkVerification(smt);
        setVerificationResult(result.verified);
        setCounterexamples(result.counterexamples || []);
        setValidExamples(result.validExamples || []);
      } else {
        const result = await checkEquivalence(smt);
        setVerificationResult(result.equivalent);
        setCounterexamples(result.counterexamples || []);
        setValidExamples(result.validExamples || []);
      }
    } catch (error) {
      setVerificationResult(false);
      setCounterexamples([{ error: error.message }]);
    }

    setLoading(false);
  };

  // Reset results when programs or mode change
  useEffect(() => {
    setSsaForm1("");
    setSsaForm2("");
    setSmtCode("");
    setVerificationResult(null);
    setCounterexamples([]);
    setValidExamples([]);
    setOptimizedSSA1("");
    setOptimizedSSA2("");
    setCfgData(null);
  }, [program1, program2, mode, unrollDepth]);

  return (
    <div className="min-h-screen bg-zinc-950 text-zinc-100">
      {/* Header with enhanced neon effect */}
      <header className="relative overflow-hidden border-b border-emerald-500/30">
        <div className="absolute inset-0 bg-[radial-gradient(circle_at_30%_30%,rgba(16,185,129,0.3),transparent_70%)]"></div>
        <div className="container mx-auto py-10 px-6 relative z-10">
          <div className="flex items-center gap-3">
            <Zap className="h-10 w-10 text-emerald-400 animate-pulse" />
            <h1 className="text-4xl font-bold tracking-tight text-transparent bg-clip-text bg-gradient-to-r from-emerald-400 via-teal-300 to-cyan-400">
              Formal Verification Engine
            </h1>
          </div>
          <p className="mt-3 text-zinc-400 max-w-2xl text-lg">
            Advanced program analysis using static single assignment and SMT solvers
          </p>
        </div>
      </header>

      <main className="container mx-auto py-10 px-6">
        <div className="grid grid-cols-1 xl:grid-cols-12 gap-8">
          {/* Left panel - Input */}
          <div className="xl:col-span-5 space-y-6">
            <div className="bg-zinc-900 rounded-xl border border-zinc-800 overflow-hidden shadow-lg shadow-emerald-900/10">
              <div className="p-5 border-b border-zinc-800 flex justify-between items-center bg-gradient-to-r from-zinc-900 to-zinc-900/70">
                <h2 className="text-xl font-semibold flex items-center gap-2">
                  <Terminal className="h-5 w-5 text-emerald-400" />
                  <span>Program Input</span>
                </h2>
                <div className="flex items-center gap-3">
                  <div className="flex items-center gap-2">
                    <div className="inline-flex h-[24px] w-[44px] shrink-0 cursor-pointer items-center rounded-full border-2 border-transparent transition-colors focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-zinc-950 focus-visible:ring-offset-2 focus-visible:ring-offset-white disabled:cursor-not-allowed disabled:opacity-50 data-[state=checked]:bg-emerald-500 data-[state=unchecked]:bg-zinc-700 relative"
                      onClick={() => setMode(mode === "verification" ? "equivalence" : "verification")}
                    >
                      <span className={`pointer-events-none block h-5 w-5 rounded-full bg-white shadow-lg ring-0 transition-transform ${mode === "equivalence" ? "translate-x-5" : "translate-x-0"}`} />
                    </div>
                    <label className="text-sm text-zinc-400">
                      Equivalence Mode
                    </label>
                  </div>
                </div>
              </div>

              <div className="p-5 space-y-5">
                <div className="space-y-2">
                  <div className="flex justify-between items-center">
                    <label className="text-zinc-400">
                      Loop Unrolling Depth
                    </label>
                    <input
                      type="number"
                      value={unrollDepth}
                      onChange={(e) => setUnrollDepth(parseInt(e.target.value))}
                      min="1"
                      className="w-20 bg-zinc-950 border border-zinc-800 rounded-md p-1 text-center text-zinc-200"
                    />
                  </div>
                </div>

                <div className="space-y-2">
                  <label className="text-zinc-400 flex items-center gap-2">
                    <Code2 className="h-4 w-4 text-emerald-400" />
                    Program 1
                  </label>
                  <textarea
                    value={program1}
                    onChange={(e) => setProgram1(e.target.value)}
                    className="font-mono h-60 resize-none bg-zinc-950 border border-zinc-800 rounded-md p-3 w-full text-emerald-100 placeholder-zinc-600 focus:outline-none focus:ring-1 focus:ring-emerald-500 transition-all duration-200"
                    placeholder="Enter your program here..."
                  />
                </div>

                {mode === "equivalence" && (
                  <div className="space-y-2">
                    <label className="text-zinc-400 flex items-center gap-2">
                      <Code2 className="h-4 w-4 text-amber-400" />
                      Program 2
                    </label>
                    <textarea
                      value={program2}
                      onChange={(e) => setProgram2(e.target.value)}
                      className="font-mono h-60 resize-none bg-zinc-950 border border-zinc-800 rounded-md p-3 w-full text-amber-100 placeholder-zinc-600 focus:outline-none focus:ring-1 focus:ring-amber-500 transition-all duration-200"
                      placeholder="Enter your second program here..."
                    />
                  </div>
                )}

                <button
                  onClick={analyzePrograms}
                  disabled={loading}
                  className="w-full bg-gradient-to-r from-emerald-600 to-emerald-700 hover:from-emerald-500 hover:to-emerald-600 text-white py-3 rounded-md font-medium transition-all duration-200 flex items-center justify-center space-x-2 shadow-md"
                >
                  {loading ? (
                    <>
                      <svg
                        className="animate-spin h-5 w-5 text-white"
                        xmlns="http://www.w3.org/2000/svg"
                        fill="none"
                        viewBox="0 0 24 24"
                      >
                        <circle
                          className="opacity-25"
                          cx="12"
                          cy="12"
                          r="10"
                          stroke="currentColor"
                          strokeWidth="4"
                        ></circle>
                        <path
                          className="opacity-75"
                          fill="currentColor"
                          d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4zm2 5.291A7.962 7.962 0 014 12H0c0 3.042 1.135 5.824 3 7.938l3-2.647z"
                        ></path>
                      </svg>
                      <span>Analyzing...</span>
                    </>
                  ) : (
                    <span>Analyze Program</span>
                  )}
                </button>
              </div>
            </div>

            {/* Verification Results */}
            <div className="bg-zinc-900 rounded-xl border border-zinc-800 overflow-hidden shadow-lg shadow-emerald-900/10 transform transition-all duration-300">
              <div className="p-5 border-b border-zinc-800 bg-gradient-to-r from-zinc-900 to-zinc-900/70">
                <h2 className="text-xl font-semibold flex items-center gap-2">
                  <AlertCircle className="h-5 w-5 text-emerald-400" />
                  <span>Verification Results</span>
                </h2>
              </div>

              <div className="p-5">
                {verificationResult === null ? (
                  <div className="text-center p-8 text-zinc-500 opacity-80">
                    Run the analysis to see results
                  </div>
                ) : (
                  <div className="space-y-4 animate-fadeIn">
                    <div
                      className={`p-5 rounded-lg flex items-start gap-3 transition-all ${
                        verificationResult
                          ? "bg-emerald-950/50 border border-emerald-800/60"
                          : "bg-red-950/50 border border-red-800/60"
                      }`}
                    >
                      {verificationResult ? (
                        <CheckCircle2 className="h-6 w-6 text-emerald-400 mt-0.5" />
                      ) : (
                        <AlertCircle className="h-6 w-6 text-red-400 mt-0.5" />
                      )}
                      <div>
                        <h3 className="font-medium text-lg">
                          {mode === "verification"
                            ? verificationResult
                              ? "All assertions verified"
                              : "Verification failed"
                            : verificationResult
                              ? "Programs are equivalent"
                              : "Programs are not equivalent"}
                        </h3>
                        <p className="text-zinc-400 mt-1">
                          {verificationResult
                            ? "The formal verification was successful."
                            : "The verification found potential issues."}
                        </p>
                      </div>
                    </div>

                    {validExamples.length > 0 && (
                      <div className="space-y-2">
                        <h3 className="text-lg font-medium flex items-center gap-2">
                          <span className="inline-flex items-center rounded-md bg-emerald-900/80 px-2 py-1 text-xs font-medium text-emerald-100">
                            Valid Examples
                          </span>
                        </h3>
                        <div className="bg-zinc-950 rounded-lg p-3 overflow-auto max-h-40 border border-zinc-800">
                          {validExamples.map((example, idx) => (
                            <div key={idx} className="mb-2 p-2 border-b border-zinc-800 last:border-0">
                              <div className="text-xs text-zinc-500 mb-1">Example {idx + 1}</div>
                              <ul className="space-y-1">
                                {Object.entries(example).map(([key, value]) => (
                                  <li key={key} className="text-sm flex">
                                    <span className="font-mono text-emerald-400 mr-2">{key}</span>
                                    <span className="text-zinc-300">=</span>
                                    <span className="font-mono text-amber-300 ml-2">{value}</span>
                                  </li>
                                ))}
                              </ul>
                            </div>
                          ))}
                        </div>
                      </div>
                    )}

                    {counterexamples.length > 0 && (
                      <div className="space-y-2">
                        <h3 className="text-lg font-medium flex items-center gap-2">
                          <span className="inline-flex items-center rounded-md bg-red-900/80 px-2 py-1 text-xs font-medium text-red-100">
                            Counterexamples
                          </span>
                        </h3>
                        <div className="bg-zinc-950 rounded-lg p-3 overflow-auto max-h-40 border border-zinc-800">
                          {counterexamples.map((example, idx) => (
                            <div key={idx} className="mb-2 p-2 border-b border-zinc-800 last:border-0">
                              <div className="text-xs text-zinc-500 mb-1">Counterexample {idx + 1}</div>
                              <ul className="space-y-1">
                                {Object.entries(example).map(([key, value]) => (
                                  <li key={key} className="text-sm flex">
                                    <span className="font-mono text-red-400 mr-2">{key}</span>
                                    <span className="text-zinc-300">=</span>
                                    <span className="font-mono text-amber-300 ml-2">{value}</span>
                                  </li>
                                ))}
                              </ul>
                            </div>
                          ))}
                        </div>
                      </div>
                    )}
                  </div>
                )}
              </div>
            </div>
          </div>

          {/* Right panel - Analysis */}
          <div className="xl:col-span-7 space-y-6">
            <div className="bg-zinc-900 rounded-xl border border-zinc-800 overflow-hidden shadow-lg shadow-emerald-900/10">
              <div className="border-b border-zinc-800 bg-gradient-to-r from-zinc-900 to-zinc-900/70">
                <div className="flex h-14">
                  {["ssa", "optimized", "cfg", "smt"].map((tab) => (
                    <button
                      key={tab}
                      onClick={() => setActiveTab(tab)}
                      className={`px-4 h-full transition-all ${
                        activeTab === tab
                          ? "border-b-2 border-emerald-500 text-emerald-400"
                          : "text-zinc-400 hover:text-zinc-300"
                      }`}
                    >
                      {tab === "ssa" && "SSA Form"}
                      {tab === "optimized" && "Optimized SSA"}
                      {tab === "cfg" && "Control Flow Graph"}
                      {tab === "smt" && "SMT Constraints"}
                    </button>
                  ))}
                </div>
              </div>

              <div className="p-5">
                {activeTab === "ssa" && (
                  <div className="space-y-4">
                    <div className="space-y-2">
                      <div className="flex items-center justify-between">
                        <label className="text-zinc-400 flex items-center gap-2">
                          <span className="inline-flex items-center rounded-md bg-emerald-900/80 px-2 py-1 text-xs font-medium text-emerald-100">
                            Program 1
                          </span>
                        </label>
                      </div>
                      <div className="relative">
                        <pre className="font-mono text-sm bg-zinc-950 p-4 rounded-lg overflow-auto h-[300px] border border-zinc-800 text-emerald-100">
                          {ssaForm1 || "No SSA form generated yet."}
                        </pre>
                        <div className="absolute top-2 right-2">
                          <span className="inline-flex items-center rounded-md bg-zinc-800/80 px-2 py-1 text-xs font-medium text-zinc-300">
                            SSA
                          </span>
                        </div>
                      </div>
                    </div>

                    {mode === "equivalence" && (
                      <div className="space-y-2">
                        <div className="flex items-center justify-between">
                          <label className="text-zinc-400 flex items-center gap-2">
                            <span className="inline-flex items-center rounded-md bg-amber-900/80 px-2 py-1 text-xs font-medium text-amber-100">
                              Program 2
                            </span>
                          </label>
                        </div>
                        <div className="relative">
                          <pre className="font-mono text-sm bg-zinc-950 p-4 rounded-lg overflow-auto h-[300px] border border-zinc-800 text-amber-100">
                            {ssaForm2 || "No SSA form generated yet."}
                          </pre>
                          <div className="absolute top-2 right-2">
                            <span className="inline-flex items-center rounded-md bg-zinc-800/80 px-2 py-1 text-xs font-medium text-zinc-300">
                              SSA
                            </span>
                          </div>
                        </div>
                      </div>
                    )}
                  </div>
                )}

                {activeTab === "optimized" && (
                  <div className="space-y-4">
                    <div className="space-y-2">
                      <div className="flex items-center justify-between">
                        <label className="text-zinc-400 flex items-center gap-2">
                          <span className="inline-flex items-center rounded-md bg-emerald-900/80 px-2 py-1 text-xs font-medium text-emerald-100">
                            Program 1
                          </span>
                        </label>
                      </div>
                      <div className="relative">
                        <pre className="font-mono text-sm bg-zinc-950 p-4 rounded-lg overflow-auto h-[300px] border border-zinc-800 text-emerald-100">
                          {optimizedSSA1 || "No optimized SSA form generated yet."}
                        </pre>
                        <div className="absolute top-2 right-2">
                          <span className="inline-flex items-center rounded-md bg-zinc-800/80 px-2 py-1 text-xs font-medium text-zinc-300">
                            Optimized
                          </span>
                        </div>
                      </div>
                    </div>

                    {mode === "equivalence" && (
                      <div className="space-y-2">
                        <div className="flex items-center justify-between">
                          <label className="text-zinc-400 flex items-center gap-2">
                            <span className="inline-flex items-center rounded-md bg-amber-900/80 px-2 py-1 text-xs font-medium text-amber-100">
                              Program 2
                            </span>
                          </label>
                        </div>
                        <div className="relative">
                          <pre className="font-mono text-sm bg-zinc-950 p-4 rounded-lg overflow-auto h-[300px] border border-zinc-800 text-amber-100">
                            {optimizedSSA2 || "No optimized SSA form generated yet."}
                          </pre>
                          <div className="absolute top-2 right-2">
                            <span className="inline-flex items-center rounded-md bg-zinc-800/80 px-2 py-1 text-xs font-medium text-zinc-300">
                              Optimized
                            </span>
                          </div>
                        </div>
                      </div>
                    )}
                  </div>
                )}

                {activeTab === "cfg" && (
                  <div>
                    <div className="bg-zinc-950 p-4 rounded-lg overflow-auto h-[650px] border border-zinc-800">
                      {cfgData ? <SimpleGraph data={cfgData} /> : "No control flow graph generated yet."}
                    </div>
                  </div>
                )}

                {activeTab === "smt" && (
                  <div>
                    <div className="relative">
                      <pre className="font-mono text-sm bg-zinc-950 p-4 rounded-lg overflow-auto h-[650px] border border-zinc-800 text-cyan-100">
                        {smtCode || "No SMT code generated yet."}
                      </pre>
                      <div className="absolute top-2 right-2">
                        <span className="inline-flex items-center rounded-md bg-zinc-800/80 px-2 py-1 text-xs font-medium text-zinc-300">
                          SMT
                        </span>
                      </div>
                    </div>
                  </div>
                )}
              </div>
            </div>
          </div>
        </div>
      </main>

      <style jsx>{`
        @keyframes fadeIn {
          from { opacity: 0; transform: translateY(10px); }
          to { opacity: 1; transform: translateY(0); }
        }
        .animate-fadeIn {
          animation: fadeIn 0.3s ease-out forwards;
        }
        @keyframes pulse {
          0%, 100% { opacity: 1; }
          50% { opacity: 0.7; }
        }
        .animate-pulse {
          animation: pulse 2s cubic-bezier(0.4, 0, 0.6, 1) infinite;
        }
      `}</style>
    </div>
  );
}