import React from 'react';

const SimpleGraph = ({ data }) => {
  if (!data || !data.nodes || !data.edges) {
    return <div className="text-zinc-500 flex items-center justify-center h-full">No graph data available</div>;
  }

  return (
    <div className="p-4">
      <h3 className="font-medium mb-6 text-emerald-400 flex items-center">
        <svg className="w-5 h-5 mr-2" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2">
          <path d="M2 12h2m16 0h2M7 2v2m0 16v2m10-20v2m0 16v2" strokeLinecap="round" />
          <circle cx="12" cy="12" r="3" />
          <circle cx="7" cy="7" r="3" />
          <circle cx="17" cy="7" r="3" />
          <circle cx="17" cy="17" r="3" />
          <circle cx="7" cy="17" r="3" />
        </svg>
        Control Flow Graph
      </h3>
      
      <div className="grid grid-cols-1 md:grid-cols-2 gap-6">
        <div className="space-y-3">
          <h4 className="text-sm font-medium text-zinc-400 flex items-center">
            <svg className="w-4 h-4 mr-2" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2">
              <circle cx="12" cy="12" r="7" />
              <path d="M12 9v6m-3-3h6" strokeLinecap="round" />
            </svg>
            Nodes
          </h4>
          <div className="space-y-2 overflow-auto max-h-[520px] pr-2">
            {data.nodes.map((node, idx) => (
              <div
                key={idx}
                className="p-3 bg-zinc-900/80 backdrop-blur rounded-lg border border-zinc-800 flex items-center justify-between hover:border-emerald-800/60 transition-all group"
              >
                <div className="flex items-center gap-2">
                  <span className="inline-flex items-center justify-center rounded-full bg-emerald-900/50 w-6 h-6 text-xs font-medium text-emerald-100">
                    {node.id}
                  </span>
                  <span className="text-sm group-hover:text-emerald-300 transition-colors">{node.label}</span>
                </div>
              </div>
            ))}
          </div>
        </div>

        <div className="space-y-3">
          <h4 className="text-sm font-medium text-zinc-400 flex items-center">
            <svg className="w-4 h-4 mr-2" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2">
              <path d="M5 12h14m-7-7l7 7-7 7" strokeLinecap="round" strokeLinejoin="round" />
            </svg>
            Edges
          </h4>
          <div className="space-y-2 overflow-auto max-h-[520px] pr-2">
            {data.edges.map((edge, idx) => (
              <div
                key={idx}
                className="p-3 bg-zinc-900/80 backdrop-blur rounded-lg border border-zinc-800 flex items-center justify-between hover:border-emerald-800/60 transition-all group"
              >
                <div className="flex items-center gap-2">
                  <span className="inline-flex items-center justify-center rounded-md bg-zinc-800/90 w-6 h-6 text-xs font-medium text-zinc-300 group-hover:bg-zinc-700/90 transition-colors">
                    {edge.from}
                  </span>
                  <svg width="20" height="20" viewBox="0 0 24 24" fill="none" className="text-emerald-400">
                    <path
                      d="M5 12h14m-7-7l7 7-7 7"
                      stroke="currentColor"
                      strokeWidth="2"
                      strokeLinecap="round"
                      strokeLinejoin="round"
                    />
                  </svg>
                  <span className="inline-flex items-center justify-center rounded-md bg-zinc-800/90 w-6 h-6 text-xs font-medium text-zinc-300 group-hover:bg-zinc-700/90 transition-colors">
                    {edge.to}
                  </span>
                  {edge.label && (
                    <span className="text-amber-400 text-xs px-2 py-1 rounded-full bg-amber-900/20 border border-amber-800/30">
                      {edge.label}
                    </span>
                  )}
                </div>
              </div>
            ))}
          </div>
        </div>
      </div>
    </div>
  );
};

export default SimpleGraph;