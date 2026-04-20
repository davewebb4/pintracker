import { useState, useEffect, useCallback, useRef } from "react";
import { supabase } from "./supabase";

const uuid = () => crypto.randomUUID();

const STORAGE_KEY = "pinpal-data";

// ─── Pin Layout ───
const PIN_POSITIONS = [
  { id: 7, x: 20, y: 0 },  { id: 8, x: 40, y: 0 },  { id: 9, x: 60, y: 0 },  { id: 10, x: 80, y: 0 },
  { id: 4, x: 30, y: 20 }, { id: 5, x: 50, y: 20 }, { id: 6, x: 70, y: 20 },
  { id: 2, x: 40, y: 40 }, { id: 3, x: 60, y: 40 },
  { id: 1, x: 50, y: 60 },
];

// ─── Scoring ───
function calculateScore(frames) {
  const rolls = [];
  for (const f of frames) if (f.rolls) f.rolls.forEach(r => rolls.push(r));
  let score = 0, ri = 0;
  for (let frame = 0; frame < 10; frame++) {
    if (ri >= rolls.length) break;
    if (frame < 9) {
      if (rolls[ri] === 10) { score += 10 + (rolls[ri+1]||0) + (rolls[ri+2]||0); ri++; }
      else if ((rolls[ri]||0)+(rolls[ri+1]||0) === 10) { score += 10+(rolls[ri+2]||0); ri+=2; }
      else { score += (rolls[ri]||0)+(rolls[ri+1]||0); ri+=2; }
    } else { score += (rolls[ri]||0)+(rolls[ri+1]||0)+(rolls[ri+2]||0); }
  }
  return score;
}

function getFrameScores(frames) {
  const rolls = [];
  for (const f of frames) if (f.rolls) f.rolls.forEach(r => rolls.push(r));
  const result = []; let ri = 0, cum = 0;
  for (let frame = 0; frame < 10; frame++) {
    if (ri >= rolls.length) { result.push(null); continue; }
    if (frame < 9) {
      if (rolls[ri] === 10) {
        if (rolls[ri+1]!==undefined && rolls[ri+2]!==undefined) { cum+=10+rolls[ri+1]+rolls[ri+2]; result.push(cum); } else result.push(null);
        ri++;
      } else if (rolls[ri+1]===undefined) { result.push(null); ri++; }
      else if (rolls[ri]+rolls[ri+1]===10) {
        if (rolls[ri+2]!==undefined) { cum+=10+rolls[ri+2]; result.push(cum); } else result.push(null);
        ri+=2;
      } else { cum+=rolls[ri]+rolls[ri+1]; result.push(cum); ri+=2; }
    } else {
      if (rolls[ri]===10||(rolls[ri]||0)+(rolls[ri+1]||0)===10) {
        if (rolls[ri+2]!==undefined) { cum+=(rolls[ri]||0)+(rolls[ri+1]||0)+(rolls[ri+2]||0); result.push(cum); } else result.push(null);
      } else {
        if (rolls[ri+1]!==undefined) { cum+=(rolls[ri]||0)+(rolls[ri+1]||0); result.push(cum); } else result.push(null);
      }
    }
  }
  return result;
}

function getMaxPossibleScore(frames) {
  const existing = [];
  for (const f of frames) if (f.rolls) f.rolls.forEach(r => existing.push(r));
  const filled = [...existing];
  let pos = 0;
  for (let frame = 0; frame < 10; frame++) {
    if (frame < 9) {
      if (pos >= filled.length) { filled.push(10); pos++; }
      else if (filled[pos] === 10) { pos++; }
      else { const first=filled[pos]; pos++; if (pos>=filled.length) filled.push(10-first); pos++; }
    } else {
      if (pos>=filled.length) filled.push(10);
      const r1=filled[pos]; pos++;
      if (pos>=filled.length) filled.push(r1===10?10:10-r1);
      const r2=filled[pos]; pos++;
      if (r1===10||r1+r2>=10) { if (pos>=filled.length) filled.push(10); pos++; }
    }
  }
  let score=0; pos=0;
  for (let frame=0;frame<10;frame++) {
    if (frame<9) {
      if (filled[pos]===10) { score+=10+(filled[pos+1]||0)+(filled[pos+2]||0); pos++; }
      else if ((filled[pos]||0)+(filled[pos+1]||0)===10) { score+=10+(filled[pos+2]||0); pos+=2; }
      else { score+=(filled[pos]||0)+(filled[pos+1]||0); pos+=2; }
    } else { score+=(filled[pos]||0)+(filled[pos+1]||0)+(filled[pos+2]||0); }
  }
  return score;
}

// ─── Stats Utilities ───
// Pin adjacency based on physical proximity in the triangular layout
const PIN_ADJACENCY = {
  1:[2,3], 2:[1,3,4,5], 3:[1,2,5,6],
  4:[2,5,7,8], 5:[2,3,4,6,8,9], 6:[3,5,9,10],
  7:[4,8], 8:[4,5,7,9], 9:[5,6,8,10], 10:[6,9],
};

// Combinations scored as splits regardless of adjacency
const EXPLICIT_SPLITS = new Set([
  "2,3","4,5","5,6","4,5,6",
  "7,8","8,9","9,10","7,8,9","8,9,10","7,8,9,10",
]);

function isSplit(pinsLeft) {
  if (!pinsLeft || pinsLeft.length < 2) return false;
  if (pinsLeft.includes(1)) return false; // headpin must be down
  const key = [...pinsLeft].sort((a,b) => a-b).join(",");
  if (EXPLICIT_SPLITS.has(key)) return true;
  const remaining = new Set(pinsLeft);
  const visited = new Set();
  let groups = 0;
  for (const pin of remaining) {
    if (visited.has(pin)) continue;
    groups++;
    if (groups >= 2) return true;
    const queue = [pin];
    while (queue.length) {
      const curr = queue.shift();
      if (visited.has(curr)) continue;
      visited.add(curr);
      for (const n of PIN_ADJACENCY[curr] || []) {
        if (remaining.has(n) && !visited.has(n)) queue.push(n);
      }
    }
  }
  return false;
}

function isCleanGame(game) {
  for (let i = 0; i < 10; i++) {
    const f = game.frames[i];
    const r1 = f.rolls?.[0], r2 = f.rolls?.[1];
    if (r1 === undefined) return false;
    if (r1 === 10) continue; // strike = clean
    if (r2 === undefined) return false;
    if (r1 + r2 !== 10) return false; // not a spare = open
  }
  return true;
}

function analyzeFrames(games) {
  const s = {
    totalFrames: 0,
    firstBallTotal: 0,
    strikeOpp: 0, strikes: 0,
    spareOpp: 0, spares: 0,
    singleOpp: 0, singleMade: 0,
    multiOpp: 0,  multiMade: 0,
    splitOpp: 0,  splitMade: 0,
    openFrames: 0,
  };
  for (const game of games) {
    for (let fi = 0; fi < 10; fi++) {
      const frame = game.frames[fi];
      if (!frame.rolls || frame.rolls.length < 1) continue;
      const r1 = frame.rolls[0];
      s.totalFrames++;
      s.firstBallTotal += r1;
      s.strikeOpp++;
      if (r1 === 10) {
        s.strikes++;
      } else {
        const pinsLeft = frame.pinsLeft || [];
        // Only classify if pin data is consistent
        const accurate = pinsLeft.length === (10 - r1);
        const split  = accurate && isSplit(pinsLeft);
        const single = accurate && pinsLeft.length === 1;
        const multi  = accurate && pinsLeft.length > 1 && !split;
        s.spareOpp++;
        if (split)       s.splitOpp++;
        else if (single) s.singleOpp++;
        else if (multi)  s.multiOpp++;
        if (frame.rolls.length >= 2) {
          const spare = (r1 + frame.rolls[1] === 10);
          if (spare) {
            s.spares++;
            if (split)       s.splitMade++;
            else if (single) s.singleMade++;
            else if (multi)  s.multiMade++;
          } else {
            s.openFrames++;
          }
        }
      }
    }
  }
  return s;
}

// ─── Data Factories ───
function emptyGame(type="open", leagueName="", leagueId=null, seriesId=null) {
  return {
    id: uuid(),
    type, leagueName, leagueId, seriesId,
    date: new Date().toISOString().split("T")[0],
    frames: Array.from({length:10},(_,i)=>({frameNum:i+1,rolls:[],pinsLeft:[]})),
    complete: false,
  };
}

function emptyLeague(name, gamesPerSeries) {
  return { id: uuid(), name, gamesPerSeries, createdAt: new Date().toISOString() };
}

// ─── Shared Styles ───
const C_DARK = {
  gold: "#f0c97a", darkGold: "#c8952a", cream: "#f0e6d3",
  bg: "#0d0a07", card: "#1e1812", border: "#3d3424", muted: "#8a7a5a",
  text: "#f0e6d3", overlay: "rgba(0,0,0,0.75)", overlayDeep: "rgba(0,0,0,0.9)",
  surface: "#1a150e", surfaceDeep: "#15100a", inputBg: "#1e1812",
  strikeColor: "#e74c3c", spareColor: "#3498db",
  btnText: "#0d0a07",
};
const C_LIGHT = {
  gold: "#a07020", darkGold: "#7a5210", cream: "#1a1208",
  bg: "#f0ece2", card: "#ffffff", border: "#c8b888", muted: "#7a6a48",
  text: "#1a1208", overlay: "rgba(0,0,0,0.45)", overlayDeep: "rgba(0,0,0,0.6)",
  surface: "#ede6d6", surfaceDeep: "#e5dcc8", inputBg: "#f8f4ec",
  strikeColor: "#c0392b", spareColor: "#2980b9",
  btnText: "#ffffff",
};

let C = C_DARK;

const btnPrimary = () => ({
  background: `linear-gradient(145deg, ${C.gold}, ${C.darkGold})`,
  color: C.btnText, border: "none", padding: "14px 32px",
  fontSize: 15, fontFamily: "'Oswald', sans-serif",
  textTransform: "uppercase", letterSpacing: 3, fontWeight: 500,
  borderRadius: 12, cursor: "pointer", width: "100%",
  boxShadow: "0 4px 15px rgba(200,169,110,0.25)",
});
const btnSecondary = () => ({
  ...btnPrimary(),
  background: "transparent", border: `2px solid ${C.border}`,
  color: C.gold, boxShadow: "none",
});

const label = () => ({
  fontSize: 11, color: C.muted, textTransform: "uppercase",
  letterSpacing: 2, display: "block", marginBottom: 8,
  fontFamily: "'Oswald', sans-serif",
});
const inputStyle = () => ({
  width: "100%", padding: "12px 14px", background: C.inputBg,
  border: `1px solid ${C.border}`, borderRadius: 8, color: C.text,
  fontSize: 14, fontFamily: "'Oswald', sans-serif",
  outline: "none", boxSizing: "border-box",
});

// ─── Responsive breakpoint hook ───
function useBreakpoint() {
  const [width, setWidth] = useState(() => window.innerWidth);
  useEffect(() => {
    const handler = () => setWidth(window.innerWidth);
    window.addEventListener("resize", handler);
    return () => window.removeEventListener("resize", handler);
  }, []);
  if (width < 768) return "mobile";
  if (width < 1024) return "tablet";
  return "desktop";
}

// ─── PinDiagram ───
function PinDiagram({ standing, onToggle, disabled }) {
  const isDragging = useRef(false);
  const draggedPins = useRef(new Set());
  const containerRef = useRef(null);

  const handlePointerDown = (e) => {
    if (disabled) return;
    isDragging.current = true;
    draggedPins.current = new Set();
    containerRef.current?.setPointerCapture(e.pointerId);
    const pinId = parseInt(e.target.dataset.pinId);
    if (!isNaN(pinId)) { draggedPins.current.add(pinId); onToggle(pinId); }
  };

  const handlePointerMove = (e) => {
    if (!isDragging.current || disabled) return;
    const el = document.elementFromPoint(e.clientX, e.clientY);
    const pinId = el ? parseInt(el.dataset.pinId) : NaN;
    if (!isNaN(pinId) && !draggedPins.current.has(pinId)) {
      draggedPins.current.add(pinId); onToggle(pinId);
    }
  };

  const endDrag = () => { isDragging.current = false; draggedPins.current = new Set(); };

  return (
    <div ref={containerRef}
      style={{ position:"relative", width:"100%", maxWidth:340, height:280, margin:"0 auto", touchAction:"none" }}
      onPointerDown={handlePointerDown} onPointerMove={handlePointerMove}
      onPointerUp={endDrag} onPointerCancel={endDrag}>
      {PIN_POSITIONS.map(pin => {
        const isUp = standing.includes(pin.id);
        return (
          <button key={pin.id} data-pin-id={pin.id} disabled={disabled} style={{
            position:"absolute", left:`${pin.x}%`, top:`calc(${pin.y}% + 56px)`,
            transform:"translate(-50%,-50%)", width:46, height:46,
            borderRadius:"50%", border:"none",
            cursor: disabled ? "default" : "pointer",
            background: isUp ? "linear-gradient(145deg,#f0e6d3,#d4c4a8)" : "transparent",
            color: isUp ? "#2a1f0e" : "#555",
            fontFamily:"'Oswald',sans-serif", fontSize:18, fontWeight:700,
            boxShadow: isUp ? "0 3px 8px rgba(0,0,0,0.3),inset 0 1px 2px rgba(255,255,255,0.4)" : "none",
            transition:"all 0.15s ease", opacity: disabled?0.5:1, userSelect:"none",
          }}>{isUp ? pin.id : <span style={{width:20,height:20,borderRadius:"50%",background:"#222",display:"inline-block"}}/>}</button>
        );
      })}
    </div>
  );
}

// ─── Scorecard ───
function Scorecard({ frames, complete, onFrameClick, currentFrame: activeFrame }) {
  const bp = useBreakpoint();
  const fontOffset = bp === "mobile" ? -4 : bp === "tablet" ? -2 : 0;
  const rollFont  = 22 + fontOffset;
  const scoreFont = 22 + fontOffset;
  const rollH     = 32 + fontOffset;
  const scoreH    = 34 + fontOffset;
  const frameScores = getFrameScores(frames);
  const frame10Done = (frames[9]?.rolls?.length >= 2 && frames[9].rolls[0] + frames[9].rolls[1] < 10) || frames[9]?.rolls?.length >= 3;
  const maxScore = (complete || frame10Done) ? null : getMaxPossibleScore(frames);

  const renderRolls = (frame, fi) => {
    const rolls = frame.rolls || [];
    const splitOnFirst = rolls[0] !== undefined && rolls[0] !== 10 &&
      isSplit(frame.pinsLeft) && (frame.pinsLeft||[]).length === (10 - rolls[0]);

    if (fi < 9) {
      const r1=rolls[0], r2=rolls[1];
      let d1 = r1!==undefined ? (r1===10?"X":r1===0?"-":r1) : "";
      let d2 = "";
      if (r1===10) { d1=""; d2="X"; }
      else if (r2!==undefined) d2 = (r1+r2===10)?"/":r2===0?"-":r2;
      return (
        <div style={{display:"flex",width:"100%",height:"100%"}}>
          <div style={{flex:1,display:"flex",alignItems:"center",justifyContent:"center",borderRight:`1px solid ${C.border}`}}>
            <span style={{fontSize:rollFont,fontWeight:400,color:splitOnFirst?C.strikeColor:C.gold}}>{d1}</span>
          </div>
          <div style={{flex:1,display:"flex",alignItems:"center",justifyContent:"center"}}>
            <span style={{fontSize:rollFont,fontWeight:400,color:C.gold}}>{d2}</span>
          </div>
        </div>
      );
    } else {
      return (
        <div style={{display:"flex",width:"100%",height:"100%"}}>
          {[0,1,2].map(i => {
            const r=rolls[i];
            let d = r!==undefined?(r===10?"X":r===0?"-":r):"";
            if (i===1&&rolls[0]!==10&&r!==undefined&&rolls[0]+r===10) d="/";
            if (i===2&&rolls[1]!==10&&r!==undefined&&rolls[0]===10&&rolls[1]!==10&&rolls[1]+r===10) d="/";
            const color = i===0&&splitOnFirst ? C.strikeColor : C.gold;
            return (
              <div key={i} style={{flex:1,display:"flex",alignItems:"center",justifyContent:"center",borderRight:i<2?`1px solid ${C.border}`:"none"}}>
                <span style={{fontSize:rollFont,fontWeight:400,color}}>{d}</span>
              </div>
            );
          })}
        </div>
      );
    }
  };

  return (
    <div style={{margin:"12px 0",overflowX:"auto"}}>
      <div style={{display:"flex",width:"100%",minWidth:320}}>
        {frames.map((frame,i) => {
          const editable = onFrameClick && (activeFrame === undefined || i <= activeFrame);
          return (
            <div key={i}
              onClick={editable ? () => onFrameClick(i) : undefined}
              style={{
                flex: i===9?"1.5":"1",
                minWidth:0, overflow:"hidden",
                borderTop:`1px solid ${editable ? C.darkGold+"66" : C.border}`,
                borderBottom:`1px solid ${editable ? C.darkGold+"66" : C.border}`,
                borderLeft:`1px solid ${editable ? C.darkGold+"66" : C.border}`,
                borderRight: i<9?"none":`1px solid ${editable ? C.darkGold+"66" : C.border}`,
                textAlign:"center", background: editable ? C.surfaceDeep : C.surface,
                cursor: editable ? "pointer" : "default",
              }}>
              <div style={{fontSize:13,padding:"1px 0",borderBottom:`1px solid ${C.border}`,color: editable ? C.darkGold : C.muted,fontFamily:"'Oswald',sans-serif",letterSpacing:1,fontWeight:300}}>{i+1}</div>
              <div style={{borderBottom:`1px solid ${C.border}`,height:rollH,display:"flex",alignItems:"stretch"}}>
                {renderRolls(frame,i)}
              </div>
              <div style={{height:scoreH,fontSize:scoreFont,fontWeight:300,fontFamily:"'Oswald',sans-serif",color:C.cream,display:"flex",flexDirection:"column",alignItems:"center",justifyContent:"center",gap:1}}>
                <span>{frameScores[i]!==null?frameScores[i]:""}</span>
                {i===9&&maxScore!==null&&(
                  <span style={{fontSize:14,color:C.muted,fontWeight:400}}>[{maxScore}]</span>
                )}
              </div>
            </div>
          );
        })}
      </div>
    </div>
  );
}

// ─── Home (Landing) ───
function HomeView({ leagues, games, onNavigate, activeGame, onResume, onAbandon }) {
  const tiles = [
    { id:"leagues",     label:"LEAGUES",      accent:C.gold },
    { id:"tournaments", label:"TOURNAMENTS",  accent:C.muted },
    { id:"open",        label:"OPEN BOWLING", accent:C.gold },
    { id:"stats",       label:"STATISTICS",   accent:C.muted },
    { id:"settings",    label:"SETTINGS",     accent:C.gold },
    { id:"help",        label:"HELP",         accent:C.muted },
  ];

  return (
    <div style={{padding:"0 16px 80px"}}>
      {activeGame&&(
        <div style={{marginBottom:16,background:C.card,borderRadius:14,border:`2px solid ${C.gold}`,overflow:"hidden"}}>
          <div style={{padding:"14px 18px",display:"flex",alignItems:"center",justifyContent:"space-between"}}>
            <div>
              <div style={{fontSize:13,color:C.muted,textTransform:"uppercase",letterSpacing:2,fontFamily:"'Oswald',sans-serif"}}>Game In Progress</div>
            </div>
            <div style={{display:"flex",gap:8}}>
              <button style={{...btnSecondary(),width:"auto",padding:"8px 14px",fontSize:13,color:"#8a4a4a",border:"1px solid #3a2020"}} onClick={onAbandon}>Abandon</button>
              <button style={{...btnPrimary(),width:"auto",padding:"8px 18px",fontSize:13}} onClick={onResume}>Resume</button>
            </div>
          </div>
        </div>
      )}
      <div style={{display:"flex",flexDirection:"column",gap:10}}>
        {tiles.map(tile => (
          <div key={tile.id} onClick={()=>onNavigate(tile.id)} style={{
            background:`linear-gradient(160deg, ${C.surface} 0%, ${C.surfaceDeep} 100%)`,
            borderRadius:14, padding:"18px 22px",
            border:`1px solid ${C.border}`, cursor:"pointer",
            display:"flex", alignItems:"center", justifyContent:"space-between",
            boxShadow:"0 4px 12px rgba(0,0,0,0.2), inset 0 1px 0 rgba(255,255,255,0.05)",
          }}>
            <div>
              <div style={{fontFamily:"'Oswald',sans-serif",fontSize:17,fontWeight:600,color:tile.accent,letterSpacing:2}}>{tile.label}</div>
              <div style={{fontSize:14,color:C.muted,marginTop:3}}>{tile.sub}</div>
            </div>
            <div style={{fontSize:18,color:C.border}}>›</div>
          </div>
        ))}
      </div>
    </div>
  );
}

// ─── Leagues List ───
function LeaguesView({ leagues, games, onNavigate, onSelectLeague }) {
  return (
    <div style={{padding:"0 16px 80px"}}>
      <button style={btnPrimary()} onClick={()=>onNavigate("league-new")}>+ New League</button>
      {leagues.length===0 ? (
        <div style={{textAlign:"center",padding:40,color:C.muted}}>
          <p style={{fontFamily:"'Oswald',sans-serif",fontSize:16}}>No leagues yet</p>
          <p style={{fontSize:14,marginTop:6}}>Create your first league above</p>
        </div>
      ) : leagues.map(league => {
        const lg = games.filter(g=>g.leagueId===league.id&&g.complete);
        const scores = lg.map(g=>calculateScore(g.frames));
        const avg = scores.length>0?(scores.reduce((a,b)=>a+b,0)/scores.length).toFixed(0):"—";
        const high = scores.length>0?Math.max(...scores):"—";
        const seriesCount = new Set(lg.map(g=>g.seriesId).filter(Boolean)).size;
        const seriesMap2 = {};
        for (const g of lg) { const k=g.seriesId||g.id; if(!seriesMap2[k]) seriesMap2[k]=[]; seriesMap2[k].push(g); }
        const seriesTotals2 = Object.values(seriesMap2).map(s=>s.reduce((t,g)=>t+calculateScore(g.frames),0));
        const highSeries2 = seriesTotals2.length>0?Math.max(...seriesTotals2):"—";
        return (
          <div key={league.id} onClick={()=>{onSelectLeague(league);onNavigate("league-detail");}} style={{
            background:C.card, borderRadius:12, padding:16,
            border:`1px solid ${C.border}`, marginTop:12, cursor:"pointer",
          }}>
            <div style={{fontFamily:"'Oswald',sans-serif",fontSize:20,color:C.gold,fontWeight:600,textAlign:"left"}}>{league.name}</div>
            {scores.length>0&&(
              <div style={{display:"flex",gap:16,marginTop:12,paddingTop:12,borderTop:`1px solid ${C.border}`,flexWrap:"wrap"}}>
                {[{l:"HIGH",v:high},{l:"SERIES",v:highSeries2},{l:"AVG",v:avg}].map(s=>(
                  <div key={s.l} style={{display:"flex",alignItems:"baseline",gap:5}}>
                    <span style={{fontSize:18,fontWeight:400,color:C.gold,fontFamily:"'Oswald',sans-serif"}}>{s.v}</span>
                    <span style={{fontSize:12,color:C.muted,letterSpacing:1}}>{s.l}</span>
                  </div>
                ))}
              </div>
            )}
          </div>
        );
      })}
    </div>
  );
}

// ─── New League ───
function LeagueNewView({ onNavigate, onCreate }) {
  const [name, setName] = useState("");
  const [gamesPerSeries, setGamesPerSeries] = useState(3);

  return (
    <div style={{padding:"0 16px 80px"}}>
      <h2 style={{fontFamily:"'Oswald',sans-serif",fontSize:22,color:C.cream,marginBottom:24,letterSpacing:2,marginTop:8}}>NEW LEAGUE</h2>

      <div style={{marginBottom:20}}>
        <span style={label()}>League Name</span>
        <input value={name} onChange={e=>setName(e.target.value)}
          placeholder="e.g. Tuesday Night League" style={inputStyle()} />
      </div>

      <div style={{marginBottom:28}}>
        <span style={label()}>Games per Series</span>
        <div style={{display:"flex",gap:10}}>
          {[3,4].map(n=>(
            <button key={n} onClick={()=>setGamesPerSeries(n)} style={{
              ...( gamesPerSeries===n ? btnPrimary() : btnSecondary() ),
              flex:1, padding:"14px 8px", fontSize:16, letterSpacing:1,
            }}>
              {n} Games
            </button>
          ))}
        </div>
        <p style={{fontSize:14,color:C.muted,marginTop:10,lineHeight:1.6}}>
          {gamesPerSeries===3
            ? "Standard 3-game series — most common in casual and competitive leagues."
            : "4-game series — used in some competitive leagues for a fuller session."}
        </p>
      </div>

      <button style={{...btnPrimary(), opacity: name.trim()?1:0.4}}
        onClick={()=>{ if(name.trim()){ onCreate(name.trim(),gamesPerSeries); onNavigate("leagues"); } }}>
        Create League
      </button>
    </div>
  );
}

// ─── League Detail ───
function LeagueDetailView({ league, games, onStartSeries, onSelectSeries, onViewStats }) {
  const leagueGames = games.filter(g=>g.leagueId===league.id&&g.complete);

  // Group by seriesId
  const seriesMap = {};
  for (const g of leagueGames) {
    const key = g.seriesId || g.id;
    if (!seriesMap[key]) seriesMap[key] = [];
    seriesMap[key].push(g);
  }
  const seriesList = Object.values(seriesMap).sort((a,b)=>b[0].id-a[0].id);

  const allScores = leagueGames.map(g=>calculateScore(g.frames));
  const avg = allScores.length>0?(allScores.reduce((a,b)=>a+b,0)/allScores.length).toFixed(1):"—";
  const high = allScores.length>0?Math.max(...allScores):"—";
  const seriesTotals = seriesList.map(s=>s.reduce((t,g)=>t+calculateScore(g.frames),0));
  const highSeries = seriesTotals.length>0?Math.max(...seriesTotals):"—";

  return (
    <div style={{padding:"0 16px 80px"}}>
      <div style={{textAlign:"center",marginBottom:16,marginTop:8}}>
        <h2 style={{fontFamily:"'Oswald',sans-serif",fontSize:24,color:C.gold,margin:0,fontWeight:600}}>{league.name}</h2>
        <p style={{fontSize:14,color:C.muted,marginTop:4}}>{league.gamesPerSeries}-game series</p>
      </div>

      {allScores.length>0&&(
        <div style={{display:"flex",gap:12,marginBottom:16}}>
          {[{l:"AVG",v:avg},{l:"HIGH GAME",v:high},{l:"HIGH SERIES",v:highSeries}].map(s=>(
            <div key={s.l} style={{flex:1,background:C.card,borderRadius:10,padding:"12px 8px",textAlign:"center",border:`1px solid ${C.border}`}}>
              <div style={{fontSize:22,fontWeight:400,color:C.gold,fontFamily:"'Oswald',sans-serif"}}>{s.v}</div>
              <div style={{fontSize:14,color:C.muted,letterSpacing:1,marginTop:2}}>{s.l}</div>
            </div>
          ))}
        </div>
      )}

      <div style={{display:"flex",flexDirection:"column",gap:10,marginBottom:20}}>
        <button style={btnPrimary()} onClick={()=>onStartSeries(league)}>Bowl Series</button>
        {leagueGames.length>0&&(
          <button style={{...btnSecondary(),fontSize:14,letterSpacing:1}} onClick={onViewStats}>League Stats</button>
        )}
      </div>

      {seriesList.length===0?(
        <div style={{textAlign:"center",padding:32,color:C.muted}}>
          <p style={{fontFamily:"'Oswald',sans-serif"}}>No series bowled yet</p>
        </div>
      ):seriesList.map((series,si)=>{
        const seriesScores = series.map(g=>calculateScore(g.frames));
        const total = seriesScores.reduce((a,b)=>a+b,0);
        return (
          <div key={si} onClick={()=>onSelectSeries(series)}
            style={{background:C.card,borderRadius:12,padding:14,border:`1px solid ${C.border}`,marginBottom:10,cursor:"pointer"}}>
            <div style={{display:"flex",justifyContent:"space-between",alignItems:"center",marginBottom:6}}>
              <span style={{fontSize:14,color:C.muted}}>{series[0]?.date}</span>
              <div style={{display:"flex",alignItems:"center",gap:10}}>
                <span style={{fontFamily:"'Oswald',sans-serif",fontSize:18,color:C.gold,fontWeight:700}}>
                  {total} <span style={{fontSize:14,fontWeight:400,color:C.muted}}>total</span>
                </span>
                <span style={{fontSize:16,color:C.muted}}>›</span>
              </div>
            </div>
            <div style={{display:"flex",alignItems:"baseline",justifyContent:"space-between",fontSize:14}}>
              <span style={{color:C.cream}}>Scores: {seriesScores.join(", ")}</span>
              <span style={{color:C.muted}}>Avg: {(total/seriesScores.length).toFixed(1)}</span>
            </div>
          </div>
        );
      })}
    </div>
  );
}

// ─── Series Detail (view past series stats) ───
function SeriesDetailView({ series, league, onViewStats, onFrameEdit }) {
  const [selectedGame, setSelectedGame] = useState(null);
  const scores = series.map(g => calculateScore(g.frames));
  const total  = scores.reduce((a,b) => a+b, 0);
  const avg    = (total / scores.length).toFixed(1);
  const date   = series[0]?.date;

  if (selectedGame) {
    const gi = series.findIndex(g => g.id === selectedGame.id);
    return <GameDetailOverlay game={selectedGame} gameNumber={gi+1} sessionTotal={total} sessionAvg={avg} onClose={()=>setSelectedGame(null)} onFrameEdit={onFrameEdit}/>;
  }

  return (
    <div style={{padding:"0 16px 80px"}}>
      <div style={{textAlign:"center",marginBottom:20,marginTop:8}}>
        <div style={{fontSize:14,color:C.muted,marginBottom:4}}>{league?.name} · {date}</div>
        <div style={{fontSize:64,fontWeight:700,color:C.gold,fontFamily:"'Oswald',sans-serif",lineHeight:1}}>{total}</div>
        <div style={{fontSize:14,color:C.muted,marginTop:4}}>{series.length}-game series · avg {avg}</div>
      </div>
      <button style={{...btnSecondary(), marginBottom:20, fontSize:14, letterSpacing:2}} onClick={onViewStats}>
        Date Statistics
      </button>
      <div style={{background:C.card,borderRadius:12,border:`1px solid ${C.border}`,overflow:"hidden",marginBottom:10}}>
        {series.map((game, gi) => (
          <div key={gi} onClick={()=>setSelectedGame(game)} style={{display:"flex",justifyContent:"space-between",alignItems:"center",padding:"14px 16px",borderBottom:gi<series.length-1?`1px solid ${C.border}`:"none",cursor:"pointer"}}>
            <span style={{fontSize:14,color:C.muted,textTransform:"uppercase",letterSpacing:1,fontFamily:"'Oswald',sans-serif"}}>Game {gi+1}</span>
            <div style={{display:"flex",alignItems:"center",gap:12}}>
              <span style={{fontSize:22,fontWeight:300,color:C.gold,fontFamily:"'Oswald',sans-serif"}}>{scores[gi]}</span>
              <span style={{fontSize:14,color:C.muted}}>›</span>
            </div>
          </div>
        ))}
      </div>
    </div>
  );
}

function SeriesStatsView({ series }) {
  return (
    <div style={{padding:"0 16px 80px"}}>
      <GameStatsModule games={series} />
    </div>
  );
}

function LeagueStatsView({ games, leagues }) {
  return (
    <div style={{padding:"0 16px 80px"}}>
      <GameStatsModule games={games} leagues={leagues} showGameAvg={true} statsTitle="League Statistics" />
    </div>
  );
}

// ─── Between series games ───
function SeriesNextView({ activeSeries, onStartNext, onExit }) {
  const [selectedGame, setSelectedGame] = useState(null);
  const lastGame = activeSeries.completedGames[activeSeries.completedGames.length-1];
  const lastScore = calculateScore(lastGame.frames);
  const runningTotal = activeSeries.completedGames.reduce((t,g)=>t+calculateScore(g.frames),0);
  const gamesDone = activeSeries.completedGames.length;
  const gamesLeft = activeSeries.league.gamesPerSeries - gamesDone;

  return (
    <>
    {selectedGame && <GameRecapOverlay game={selectedGame} onClose={()=>setSelectedGame(null)}/>}
    <div style={{padding:"0 16px",textAlign:"center"}}>
      <div style={{marginTop:40,marginBottom:40}}>
        <div style={{fontSize:14,color:C.muted,letterSpacing:3,fontFamily:"'Oswald',sans-serif",textTransform:"uppercase",marginBottom:8}}>
          Game {gamesDone} Complete
        </div>
        <div style={{fontSize:72,fontWeight:700,color:C.gold,fontFamily:"'Oswald',sans-serif",lineHeight:1}}>{lastScore}</div>
        <div style={{fontSize:14,color:C.muted,marginTop:8}}>Running total: <span style={{color:C.cream}}>{runningTotal}</span></div>
      </div>

      <div style={{display:"flex",gap:8,marginBottom:16}}>
        {activeSeries.completedGames.map((g,i)=>(
          <div key={i} onClick={()=>setSelectedGame(g)} style={{flex:1,background:C.card,borderRadius:10,padding:"10px 4px",textAlign:"center",border:`1px solid ${C.border}`,cursor:"pointer"}}>
            <div style={{fontSize:14,color:C.muted,marginBottom:2}}>G{i+1}</div>
            <div style={{fontSize:18,color:C.cream,fontFamily:"'Oswald',sans-serif",fontWeight:700}}>{calculateScore(g.frames)}</div>
          </div>
        ))}
        {Array.from({length:gamesLeft}).map((_,i)=>(
          <div key={`empty-${i}`} style={{flex:1,background:C.surfaceDeep,borderRadius:10,padding:"10px 4px",textAlign:"center",border:`1px dashed ${C.border}`}}>
            <div style={{fontSize:14,color:C.muted,marginBottom:2}}>G{gamesDone+i+1}</div>
            <div style={{fontSize:18,color:C.muted,fontFamily:"'Oswald',sans-serif"}}>—</div>
          </div>
        ))}
      </div>

      <button style={btnPrimary()} onClick={onStartNext}>
        Bowl Game {gamesDone+1}
      </button>
      <button style={{...btnSecondary(),marginTop:10}} onClick={onExit}>
        Exit Series
      </button>
    </div>
    </>
  );
}

// ─── Game Stats Module ───

function StatsHeading({ title }) {
  return (
    <div style={{
      fontSize:14, letterSpacing:3, textTransform:"uppercase",
      fontFamily:"'Oswald',sans-serif", color:C.muted,
      padding:"20px 0 10px", borderBottom:`1px solid ${C.border}`,
      marginBottom:4,
    }}>{title}</div>
  );
}

// indent: 0 = top level, 1 = sub, 2 = sub-sub
function ListRow({ label, value, sub, indent=0, valueColor, onClick }) {
  const indentPx = indent * 20;
  const labelColor   = indent === 0 ? C.text : C.muted;
  const labelSize    = indent === 2 ? 12 : 13;
  const valueSize    = indent === 2 ? 13 : 15;
  const borderColor  = indent === 0 ? C.border : "transparent";

  return (
    <div onClick={onClick} style={{
      display:"flex", justifyContent:"space-between", alignItems:"center",
      padding:"10px 0", paddingLeft:indentPx,
      borderBottom:`1px solid ${borderColor}`,
      cursor: onClick ? "pointer" : "default",
    }}>
      <div style={{display:"flex",alignItems:"center",gap:6}}>
        {indent > 0 && (
          <span style={{
            width:2, height:14, borderRadius:1,
            background: indent===1 ? C.border : C.surface,
            display:"inline-block", flexShrink:0,
          }}/>
        )}
        <span style={{fontSize:labelSize, color:labelColor}}>{label}</span>
        {onClick && <span style={{fontSize:14,color:C.darkGold,marginLeft:4}}>›</span>}
      </div>
      <div style={{display:"flex",alignItems:"baseline",gap:5,textAlign:"right"}}>
        <span style={{fontSize:valueSize,fontWeight:600,color:valueColor||C.gold,fontFamily:"'Oswald',sans-serif"}}>{value}</span>
        {sub && <span style={{fontSize:14,color:C.muted}}>{sub}</span>}
      </div>
    </div>
  );
}

function PctRow({ label, made, opp, indent=0, valueColor, onClick }) {
  if (!opp) return null;
  const pct = ((made/opp)*100).toFixed(1);
  return (
    <ListRow label={label} value={`${pct}%`} sub={`(${made}/${opp})`}
      indent={indent} valueColor={valueColor} onClick={onClick} />
  );
}

// ─── Shared overlay shell ───
function DrillOverlay({ title, onClose, children }) {
  return (
    <div style={{position:"fixed",top:0,left:0,right:0,bottom:0,background:C.overlayDeep,zIndex:300,display:"flex",flexDirection:"column"}}>
      <div style={{background:C.card,flex:1,display:"flex",flexDirection:"column",overflow:"hidden"}}>
        <div style={{display:"flex",justifyContent:"space-between",alignItems:"center",padding:"20px 20px 14px",borderBottom:`1px solid ${C.border}`,flexShrink:0}}>
          <div style={{fontFamily:"'Oswald',sans-serif",fontSize:16,color:C.gold,letterSpacing:2,textTransform:"uppercase"}}>{title}</div>
          <button onClick={onClose} style={{background:C.gold,border:"none",color:C.btnText,cursor:"pointer",fontSize:14,fontFamily:"'Oswald',sans-serif",fontWeight:500,textTransform:"uppercase",letterSpacing:1,padding:"6px 14px",borderRadius:8}}>Close</button>
        </div>
        <div style={{overflowY:"auto",flex:1,padding:"8px 20px 32px"}}>{children}</div>
      </div>
    </div>
  );
}

// ─── Game Recap Overlay ───
function GameRecapOverlay({ game, onClose }) {
  const score = calculateScore(game.frames);
  return (
    <div style={{position:"fixed",top:0,left:0,right:0,bottom:0,background:C.overlayDeep,zIndex:400,display:"flex",flexDirection:"column"}}>
      <div style={{background:C.card,flex:1,display:"flex",flexDirection:"column",overflow:"hidden"}}>
        <div style={{display:"flex",justifyContent:"space-between",alignItems:"center",padding:"20px 20px 14px",borderBottom:`1px solid ${C.border}`,flexShrink:0}}>
          <div>
            <div style={{fontFamily:"'Oswald',sans-serif",fontSize:28,fontWeight:700,color:C.gold,lineHeight:1}}>{score}</div>
            <div style={{fontSize:14,color:C.cream,fontWeight:600,marginTop:3,letterSpacing:1}}>{game.date}</div>
          </div>
          <button onClick={onClose} style={{background:C.gold,border:"none",color:C.btnText,cursor:"pointer",fontSize:14,fontFamily:"'Oswald',sans-serif",fontWeight:500,textTransform:"uppercase",letterSpacing:1,padding:"6px 14px",borderRadius:8}}>Close</button>
        </div>
        <div style={{overflowY:"auto",flex:1,padding:"20px 16px 32px"}}>
          <Scorecard frames={game.frames} complete={game.complete}/>
        </div>
      </div>
    </div>
  );
}

// ─── Game list drill-down (high game / clean games) ───
function GameListDrillDown({ items, title, onClose }) {
  const [selectedGame, setSelectedGame] = useState(null);
  return (
    <>
      <DrillOverlay title={title} onClose={onClose}>
        {items.map((item, i) => (
          <div key={i} onClick={() => setSelectedGame(item.game)}
            style={{display:"flex",alignItems:"baseline",justifyContent:"space-between",padding:"12px 0",borderBottom:`1px solid ${C.border}`,cursor:"pointer"}}>
            <span style={{fontSize:14,color:C.cream,fontWeight:600}}>{item.date}</span>
            <div style={{display:"flex",alignItems:"baseline",gap:10}}>
              <span style={{fontSize:24,fontWeight:700,color:C.gold,fontFamily:"'Oswald',sans-serif"}}>{item.score}</span>
              <span style={{fontSize:14,color:C.darkGold}}>›</span>
            </div>
          </div>
        ))}
      </DrillOverlay>
      {selectedGame && <GameRecapOverlay game={selectedGame} onClose={() => setSelectedGame(null)}/>}
    </>
  );
}

// ─── Series list drill-down (high series / clean series) ───
function SeriesListDrillDown({ items, title, onClose }) {
  const [selectedSeries, setSelectedSeries] = useState(null);
  const [selectedGame, setSelectedGame] = useState(null);

  if (selectedGame) return <GameRecapOverlay game={selectedGame} onClose={() => setSelectedGame(null)}/>;

  if (selectedSeries) return (
    <DrillOverlay title={`Series — ${selectedSeries.date}`} onClose={() => setSelectedSeries(null)}>
      {selectedSeries.games.map((game, gi) => (
        <div key={gi} onClick={() => setSelectedGame(game)}
          style={{display:"flex",alignItems:"baseline",justifyContent:"space-between",padding:"12px 0",borderBottom:`1px solid ${C.border}`,cursor:"pointer"}}>
          <span style={{fontSize:14,color:C.cream,fontWeight:600}}>Game {gi + 1}</span>
          <div style={{display:"flex",alignItems:"baseline",gap:10}}>
            <span style={{fontSize:24,fontWeight:700,color:C.gold,fontFamily:"'Oswald',sans-serif"}}>{selectedSeries.scores[gi]}</span>
            <span style={{fontSize:14,color:C.darkGold}}>›</span>
          </div>
        </div>
      ))}
    </DrillOverlay>
  );

  return (
    <DrillOverlay title={title} onClose={onClose}>
      {items.map((item, i) => (
        <div key={i} onClick={() => setSelectedSeries(item)}
          style={{display:"flex",alignItems:"baseline",justifyContent:"space-between",padding:"12px 0",borderBottom:`1px solid ${C.border}`,cursor:"pointer"}}>
          <span style={{fontSize:14,color:C.cream,fontWeight:600}}>{item.date}</span>
          <div style={{display:"flex",alignItems:"baseline",gap:10}}>
            <span style={{fontSize:24,fontWeight:700,color:C.gold,fontFamily:"'Oswald',sans-serif"}}>{item.total}</span>
            <span style={{fontSize:14,color:C.darkGold}}>›</span>
          </div>
        </div>
      ))}
    </DrillOverlay>
  );
}

// ─── Game Average Drill-Down ───
function GameAvgDrillDown({ positionScores, onClose }) {
  const positions = Object.keys(positionScores).map(Number).sort((a,b) => a-b);
  return (
    <DrillOverlay title="Average by Game" onClose={onClose}>
      {positions.map(pos => {
        const sc = positionScores[pos];
        const avg = (sc.reduce((a,b)=>a+b,0) / sc.length).toFixed(1);
        return (
          <div key={pos} style={{display:"flex",alignItems:"baseline",justifyContent:"space-between",padding:"12px 0",borderBottom:`1px solid ${C.border}`}}>
            <span style={{fontSize:15,color:C.cream}}>Game {pos+1}</span>
            <div style={{display:"flex",alignItems:"baseline",gap:8}}>
              <span style={{fontSize:24,fontWeight:700,color:C.gold,fontFamily:"'Oswald',sans-serif"}}>{avg}</span>
              <span style={{fontSize:14,color:C.muted}}>({sc.length} game{sc.length!==1?"s":""})</span>
            </div>
          </div>
        );
      })}
    </DrillOverlay>
  );
}

// ─── Strike Streak Drill-Down ───
function StrikeStreakDrillDown({ streakCounts, onClose }) {
  const rows = [];
  for (let n = 12; n >= 1; n--) {
    if (streakCounts[n]) rows.push({ n, count: streakCounts[n] });
  }
  return (
    <DrillOverlay title="Strike Streaks" onClose={onClose}>
      {rows.length === 0 ? (
        <div style={{textAlign:"center",padding:40,color:C.muted,fontFamily:"'Oswald',sans-serif"}}>No data yet</div>
      ) : rows.map(({n, count}) => (
        <div key={n} style={{display:"flex",alignItems:"baseline",justifyContent:"space-between",padding:"12px 0",borderBottom:`1px solid ${C.border}`}}>
          <div style={{display:"flex",alignItems:"baseline",gap:8}}>
            <span style={{fontSize:28,fontWeight:700,color:C.gold,fontFamily:"'Oswald',sans-serif"}}>{n}</span>
            <span style={{fontSize:14,color:C.muted}}>in a row</span>
          </div>
          <span style={{fontSize:20,fontWeight:600,color:C.cream,fontFamily:"'Oswald',sans-serif"}}>{count}x</span>
        </div>
      ))}
    </DrillOverlay>
  );
}

// ─── Pin Mini Map ───
function PinMiniMap({ standing }) {
  return (
    <div style={{position:"relative", width:80, height:68, flexShrink:0}}>
      {PIN_POSITIONS.map(pin => {
        const isUp = standing.includes(pin.id);
        return (
          <div key={pin.id} style={{
            position:"absolute",
            left:`${pin.x}%`,
            top:`calc(${pin.y}% + 12px)`,
            transform:"translate(-50%,-50%)",
            width: isUp ? 9 : 6,
            height: isUp ? 9 : 6,
            borderRadius:"50%",
            background: isUp ? C.gold : "#555",
            transition:"all 0.1s",
          }}/>
        );
      })}
    </div>
  );
}

// ─── Leave Drill-Down Overlay ───
function LeaveDrillDown({ combos, title, onClose, countOnly=false }) {
  const sorted = [...combos].sort((a,b) => b.left - a.left);
  return (
    <DrillOverlay title={title} onClose={onClose}>
      {sorted.length === 0 ? (
        <div style={{textAlign:"center",padding:40,color:C.muted,fontFamily:"'Oswald',sans-serif"}}>No data yet</div>
      ) : (
        <div style={{display:"flex",flexDirection:"column",gap:8}}>
          {sorted.map(combo => {
            const pct = ((combo.made / combo.left) * 100).toFixed(1);
            return (
              <div key={combo.pins.join(",")} style={{display:"flex",alignItems:"center",background:C.surfaceDeep,borderRadius:12,padding:"6px 16px 6px 12px",border:`1px solid ${C.border}`}}>
                <PinMiniMap standing={combo.pins}/>
                <div style={{marginLeft:"auto",display:"flex",alignItems:"baseline",gap:8}}>
                  {countOnly
                    ? <span style={{fontSize:22,fontWeight:400,color:C.gold,fontFamily:"'Oswald',sans-serif"}}>{combo.left}x</span>
                    : <>
                        <span style={{fontSize:22,fontWeight:400,color:C.gold,fontFamily:"'Oswald',sans-serif"}}>{pct}%</span>
                        <span style={{fontSize:14,color:C.muted}}>({combo.made}/{combo.left})</span>
                      </>
                  }
                </div>
              </div>
            );
          })}
        </div>
      )}
    </DrillOverlay>
  );
}

function GameStatsModule({ games, leagues=[], showGameAvg=false, statsTitle="Date Statistics" }) {
  const [drillDown, setDrillDown] = useState(null);

  if (!games || games.length === 0) return null;

  const scores       = games.map(g => calculateScore(g.frames));
  const total        = scores.reduce((a,b) => a+b, 0);
  const avg          = (total / scores.length).toFixed(1);
  const highGame     = Math.max(...scores);
  const cleanCount   = games.filter(g => isCleanGame(g)).length;
  const seriesGroups = {};
  for (const g of games) {
    const key = g.seriesId || g.id;
    if (!seriesGroups[key]) seriesGroups[key] = [];
    seriesGroups[key].push(g);
  }
  const seriesGroupList = Object.values(seriesGroups);
  const leagueSeriesList = seriesGroupList.filter(s => {
    if (!s.every(g => g.type === "league")) return false;
    const league = leagues.find(l => l.id === s[0].leagueId);
    if (league && s.length < league.gamesPerSeries) return false;
    return true;
  });
  const cleanSeries  = leagueSeriesList.filter(s => s.every(g => isCleanGame(g))).length;
  const highSeries   = seriesGroupList.length > 0
    ? Math.max(...seriesGroupList.map(s => s.reduce((t,g) => t + calculateScore(g.frames), 0)))
    : 0;

  // Average by game position (Game 1, Game 2, …)
  const positionScores = {};
  if (showGameAvg) {
    for (const series of seriesGroupList) {
      const sorted = [...series].sort((a,b) => a.id - b.id);
      sorted.forEach((g,i) => {
        if (!positionScores[i]) positionScores[i] = [];
        positionScores[i].push(calculateScore(g.frames));
      });
    }
  }

  const s            = analyzeFrames(games);
  const firstBallAvg = s.totalFrames > 0 ? (s.firstBallTotal / s.totalFrames).toFixed(2) : "—";
  const makeableOpp  = s.singleOpp + s.multiOpp;
  const makeableMade = s.singleMade + s.multiMade;
  const openPct      = s.totalFrames > 0 ? ((s.openFrames / s.totalFrames) * 100).toFixed(1) : "0.0";

  // Compute strike streaks
  const strikeStreaks = {};
  for (const game of games) {
    const seq = [];
    for (let fi = 0; fi < 9; fi++) seq.push(game.frames[fi].rolls?.[0] === 10);
    const r10 = game.frames[9].rolls || [];
    seq.push(r10[0] === 10);
    if (r10[0] === 10) { seq.push(r10[1] === 10); if (r10[1] === 10) seq.push(r10[2] === 10); }
    let streak = 0;
    for (const isStrike of seq) {
      if (isStrike) { streak++; }
      else { if (streak > 0) { strikeStreaks[streak] = (strikeStreaks[streak]||0)+1; streak=0; } }
    }
    if (streak > 0) strikeStreaks[streak] = (strikeStreaks[streak]||0)+1;
  }

  // Collect per-combination leave data for makeable spares and splits
  const leaveMap = {};
  const splitMap = {};
  for (const game of games) {
    for (let fi = 0; fi < 10; fi++) {
      const frame = game.frames[fi];
      if (!frame.rolls || frame.rolls.length < 1) continue;
      const r1 = frame.rolls[0];
      if (r1 === 10) continue;
      const pinsLeft = frame.pinsLeft || [];
      if (pinsLeft.length === 0) continue;
      const accurate = pinsLeft.length === (10 - r1);
      if (!accurate) continue;
      const split = isSplit(pinsLeft);
      const map = split ? splitMap : leaveMap;
      const key = [...pinsLeft].sort((a,b)=>a-b).join(",");
      if (!map[key]) map[key] = { pins: [...pinsLeft].sort((a,b)=>a-b), left:0, made:0 };
      map[key].left++;
      if (frame.rolls.length >= 2 && r1 + frame.rolls[1] === 10) map[key].made++;
    }
  }
  // Collect open-frame leaves (what was left after ball 1 that wasn't converted)
  const openLeaveMap = {};
  for (const game of games) {
    for (let fi = 0; fi < 10; fi++) {
      const frame = game.frames[fi];
      if (!frame.rolls || frame.rolls.length < 2) continue;
      const r1 = frame.rolls[0], r2 = frame.rolls[1];
      if (r1 === 10 || r1 + r2 === 10) continue; // strike or spare
      const pinsLeft = frame.pinsLeft || [];
      if (pinsLeft.length === 0) continue;
      const accurate = pinsLeft.length === (10 - r1);
      if (!accurate) continue;
      const key = [...pinsLeft].sort((a,b)=>a-b).join(",");
      if (!openLeaveMap[key]) openLeaveMap[key] = { pins: [...pinsLeft].sort((a,b)=>a-b), left:0, made:0 };
      openLeaveMap[key].left++;
    }
  }
  const openCombos = Object.values(openLeaveMap);

  const allCombos    = Object.values(leaveMap);
  const singleCombos = allCombos.filter(c => c.pins.length === 1);
  const multiCombos  = allCombos.filter(c => c.pins.length > 1);
  const splitCombos  = Object.values(splitMap);

  const drillCombos = drillDown === "single" ? singleCombos
    : drillDown === "multi"   ? multiCombos
    : drillDown === "splits"  ? splitCombos
    : drillDown === "opens"   ? openCombos
    : allCombos;
  const drillTitle  = drillDown === "single" ? "Single Pin Spares"
    : drillDown === "multi"   ? "Multi Pin Spares"
    : drillDown === "splits"  ? "Splits"
    : drillDown === "opens"   ? "Open Frames"
    : "Makeable Spares";

  // Drill-down lists (always built, capped at 100)
  const allGamesList = [...games]
    .sort((a,b) => calculateScore(b.frames) - calculateScore(a.frames))
    .slice(0, 100)
    .map(g => ({ score: calculateScore(g.frames), date: g.date, game: g }));
  const allSeriesList = [...seriesGroupList]
    .map(s => {
      const sorted = [...s].sort((a,b) => a.id - b.id);
      return { total: sorted.reduce((t,g) => t + calculateScore(g.frames), 0), date: sorted[0].date, scores: sorted.map(g => calculateScore(g.frames)), games: sorted };
    })
    .sort((a,b) => b.total - a.total)
    .slice(0, 100);

  return (
    <div>
      {drillDown === "strikes" && (
        <StrikeStreakDrillDown streakCounts={strikeStreaks} onClose={()=>setDrillDown(null)}/>
      )}
      {drillDown === "game-avg" && (
        <GameAvgDrillDown positionScores={positionScores} onClose={()=>setDrillDown(null)}/>
      )}
      {drillDown === "high-game" && (
        <GameListDrillDown items={allGamesList} title="All Games" onClose={()=>setDrillDown(null)}/>
      )}
      {drillDown === "high-series" && (
        <SeriesListDrillDown items={allSeriesList} title="All Series" onClose={()=>setDrillDown(null)}/>
      )}
      {drillDown === "clean-games" && (
        <GameListDrillDown items={games.filter(g=>isCleanGame(g)).map(g=>({score:calculateScore(g.frames),date:g.date,game:g})).sort((a,b)=>b.score-a.score)} title="Clean Games" onClose={()=>setDrillDown(null)}/>
      )}
      {drillDown === "clean-series" && (
        <SeriesListDrillDown items={leagueSeriesList
          .filter(s => s.every(g=>isCleanGame(g)))
          .map(s => {
            const sorted = [...s].sort((a,b)=>a.id-b.id);
            return { total: sorted.reduce((t,g)=>t+calculateScore(g.frames),0), date: sorted[0].date, scores: sorted.map(g=>calculateScore(g.frames)), games: sorted };
          })
          .sort((a,b)=>b.total-a.total)
        } title="Clean Series" onClose={()=>setDrillDown(null)}/>
      )}
      {drillDown && !["strikes","game-avg","high-game","high-series","clean-games","clean-series"].includes(drillDown) && (
        <LeaveDrillDown combos={drillCombos} title={drillTitle} onClose={()=>setDrillDown(null)} countOnly={drillDown==="opens"}/>
      )}

      <StatsHeading title={statsTitle} />
      <ListRow label="Average"      value={avg}       sub={`(${games.length} game${games.length>1?"s":""})`} />
      <ListRow label="High Game"    value={highGame}
        onClick={() => setDrillDown("high-game")} />
      <ListRow label="High Series"  value={highSeries}
        onClick={() => setDrillDown("high-series")} />
      <ListRow label="Clean Games"  value={cleanCount}
        onClick={cleanCount > 0 ? () => setDrillDown("clean-games") : undefined} />
      <ListRow label="Clean Series" value={cleanSeries}
        onClick={cleanSeries > 0 ? () => setDrillDown("clean-series") : undefined} />
      {showGameAvg && Object.keys(positionScores).length > 0 && (
        <ListRow label="Average by Game" value="›" valueColor={C.darkGold}
          onClick={() => setDrillDown("game-avg")} />
      )}

      <StatsHeading title="Frame Statistics" />
      <ListRow   label="First Ball Average" value={firstBallAvg} />
      <PctRow    label="Strikes"       made={s.strikes}     opp={s.strikeOpp}
        onClick={s.strikes > 0 ? () => setDrillDown("strikes") : undefined} />
      <PctRow    label="Spares"        made={s.spares}      opp={s.spareOpp}  />
      <PctRow    label="Makeable"      made={makeableMade}  opp={makeableOpp}  indent={1}
        onClick={makeableOpp > 0 ? () => setDrillDown("makeable") : undefined} />
      <PctRow    label="Single Pin"    made={s.singleMade}  opp={s.singleOpp}  indent={2}
        onClick={s.singleOpp > 0 ? () => setDrillDown("single") : undefined} />
      <PctRow    label="Multiple Pin"  made={s.multiMade}   opp={s.multiOpp}   indent={2}
        onClick={s.multiOpp > 0 ? () => setDrillDown("multi") : undefined} />
      <PctRow    label="Splits"        made={s.splitMade}   opp={s.splitOpp}   indent={1}
        onClick={s.splitOpp > 0 ? () => setDrillDown("splits") : undefined} />
      <ListRow   label="Opens"
        value={`${openPct}%`}
        sub={`(${s.openFrames} frame${s.openFrames!==1?"s":""})`}
        valueColor="#c87a50"
        onClick={s.openFrames > 0 ? () => setDrillDown("opens") : undefined}
      />
    </div>
  );
}

// ─── Series Complete ───
function SeriesCompleteView({ activeSeries, onDone }) {
  const [selectedGame, setSelectedGame] = useState(null);
  const scores = activeSeries.completedGames.map(g=>calculateScore(g.frames));
  const total = scores.reduce((a,b)=>a+b,0);

  return (
    <>
    {selectedGame && <GameRecapOverlay game={selectedGame} onClose={()=>setSelectedGame(null)}/>}
    <div style={{padding:"0 16px 80px"}}>
      <div style={{textAlign:"center",marginTop:24,marginBottom:24}}>
        <div style={{fontSize:14,color:"#7ec850",letterSpacing:3,fontFamily:"'Oswald',sans-serif",textTransform:"uppercase",marginBottom:4}}>Series Complete</div>
        <div style={{fontSize:14,color:C.muted,marginBottom:6}}>{activeSeries.league.name}</div>
        <div style={{fontSize:72,fontWeight:700,color:C.gold,fontFamily:"'Oswald',sans-serif",lineHeight:1}}>{total}</div>
        <div style={{fontSize:14,color:C.muted,marginTop:4}}>{activeSeries.league.gamesPerSeries}-game series total</div>
      </div>

      <div style={{display:"flex",gap:8,marginBottom:16}}>
        {scores.map((sc,i)=>(
          <div key={i} onClick={()=>setSelectedGame(activeSeries.completedGames[i])} style={{flex:1,background:C.card,borderRadius:10,padding:"10px 4px",textAlign:"center",border:`1px solid ${C.border}`,cursor:"pointer"}}>
            <div style={{fontSize:14,color:C.muted,marginBottom:3}}>G{i+1}</div>
            <div style={{fontSize:20,fontWeight:700,color:C.cream,fontFamily:"'Oswald',sans-serif"}}>{sc}</div>
          </div>
        ))}
      </div>

      <GameStatsModule games={activeSeries.completedGames} />

      <button style={{...btnPrimary(),marginTop:24}} onClick={onDone}>Done</button>
    </div>
    </>
  );
}

// ─── Open Bowling ───
function OpenSetupView({ games, onStart, onSelectSession, onViewAllStats, onContinueSession }) {
  const sessionMap = {};
  for (const g of games.filter(g => g.type === "open" && g.complete)) {
    const key = g.seriesId || g.id;
    if (!sessionMap[key]) sessionMap[key] = [];
    sessionMap[key].push(g);
  }
  const sessions = Object.values(sessionMap).sort((a,b) => (b[0].seriesId||b[0].id) - (a[0].seriesId||a[0].id));
  const hasHistory = sessions.length > 0;
  const today = new Date().toISOString().split("T")[0];
  const todaySession = sessions.find(s => s[0].date === today);

  return (
    <div style={{padding:"0 16px 80px"}}>
      <div style={{display:"flex",flexDirection:"column",gap:10,marginBottom:20}}>
        <button style={btnPrimary()} onClick={onStart}>Start Session</button>
        {hasHistory && (
          <button style={{...btnSecondary(),fontSize:14,letterSpacing:1}} onClick={onViewAllStats}>All Open Stats</button>
        )}
      </div>
      {sessions.length === 0 ? (
        <div style={{textAlign:"center",padding:32,color:C.muted}}>
          <p style={{fontFamily:"'Oswald',sans-serif"}}>No sessions yet</p>
        </div>
      ) : sessions.map((session, si) => {
        const scores = session.map(g => calculateScore(g.frames));
        const total = scores.reduce((a,b)=>a+b,0);
        const avg = (total / scores.length).toFixed(1);
        return (
          <div key={si} onClick={() => onSelectSession(session)} style={{background:C.card,borderRadius:12,padding:14,border:`1px solid ${C.border}`,marginBottom:10,cursor:"pointer"}}>
            <div style={{display:"flex",justifyContent:"space-between",alignItems:"center"}}>
              <div>
                <div style={{fontSize:14,color:C.muted,marginBottom:4}}>{session[0].date}</div>
                <div style={{fontSize:14,color:C.cream,fontFamily:"'Oswald',sans-serif"}}>
                  {scores.length} game{scores.length!==1?"s":""}
                </div>
              </div>
              <div style={{display:"flex",alignItems:"center",gap:16}}>
                <div style={{textAlign:"right"}}>
                  <div style={{fontSize:14,color:C.muted,letterSpacing:1,marginBottom:2}}>SERIES</div>
                  <div style={{fontSize:18,fontWeight:400,color:C.gold,fontFamily:"'Oswald',sans-serif"}}>{total}</div>
                </div>
                <div style={{textAlign:"right"}}>
                  <div style={{fontSize:14,color:C.muted,letterSpacing:1,marginBottom:2}}>AVERAGE</div>
                  <div style={{fontSize:18,fontWeight:400,color:C.gold,fontFamily:"'Oswald',sans-serif"}}>{avg}</div>
                </div>
                <span style={{fontSize:16,color:C.muted}}>›</span>
              </div>
            </div>
          </div>
        );
      })}
    </div>
  );
}

function OpenSessionNextView({ activeOpenSession, onStartNext, onEnd }) {
  const lastGame = activeOpenSession.completedGames[activeOpenSession.completedGames.length-1];
  const lastScore = calculateScore(lastGame.frames);
  const runningTotal = activeOpenSession.completedGames.reduce((t,g)=>t+calculateScore(g.frames),0);
  const gamesDone = activeOpenSession.completedGames.length;
  return (
    <div style={{padding:"0 16px",textAlign:"center"}}>
      <div style={{marginTop:40,marginBottom:40}}>
        <div style={{fontSize:14,color:C.muted,letterSpacing:3,fontFamily:"'Oswald',sans-serif",textTransform:"uppercase",marginBottom:8}}>
          Game {gamesDone} Complete
        </div>
        <div style={{fontSize:72,fontWeight:700,color:C.gold,fontFamily:"'Oswald',sans-serif",lineHeight:1}}>{lastScore}</div>
        <div style={{fontSize:14,color:C.muted,marginTop:8}}>Session total: <span style={{color:C.cream}}>{runningTotal}</span></div>
      </div>
      <div style={{display:"flex",gap:8,marginBottom:24}}>
        {activeOpenSession.completedGames.map((g,i)=>(
          <div key={i} style={{flex:1,background:C.card,borderRadius:10,padding:"10px 4px",textAlign:"center",border:`1px solid ${C.border}`}}>
            <div style={{fontSize:14,color:C.muted,marginBottom:2}}>G{i+1}</div>
            <div style={{fontSize:18,color:C.cream,fontFamily:"'Oswald',sans-serif",fontWeight:700}}>{calculateScore(g.frames)}</div>
          </div>
        ))}
      </div>
      <div style={{display:"flex",flexDirection:"column",gap:10}}>
        <button style={btnPrimary()} onClick={onStartNext}>Bowl Another Game</button>
        <button style={{...btnSecondary(),fontSize:14,letterSpacing:1}} onClick={onEnd}>End Session</button>
      </div>
    </div>
  );
}

// ─── Shared game detail overlay ───
function GameDetailOverlay({ game, gameNumber, sessionTotal, sessionAvg, onClose, onFrameEdit }) {
  const [localGame, setLocalGame] = useState(game);
  const [editFi, setEditFi]       = useState(null);
  const [editStep, setEditStep]   = useState(0);
  const [editPins, setEditPins]   = useState([1,2,3,4,5,6,7,8,9,10]);
  const [editData, setEditData]   = useState({ rolls:[], pinsAfterFirst:[1,2,3,4,5,6,7,8,9,10] });

  useEffect(() => { setLocalGame(game); }, [game]);

  const score = calculateScore(localGame.frames);

  const startEdit = (fi) => {
    const frame = localGame.frames[fi];
    const wasStrike = frame?.rolls?.[0] === 10;
    const leave = wasStrike ? [] : (frame?.pinsAfterFirst?.length > 0 ? frame.pinsAfterFirst : [1,2,3,4,5,6,7,8,9,10]);
    setEditFi(fi); setEditStep(0); setEditPins(leave);
    setEditData({ rolls:[], pinsAfterFirst:[1,2,3,4,5,6,7,8,9,10] });
  };

  const cancelEdit = () => { setEditFi(null); setEditStep(0); setEditPins([1,2,3,4,5,6,7,8,9,10]); setEditData({ rolls:[], pinsAfterFirst:[1,2,3,4,5,6,7,8,9,10] }); };

  const togglePin = (pinId) => setEditPins(prev => prev.includes(pinId) ? prev.filter(p=>p!==pinId) : [...prev,pinId].sort((a,b)=>a-b));

  const commitEdit = (fi, data) => {
    const ng = JSON.parse(JSON.stringify(localGame));
    ng.frames[fi].rolls = data.rolls;
    ng.frames[fi].pinsLeft = data.pinsLeft || [];
    ng.frames[fi].pinsAfterFirst = data.pinsAfterFirst;
    ng.frames[fi].pinsAfterSecond = data.pinsAfterSecond;
    setLocalGame(ng);
    onFrameEdit(ng);
    cancelEdit();
  };

  const updateScorecard = (fi, rolls, pinsAfterFirst) => {
    setLocalGame(prev => {
      const ng = JSON.parse(JSON.stringify(prev));
      ng.frames[fi].rolls = rolls;
      if (pinsAfterFirst !== undefined) ng.frames[fi].pinsAfterFirst = pinsAfterFirst;
      return ng;
    });
  };

  const recordRoll = (overridePins) => {
    const pins = overridePins !== undefined ? overridePins : editPins;
    const allPins = editStep === 0 ? [1,2,3,4,5,6,7,8,9,10] : editData.pinsAfterFirst;
    const knocked = allPins.filter(p => !pins.includes(p)).length;
    const newRolls = [...editData.rolls, knocked];
    const newData = { ...editData, rolls: newRolls };

    if (editFi < 9) {
      if (editStep === 0) {
        if (knocked === 10) {
          commitEdit(editFi, { ...newData, pinsLeft:[] });
        } else {
          newData.pinsAfterFirst = [...editPins]; newData.pinsLeft = [...editPins];
          updateScorecard(editFi, newRolls, [...editPins]);
          setEditData(newData); setEditStep(1);
          const frame = localGame.frames[editFi];
          const ball2 = frame?.pinsAfterSecond != null ? frame.pinsAfterSecond.filter(p=>editPins.includes(p)) : [...editPins];
          setEditPins(ball2);
        }
      } else { newData.pinsAfterSecond = [...pins]; commitEdit(editFi, newData); }
    } else {
      if (editStep === 0) {
        if (knocked === 10) { newData.pinsAfterFirst=[1,2,3,4,5,6,7,8,9,10]; setEditPins([1,2,3,4,5,6,7,8,9,10]); }
        else { newData.pinsAfterFirst=[...editPins]; }
        updateScorecard(editFi, newRolls);
        setEditData(newData); setEditStep(1);
      } else if (editStep === 1) {
        if (newRolls[0]===10||newRolls[0]+knocked>=10) {
          const fresh=(knocked===10)||(newRolls[0]!==10&&newRolls[0]+knocked===10);
          if(fresh){newData.pinsAfterFirst=[1,2,3,4,5,6,7,8,9,10];setEditPins([1,2,3,4,5,6,7,8,9,10]);}
          else{newData.pinsAfterFirst=[...editPins];}
          updateScorecard(editFi, newRolls);
          setEditData(newData); setEditStep(2);
        } else { commitEdit(editFi, newData); }
      } else { commitEdit(editFi, newData); }
    }
  };

  return (
    <div style={{position:"fixed",top:0,left:0,right:0,bottom:0,background:C.bg,zIndex:300,overflowY:"auto",display:"flex",flexDirection:"column"}}>
      <div style={{position:"relative",display:"flex",alignItems:"center",padding:"16px 16px 0",flexShrink:0}}>
        {editFi !== null
          ? <button style={{background:"none",border:"none",color:C.muted,cursor:"pointer",fontSize:16,padding:0,fontFamily:"'Oswald',sans-serif"}} onClick={cancelEdit}>✕ Cancel</button>
          : <button style={{background:"none",border:"none",color:C.gold,cursor:"pointer",fontSize:16,padding:0,fontFamily:"'Oswald',sans-serif"}} onClick={onClose}>← Back</button>
        }
        <span style={{position:"absolute",left:0,right:0,textAlign:"center",fontSize:17,color:C.muted,textTransform:"uppercase",letterSpacing:2,pointerEvents:"none"}}>
          {editFi !== null ? `Frame ${editFi+1} · Ball ${editStep+1}` : `Game ${gameNumber}`}
        </span>
      </div>
      <div style={{padding:"0 5px",marginTop:12,flexShrink:0}}>
        <Scorecard frames={localGame.frames} complete={localGame.complete} currentFrame={10}
          onFrameClick={editFi === null ? fi => startEdit(fi) : undefined}/>
      </div>

      {editFi !== null ? (
        <div style={{padding:"20px 16px 24px"}}>
          <PinDiagram standing={editPins} onToggle={togglePin} disabled={false}/>
          <div style={{marginTop:24,display:"flex",gap:8}}>
            <button style={{...btnSecondary(),flex:1,padding:"12px 8px",fontSize:15}} onClick={()=>recordRoll([])}>{editStep===0||editPins.length===10?"Strike":"Spare"}</button>
            <button style={{...btnPrimary(),flex:1,padding:"12px 8px",fontSize:15}} onClick={()=>recordRoll()}>
              {editFi<9?(editStep===0?"Next":"Confirm"):(editStep<2?"Next":"Confirm")}
            </button>
          </div>
        </div>
      ) : (
        <div style={{padding:"24px 16px",textAlign:"center",flexShrink:0}}>
          <div style={{fontSize:13,color:C.muted,letterSpacing:3,textTransform:"uppercase",marginBottom:6}}>Game {gameNumber} Complete</div>
          <div style={{fontSize:72,fontWeight:700,color:C.gold,fontFamily:"'Oswald',sans-serif",lineHeight:1,marginBottom:16}}>{score}</div>
          <div style={{display:"flex",justifyContent:"center",gap:32}}>
            <div>
              <div style={{fontSize:12,color:C.muted,letterSpacing:2,textTransform:"uppercase",marginBottom:2}}>Session Total</div>
              <div style={{fontSize:22,fontWeight:300,color:C.cream,fontFamily:"'Oswald',sans-serif"}}>{sessionTotal}</div>
            </div>
            <div>
              <div style={{fontSize:12,color:C.muted,letterSpacing:2,textTransform:"uppercase",marginBottom:2}}>Average</div>
              <div style={{fontSize:22,fontWeight:300,color:C.cream,fontFamily:"'Oswald',sans-serif"}}>{sessionAvg}</div>
            </div>
          </div>
        </div>
      )}
    </div>
  );
}

function OpenSessionDetailView({ session, onViewStats, onNewGame, onFrameEdit }) {
  const [selectedGame, setSelectedGame] = useState(null);
  const scores = session.map(g => calculateScore(g.frames));
  const total  = scores.reduce((a,b)=>a+b,0);
  const avg    = (total / scores.length).toFixed(1);
  const today  = new Date().toISOString().split("T")[0];
  const isToday = session[0].date === today;

  if (selectedGame) {
    const gi = session.findIndex(g => g.id === selectedGame.id);
    return <GameDetailOverlay game={selectedGame} gameNumber={gi+1} sessionTotal={total} sessionAvg={avg} onClose={()=>setSelectedGame(null)} onFrameEdit={onFrameEdit}/>;
  }

  return (
    <div style={{padding:"0 16px 80px"}}>
      <div style={{textAlign:"center",marginBottom:20,marginTop:8}}>
        <div style={{fontSize:14,color:C.muted,marginBottom:4}}>{session[0].date}</div>
        <div style={{fontSize:64,fontWeight:700,color:C.gold,fontFamily:"'Oswald',sans-serif",lineHeight:1}}>{total}</div>
        <div style={{fontSize:14,color:C.muted,marginTop:4}}>{session.length}-game session · avg {avg}</div>
      </div>
      <div style={{display:"flex",flexDirection:"column",gap:10,marginBottom:20}}>
        {isToday && <button style={btnPrimary()} onClick={onNewGame}>New Game</button>}
        <button style={{...btnSecondary(),fontSize:14,letterSpacing:2}} onClick={onViewStats}>Session Stats</button>
      </div>
      <div style={{background:C.card,borderRadius:12,border:`1px solid ${C.border}`,overflow:"hidden"}}>
        {session.map((game, gi) => (
          <div key={gi} onClick={()=>setSelectedGame(game)} style={{display:"flex",justifyContent:"space-between",alignItems:"center",padding:"14px 16px",borderBottom:gi<session.length-1?`1px solid ${C.border}`:"none",cursor:"pointer"}}>
            <span style={{fontSize:14,color:C.muted,textTransform:"uppercase",letterSpacing:1,fontFamily:"'Oswald',sans-serif"}}>Game {gi+1}</span>
            <div style={{display:"flex",alignItems:"center",gap:12}}>
              <span style={{fontSize:22,fontWeight:300,color:C.gold,fontFamily:"'Oswald',sans-serif"}}>{scores[gi]}</span>
              <span style={{fontSize:14,color:C.muted}}>›</span>
            </div>
          </div>
        ))}
      </div>
    </div>
  );
}

// ─── Tournaments ───
function TournamentsView({ games, onStart, onSelectSession, onViewAllStats, onContinueSession }) {
  const sessionMap = {};
  for (const g of games.filter(g => g.type === "tournament" && g.complete)) {
    const key = g.seriesId || g.id;
    if (!sessionMap[key]) sessionMap[key] = [];
    sessionMap[key].push(g);
  }
  const sessions = Object.values(sessionMap).sort((a,b) => (b[0].seriesId||b[0].id) - (a[0].seriesId||a[0].id));
  const today = new Date().toISOString().split("T")[0];

  return (
    <div style={{padding:"0 16px 80px"}}>
      <div style={{display:"flex",flexDirection:"column",gap:10,marginBottom:20}}>
        <button style={btnPrimary()} onClick={onStart}>Start Tournament</button>
        {sessions.length > 0 && (
          <button style={{...btnSecondary(),fontSize:14,letterSpacing:1}} onClick={onViewAllStats}>All Tournament Stats</button>
        )}
      </div>
      {sessions.length === 0 ? (
        <div style={{textAlign:"center",padding:32,color:C.muted}}>
          <p style={{fontFamily:"'Oswald',sans-serif"}}>No tournaments yet</p>
        </div>
      ) : sessions.map((session, si) => {
        const scores = session.map(g => calculateScore(g.frames));
        const total = scores.reduce((a,b)=>a+b,0);
        const avg = (total / scores.length).toFixed(1);
        const name = session[0].leagueName || "Tournament";
        return (
          <div key={si} onClick={() => onSelectSession(session)}
            style={{background:C.card,borderRadius:12,padding:14,border:`1px solid ${C.border}`,marginBottom:10,cursor:"pointer"}}>
            <div style={{display:"flex",justifyContent:"space-between",alignItems:"center"}}>
              <div>
                <div style={{fontFamily:"'Oswald',sans-serif",fontSize:17,color:C.gold,fontWeight:600,marginBottom:3}}>{name}</div>
                <div style={{fontSize:14,color:C.cream,fontFamily:"'Oswald',sans-serif"}}>{scores.length} game{scores.length!==1?"s":""}</div>
              </div>
              <div style={{display:"flex",alignItems:"center",gap:16}}>
                <div style={{textAlign:"right"}}>
                  <div style={{fontSize:14,color:C.muted,letterSpacing:1,marginBottom:2}}>SERIES</div>
                  <div style={{fontSize:18,fontWeight:400,color:C.gold,fontFamily:"'Oswald',sans-serif"}}>{total}</div>
                </div>
                <div style={{textAlign:"right"}}>
                  <div style={{fontSize:14,color:C.muted,letterSpacing:1,marginBottom:2}}>AVERAGE</div>
                  <div style={{fontSize:18,fontWeight:400,color:C.gold,fontFamily:"'Oswald',sans-serif"}}>{avg}</div>
                </div>
                <span style={{fontSize:16,color:C.muted}}>›</span>
              </div>
            </div>
          </div>
        );
      })}
    </div>
  );
}

function TournamentStartView({ onStart }) {
  const [name, setName] = useState("");
  return (
    <div style={{padding:"0 16px 80px"}}>
      <div style={{marginBottom:28}}>
        <span style={label()}>Tournament Name</span>
        <input value={name} onChange={e=>setName(e.target.value)}
          placeholder="e.g. City Open 2026" style={inputStyle()}/>
      </div>
      <button style={{...btnPrimary(), opacity: name.trim()?1:0.4}}
        onClick={()=>{ if(name.trim()) onStart(name.trim()); }}>
        Start Tournament
      </button>
    </div>
  );
}

function TournamentSessionNextView({ activeTournamentSession, onStartNext, onEnd }) {
  const lastGame = activeTournamentSession.completedGames[activeTournamentSession.completedGames.length-1];
  const lastScore = calculateScore(lastGame.frames);
  const runningTotal = activeTournamentSession.completedGames.reduce((t,g)=>t+calculateScore(g.frames),0);
  const gamesDone = activeTournamentSession.completedGames.length;
  return (
    <div style={{padding:"0 16px",textAlign:"center"}}>
      <div style={{marginTop:24,marginBottom:8}}>
        <div style={{fontSize:14,color:C.gold,fontFamily:"'Oswald',sans-serif",letterSpacing:2,fontWeight:600}}>{activeTournamentSession.name}</div>
      </div>
      <div style={{marginBottom:40}}>
        <div style={{fontSize:14,color:C.muted,letterSpacing:3,fontFamily:"'Oswald',sans-serif",textTransform:"uppercase",marginBottom:8}}>Game {gamesDone} Complete</div>
        <div style={{fontSize:72,fontWeight:700,color:C.gold,fontFamily:"'Oswald',sans-serif",lineHeight:1}}>{lastScore}</div>
        <div style={{fontSize:14,color:C.muted,marginTop:8}}>Running total: <span style={{color:C.cream}}>{runningTotal}</span></div>
      </div>
      <div style={{display:"flex",gap:8,marginBottom:24}}>
        {activeTournamentSession.completedGames.map((g,i)=>(
          <div key={i} style={{flex:1,background:C.card,borderRadius:10,padding:"10px 4px",textAlign:"center",border:`1px solid ${C.border}`}}>
            <div style={{fontSize:14,color:C.muted,marginBottom:2}}>G{i+1}</div>
            <div style={{fontSize:18,color:C.cream,fontFamily:"'Oswald',sans-serif",fontWeight:700}}>{calculateScore(g.frames)}</div>
          </div>
        ))}
      </div>
      <div style={{display:"flex",flexDirection:"column",gap:10}}>
        <button style={btnPrimary()} onClick={onStartNext}>New Game</button>
        <button style={{...btnSecondary(),fontSize:14,letterSpacing:1}} onClick={onEnd}>End Tournament</button>
      </div>
    </div>
  );
}

function TournamentSessionDetailView({ session, onViewStats, onNewGame, onFrameEdit }) {
  const [selectedGame, setSelectedGame] = useState(null);
  const scores = session.map(g => calculateScore(g.frames));
  const total  = scores.reduce((a,b)=>a+b,0);
  const avg    = (total / scores.length).toFixed(1);
  const today  = new Date().toISOString().split("T")[0];
  const isToday = session[0].date === today;
  const name = session[0].leagueName || "Tournament";

  if (selectedGame) {
    const gi = session.findIndex(g => g.id === selectedGame.id);
    return <GameDetailOverlay game={selectedGame} gameNumber={gi+1} sessionTotal={total} sessionAvg={avg} onClose={()=>setSelectedGame(null)} onFrameEdit={onFrameEdit}/>;
  }

  return (
    <div style={{padding:"0 16px 80px"}}>
      <div style={{textAlign:"center",marginBottom:20,marginTop:8}}>
        <div style={{fontFamily:"'Oswald',sans-serif",fontSize:20,color:C.gold,fontWeight:600,marginBottom:4}}>{name}</div>
        <div style={{fontSize:14,color:C.muted,marginBottom:4}}>{session[0].date}</div>
        <div style={{fontSize:64,fontWeight:700,color:C.gold,fontFamily:"'Oswald',sans-serif",lineHeight:1}}>{total}</div>
        <div style={{fontSize:14,color:C.muted,marginTop:4}}>{session.length}-game total · avg {avg}</div>
      </div>
      <div style={{display:"flex",flexDirection:"column",gap:10,marginBottom:20}}>
        {isToday && <button style={btnPrimary()} onClick={onNewGame}>New Game</button>}
        <button style={{...btnSecondary(),fontSize:14,letterSpacing:2}} onClick={onViewStats}>Tournament Stats</button>
      </div>
      <div style={{background:C.card,borderRadius:12,border:`1px solid ${C.border}`,overflow:"hidden"}}>
        {session.map((game, gi) => (
          <div key={gi} onClick={()=>setSelectedGame(game)} style={{display:"flex",justifyContent:"space-between",alignItems:"center",padding:"14px 16px",borderBottom:gi<session.length-1?`1px solid ${C.border}`:"none",cursor:"pointer"}}>
            <span style={{fontSize:14,color:C.muted,textTransform:"uppercase",letterSpacing:1,fontFamily:"'Oswald',sans-serif"}}>Game {gi+1}</span>
            <div style={{display:"flex",alignItems:"center",gap:12}}>
              <span style={{fontSize:22,fontWeight:300,color:C.gold,fontFamily:"'Oswald',sans-serif"}}>{scores[gi]}</span>
              <span style={{fontSize:14,color:C.muted}}>›</span>
            </div>
          </div>
        ))}
      </div>
    </div>
  );
}

// ─── Statistics ───
function StatsView({ games, leagues }) {
  const [activeFilters, setActiveFilters] = useState(null);
  const [showResults, setShowResults] = useState(false);

  useEffect(() => {
    if (activeFilters === null && leagues.length > 0) {
      setActiveFilters(new Set(leagues.map(l => "league-" + l.id)));
    }
  }, [leagues]);

  const tournamentNames = [...new Set(
    games.filter(g => g.type === "tournament" && g.complete).map(g => g.leagueName)
  )].filter(Boolean);

  const filters = activeFilters ?? new Set();

  const toggleFilter = (id) => {
    setActiveFilters(prev => {
      const next = new Set(prev ?? new Set());
      if (next.has(id)) next.delete(id); else next.add(id);
      return next;
    });
  };

  const filteredGames = games.filter(g => {
    if (!g.complete) return false;
    if (g.type === "league"     && filters.has("league-" + g.leagueId))       return true;
    if (g.type === "tournament" && filters.has("tournament-" + g.leagueName)) return true;
    return false;
  });

  const hasAnyGames = games.some(g => g.complete && (g.type === "league" || g.type === "tournament"));

  if (!hasAnyGames) return (
    <div style={{textAlign:"center",padding:40,color:C.muted}}>
      <p style={{fontSize:18,fontFamily:"'Oswald',sans-serif"}}>No completed games yet</p>
      <p style={{fontSize:14,marginTop:8}}>Complete league or tournament games to see statistics</p>
    </div>
  );

  if (showResults) return (
    <div style={{padding:"0 16px 80px"}}>
      <button onClick={()=>setShowResults(false)} style={{...btnSecondary(),fontSize:14,letterSpacing:1,marginBottom:20,marginTop:8}}>
        ‹ Change Filters
      </button>
      <GameStatsModule games={filteredGames} leagues={leagues} showGameAvg={false} statsTitle="Combined Statistics"/>
    </div>
  );

  const SelectRow = ({ id, name, sub }) => {
    const active = filters.has(id);
    return (
      <div onClick={()=>toggleFilter(id)} style={{
        display:"flex", alignItems:"center", justifyContent:"space-between",
        background:C.card, borderRadius:12, padding:"14px 16px",
        border:`1px solid ${active ? C.gold+"55" : C.border}`,
        marginBottom:10, cursor:"pointer",
      }}>
        <div>
          <div style={{fontFamily:"'Oswald',sans-serif",fontSize:16,color:active?C.gold:C.cream,fontWeight:600}}>{name}</div>
          {sub && <div style={{fontSize:14,color:C.muted,marginTop:3}}>{sub}</div>}
        </div>
        <div style={{
          width:22, height:22, borderRadius:"50%", flexShrink:0,
          border:`2px solid ${active ? C.gold : C.border}`,
          background: active ? C.gold : "transparent",
          display:"flex", alignItems:"center", justifyContent:"center",
        }}>
          {active && <span style={{fontSize:14,color:C.btnText,fontWeight:900,lineHeight:1}}>✓</span>}
        </div>
      </div>
    );
  };

  return (
    <div style={{padding:"0 16px 80px"}}>
      {leagues.length > 0 && (
        <div style={{marginTop:8,marginBottom:20}}>
          <div style={{fontSize:14,color:C.muted,letterSpacing:2,textTransform:"uppercase",marginBottom:10,fontFamily:"'Oswald',sans-serif"}}>Leagues</div>
          {leagues.map(l => {
            const count = games.filter(g=>g.leagueId===l.id&&g.complete).length;
            return <SelectRow key={l.id} id={"league-"+l.id} name={l.name} sub={`${count} game${count!==1?"s":""}`}/>;
          })}
        </div>
      )}

      {tournamentNames.length > 0 && (
        <div style={{marginBottom:20}}>
          <div style={{fontSize:14,color:C.muted,letterSpacing:2,textTransform:"uppercase",marginBottom:10,fontFamily:"'Oswald',sans-serif"}}>Tournaments</div>
          {tournamentNames.map(name => {
            const count = games.filter(g=>g.type==="tournament"&&g.leagueName===name&&g.complete).length;
            return <SelectRow key={name} id={"tournament-"+name} name={name} sub={`${count} game${count!==1?"s":""}`}/>;
          })}
        </div>
      )}

      <button style={{...btnPrimary(), opacity: filters.size > 0 ? 1 : 0.4}}
        onClick={()=>{ if(filters.size > 0) setShowResults(true); }}>
        View Stats
      </button>
    </div>
  );
}

// ─── Settings ───
function SettingsView({ onResetData, theme, onThemeChange, onSignOut }) {
  const isDark = theme === "dark";
  return (
    <div style={{padding:"0 16px 80px"}}>
      <div style={{background:C.card,borderRadius:12,padding:16,border:`1px solid ${C.border}`,marginBottom:16}}>
        <h3 style={{fontSize:14,color:C.gold,marginBottom:4,fontFamily:"'Oswald',sans-serif",textTransform:"uppercase",letterSpacing:2}}>Appearance</h3>
        <p style={{fontSize:14,color:C.muted,marginBottom:14,lineHeight:1.6}}>Choose your preferred colour theme.</p>
        <div style={{display:"flex",gap:10}}>
          <button
            style={{...btnPrimary(),flex:1,padding:"10px 16px",fontSize:14,opacity:isDark?1:0.5,border:isDark?`2px solid ${C.gold}`:"2px solid transparent"}}
            onClick={()=>onThemeChange("dark")}>
            Dark
          </button>
          <button
            style={{...btnPrimary(),flex:1,padding:"10px 16px",fontSize:14,opacity:!isDark?1:0.5,border:!isDark?`2px solid ${C.gold}`:"2px solid transparent"}}
            onClick={()=>onThemeChange("light")}>
            Light
          </button>
        </div>
      </div>
      <div style={{background:C.card,borderRadius:12,padding:16,border:`1px solid ${C.border}`,marginBottom:16}}>
        <h3 style={{fontSize:14,color:C.gold,marginBottom:4,fontFamily:"'Oswald',sans-serif",textTransform:"uppercase",letterSpacing:2}}>Data</h3>
        <p style={{fontSize:14,color:C.muted,marginBottom:14,lineHeight:1.6}}>All game data is stored locally on this device.</p>
        <button style={{...btnSecondary(),border:`1px solid #3a2020`,color:"#8a4a4a",padding:"10px 20px",fontSize:14}} onClick={onResetData}>
          Reset All Data
        </button>
      </div>
      <div style={{background:C.card,borderRadius:12,padding:16,border:`1px solid ${C.border}`,marginBottom:16}}>
        <h3 style={{fontSize:14,color:C.gold,marginBottom:4,fontFamily:"'Oswald',sans-serif",textTransform:"uppercase",letterSpacing:2}}>About</h3>
        <p style={{fontSize:14,color:C.muted,lineHeight:1.6}}>PinTracker — Bowling Scorekeeper<br/>pintracker.ca</p>
      </div>
      <button style={{...btnSecondary(),width:"100%",padding:"12px 16px",fontSize:14,letterSpacing:1,color:"#8a4a4a",border:"1px solid #3a2020"}} onClick={onSignOut}>
        Sign Out
      </button>
    </div>
  );
}

// ─── Help ───
function HelpView() {
  const section = (title, children) => (
    <div style={{background:C.card,borderRadius:12,padding:16,border:`1px solid ${C.border}`,marginBottom:16}}>
      <h3 style={{fontSize:14,color:C.gold,marginBottom:10,fontFamily:"'Oswald',sans-serif",textTransform:"uppercase",letterSpacing:2}}>{title}</h3>
      {children}
    </div>
  );
  const p = (text) => <p style={{fontSize:14,color:C.muted,lineHeight:1.7,margin:"0 0 8px"}}>{text}</p>;
  const li = (text) => <li style={{fontSize:14,color:C.muted,lineHeight:1.7,marginBottom:4}}>{text}</li>;
  return (
    <div style={{padding:"0 16px 80px"}}>
      {section("Leagues", <>
        {p("Leagues let you track your bowling across a full season.")}
        <ul style={{paddingLeft:18,margin:0}}>
          {li("Tap New League to create a league and set the number of games per series.")}
          {li("Tap Bowl Series to start a new series within that league.")}
          {li("After each game you can continue to the next game in the series or stop early.")}
          {li("Tap any past series to view the scorecard for each game.")}
          {li("Use League Stats to see your average, high game, high series, spare and split percentages.")}
        </ul>
      </>)}
      {section("Tournaments", <>
        {p("Tournaments track a set of games bowled at a specific event.")}
        <ul style={{paddingLeft:18,margin:0}}>
          {li("Tap Start Tournament and give your tournament a name.")}
          {li("Bowl as many games as needed — each game is added to the session total.")}
          {li("Tap End Session when finished to save the tournament.")}
          {li("View past tournaments and their full stats from the Tournaments tab.")}
        </ul>
      </>)}
      {section("Open Bowling", <>
        {p("Open Bowling is for casual sessions outside of leagues or tournaments.")}
        <ul style={{paddingLeft:18,margin:0}}>
          {li("Start a session and bowl as many games as you like.")}
          {li("Your running total and average update after each game.")}
          {li("Tap End Session to save or continue bowling.")}
          {li("All open sessions are saved and viewable from the Open Bowling tab.")}
        </ul>
      </>)}
      {section("Scoring", <>
        {p("After each roll, tap the pins that were knocked down on the pin diagram.")}
        <ul style={{paddingLeft:18,margin:0}}>
          {li("Strike — tap Strike or knock all 10 on the first ball.")}
          {li("Spare — tap Spare or knock all remaining pins on the second ball.")}
          {li("A split indicator (S) appears when your first ball leave qualifies as a split.")}
          {li("To correct a frame, tap it on the scorecard and re-enter the rolls.")}
          {li("If you leave the app mid-game, a Game In Progress banner appears on the home screen — tap Resume to continue or Abandon to discard.")}
        </ul>
      </>)}
      {section("Statistics", <>
        {p("Statistics are calculated across all completed games.")}
        <ul style={{paddingLeft:18,margin:0}}>
          {li("View your average, high game, strike rate, and spare percentage.")}
          {li("Spare and split breakdowns show your conversion rates by specific leave.")}
          {li("Stats are available per league as well as across all game types.")}
        </ul>
      </>)}
      {section("Settings", <>
        <ul style={{paddingLeft:18,margin:0}}>
          {li("Switch between Dark and Light theme under Appearance.")}
          {li("All data is stored locally on your device — nothing is sent to a server.")}
          {li("Use Reset All Data to clear all games and leagues. This cannot be undone.")}
        </ul>
      </>)}
      {section("Contact", <>
        {p("Need help or have a suggestion?")}
        <p style={{fontSize:14,lineHeight:1.7,margin:0}}>
          <span style={{color:C.muted}}>Email: </span>
          <a href="mailto:davewebbdesigns@gmail.com" style={{color:C.gold,textDecoration:"none"}}>davewebbdesigns@gmail.com</a>
        </p>
      </>)}
    </div>
  );
}

// ─── Auth ───
function AuthView({ onAuth }) {
  const [mode, setMode]       = useState("login"); // "login" | "signup"
  const [email, setEmail]     = useState("");
  const [password, setPassword] = useState("");
  const [error, setError]     = useState("");
  const [loading, setLoading] = useState(false);

  const handleSubmit = async () => {
    setError(""); setLoading(true);
    let result;
    if (mode === "login") {
      result = await supabase.auth.signInWithPassword({ email, password });
    } else {
      result = await supabase.auth.signUp({ email, password });
    }
    setLoading(false);
    if (result.error) { setError(result.error.message); return; }
    if (mode === "signup" && !result.data.session) {
      setError("Check your email to confirm your account.");
      return;
    }
    onAuth(result.data.user);
  };

  const handleGoogle = async () => {
    setError("");
    const { error } = await supabase.auth.signInWithOAuth({
      provider: "google",
      options: { redirectTo: window.location.origin },
    });
    if (error) setError(error.message);
  };

  return (
    <div style={{
      minHeight:"100vh", display:"flex", alignItems:"center", justifyContent:"center",
      background:`linear-gradient(180deg,${C.bg} 0%,${C.card} 100%)`,
      padding:"0 24px",
    }}>
      <div style={{width:"100%", maxWidth:380}}>
        <div style={{textAlign:"center", marginBottom:32}}>
          <h1 style={{fontFamily:"'Playfair Display',serif",fontSize:32,fontWeight:900,margin:"0 0 8px",
            background:`linear-gradient(145deg,${C.cream},${C.gold})`,WebkitBackgroundClip:"text",WebkitTextFillColor:"transparent"}}>
            PinTracker
          </h1>
          <p style={{fontSize:13,letterSpacing:4,color:C.muted,textTransform:"uppercase",margin:0}}>Bowling Scorekeeper</p>
        </div>

        <div style={{background:C.card,borderRadius:16,padding:24,border:`1px solid ${C.border}`}}>
          <div style={{display:"flex",marginBottom:20,background:C.bg,borderRadius:8,padding:3}}>
            {["login","signup"].map(m => (
              <button key={m} onClick={()=>{setMode(m);setError("");}}
                style={{flex:1,padding:"8px",border:"none",borderRadius:6,cursor:"pointer",
                  fontFamily:"'Oswald',sans-serif",fontSize:13,letterSpacing:1,textTransform:"uppercase",
                  background:mode===m?C.gold:"transparent",
                  color:mode===m?C.btnText:C.muted,
                  transition:"all 0.2s",
                }}>
                {m === "login" ? "Sign In" : "Sign Up"}
              </button>
            ))}
          </div>

          <div style={{marginBottom:14}}>
            <div style={{fontSize:12,color:C.muted,letterSpacing:1,marginBottom:6,textTransform:"uppercase"}}>Email</div>
            <input
              type="email" value={email} onChange={e=>setEmail(e.target.value)}
              style={{width:"100%",background:C.bg,border:`1px solid ${C.border}`,borderRadius:8,
                padding:"10px 12px",color:C.text,fontSize:15,fontFamily:"'Oswald',sans-serif",
                outline:"none",boxSizing:"border-box"}}
              placeholder="you@example.com"
            />
          </div>

          <div style={{marginBottom:20}}>
            <div style={{fontSize:12,color:C.muted,letterSpacing:1,marginBottom:6,textTransform:"uppercase"}}>Password</div>
            <input
              type="password" value={password} onChange={e=>setPassword(e.target.value)}
              onKeyDown={e=>e.key==="Enter"&&handleSubmit()}
              style={{width:"100%",background:C.bg,border:`1px solid ${C.border}`,borderRadius:8,
                padding:"10px 12px",color:C.text,fontSize:15,fontFamily:"'Oswald',sans-serif",
                outline:"none",boxSizing:"border-box"}}
              placeholder="••••••••"
            />
          </div>

          {error&&<div style={{fontSize:13,color:"#c85050",marginBottom:14,lineHeight:1.5}}>{error}</div>}

          <button onClick={handleSubmit} disabled={loading}
            style={{...btnPrimary(),width:"100%",padding:"12px",fontSize:15,marginBottom:12,opacity:loading?0.6:1}}>
            {loading ? "Please wait…" : mode === "login" ? "Sign In" : "Create Account"}
          </button>

          <div style={{display:"flex",alignItems:"center",gap:10,marginBottom:12}}>
            <div style={{flex:1,height:1,background:C.border}}/>
            <span style={{fontSize:12,color:C.muted}}>OR</span>
            <div style={{flex:1,height:1,background:C.border}}/>
          </div>

          <button onClick={handleGoogle}
            style={{...btnSecondary(),width:"100%",padding:"11px",fontSize:14,display:"flex",alignItems:"center",justifyContent:"center",gap:10}}>
            <svg width="18" height="18" viewBox="0 0 18 18">
              <path fill="#4285F4" d="M17.64 9.2c0-.637-.057-1.251-.164-1.84H9v3.481h4.844c-.209 1.125-.843 2.078-1.796 2.716v2.259h2.908c1.702-1.567 2.684-3.875 2.684-6.615z"/>
              <path fill="#34A853" d="M9 18c2.43 0 4.467-.806 5.956-2.184l-2.908-2.259c-.806.54-1.837.86-3.048.86-2.344 0-4.328-1.584-5.036-3.711H.957v2.332A8.997 8.997 0 0 0 9 18z"/>
              <path fill="#FBBC05" d="M3.964 10.706A5.41 5.41 0 0 1 3.682 9c0-.593.102-1.17.282-1.706V4.962H.957A8.996 8.996 0 0 0 0 9c0 1.452.348 2.827.957 4.038l3.007-2.332z"/>
              <path fill="#EA4335" d="M9 3.58c1.321 0 2.508.454 3.44 1.345l2.582-2.58C13.463.891 11.426 0 9 0A8.997 8.997 0 0 0 .957 4.962L3.964 6.294C4.672 4.169 6.656 3.58 9 3.58z"/>
            </svg>
            Continue with Google
          </button>
        </div>
      </div>
    </div>
  );
}

// ─── Main App ───
export default function BowlingApp() {
  const [view, setView]                 = useState("home");
  const [leagues, setLeagues]           = useState([]);
  const [games, setGames]               = useState([]);
  const [currentGame, setCurrentGame]   = useState(null);
  const [currentFrame, setCurrentFrame] = useState(0);
  const [currentRoll, setCurrentRoll]   = useState(0);
  const [standingPins, setStandingPins] = useState([1,2,3,4,5,6,7,8,9,10]);
  const [activeSeries, setActiveSeries]         = useState(null);
  const [activeOpenSession, setActiveOpenSession] = useState(null);
  const [activeTournamentSession, setActiveTournamentSession] = useState(null);
  const [selectedTournamentSession, setSelectedTournamentSession] = useState(null);
  const [selectedLeague, setSelectedLeague]     = useState(null);
  const [selectedSeries, setSelectedSeries]     = useState(null);
  const [selectedOpenSession, setSelectedOpenSession] = useState(null);
  const [editingFrame, setEditingFrame]     = useState(null);
  const [editGameId, setEditGameId]         = useState(null); // null = current game, id = historical
  const [editStep, setEditStep]             = useState(0);
  const [editPins, setEditPins]             = useState([1,2,3,4,5,6,7,8,9,10]);
  const [editData, setEditData]             = useState({ rolls:[], pinsLeft:[], pinsAfterFirst:[] });
  const [theme, setTheme]                   = useState(() => {
    try { return localStorage.getItem("pinpal-theme") || "dark"; } catch(e) { return "dark"; }
  });
  const [user, setUser] = useState(null);
  const [authLoading, setAuthLoading] = useState(true);
  const [installPrompt, setInstallPrompt] = useState(null);
  const [isStandalone, setIsStandalone] = useState(() =>
    window.matchMedia("(display-mode: standalone)").matches || window.navigator.standalone === true
  );
  const [installDismissed, setInstallDismissed] = useState(() => {
    try { return localStorage.getItem("pinpal-install-dismissed") === "1"; } catch(e) { return false; }
  });
  const isIOS = /iphone|ipad|ipod/i.test(navigator.userAgent);

  useEffect(() => {
    const handler = (e) => { e.preventDefault(); setInstallPrompt(e); };
    window.addEventListener("beforeinstallprompt", handler);
    const mq = window.matchMedia("(display-mode: standalone)");
    const mqHandler = (e) => setIsStandalone(e.matches);
    mq.addEventListener("change", mqHandler);
    return () => {
      window.removeEventListener("beforeinstallprompt", handler);
      mq.removeEventListener("change", mqHandler);
    };
  }, []);

  const handleInstall = async () => {
    if (!installPrompt) return;
    installPrompt.prompt();
    const { outcome } = await installPrompt.userChoice;
    if (outcome === "accepted") { setIsStandalone(true); setInstallPrompt(null); }
  };

  const dismissInstall = () => {
    setInstallDismissed(true);
    try { localStorage.setItem("pinpal-install-dismissed", "1"); } catch(e) {}
  };

  C = theme === "dark" ? C_DARK : C_LIGHT;

  useEffect(() => {
    supabase.auth.getSession().then(({ data: { session } }) => {
      setUser(session?.user ?? null);
      setAuthLoading(false);
    });
    const { data: { subscription } } = supabase.auth.onAuthStateChange((_event, session) => {
      setUser(session?.user ?? null);
    });
    return () => subscription.unsubscribe();
  }, []);

  const ACTIVE_KEY = "pinpal-active";
  const [dataLoading, setDataLoading] = useState(false);
  const [syncError, setSyncError] = useState(null);

  const isUUID = (id) => /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i.test(String(id));

  const toLeagueRow  = (l) => ({ id:l.id, user_id:user.id, name:l.name, games_per_series:l.gamesPerSeries });
  const toGameRow    = (g) => ({ id:g.id, user_id:user.id, league_id:g.leagueId||null, league_name:g.leagueName||null, series_id:g.seriesId?String(g.seriesId):null, type:g.type||"open", date:g.date, frames:g.frames, complete:g.complete });
  const fromLeagueRow = (r) => ({ id:r.id, name:r.name, gamesPerSeries:r.games_per_series });
  const fromGameRow   = (r) => ({ id:r.id, leagueId:r.league_id, leagueName:r.league_name, seriesId:r.series_id, type:r.type, date:r.date, frames:r.frames, complete:r.complete });

  // ─── Load from Supabase on login ───
  useEffect(()=>{
    if (!user) return;
    const load = async () => {
      setDataLoading(true);
      setSyncError(null);
      try {
        const [{ data: lgData, error: lgErr }, { data: gmData, error: gmErr }] = await Promise.all([
          supabase.from("leagues").select("*").eq("user_id", user.id).order("created_at"),
          supabase.from("games").select("*").eq("user_id", user.id).order("created_at"),
        ]);
        if (lgErr) throw lgErr;
        if (gmErr) throw gmErr;
        setLeagues((lgData||[]).map(fromLeagueRow));
        setGames((gmData||[]).map(fromGameRow));
        // Restore in-progress game from localStorage
        const active = localStorage.getItem(ACTIVE_KEY);
        if (active) {
          const a = JSON.parse(active);
          setCurrentGame(a.currentGame);
          setCurrentFrame(a.currentFrame);
          setCurrentRoll(a.currentRoll);
          setStandingPins(a.standingPins);
          if (a.activeSeries) setActiveSeries(a.activeSeries);
          if (a.activeOpenSession) setActiveOpenSession(a.activeOpenSession);
          if (a.activeTournamentSession) setActiveTournamentSession(a.activeTournamentSession);
        }
      } catch(e) {
        setSyncError("Could not load your data. Check your connection and refresh.");
      } finally {
        setDataLoading(false);
      }
    };
    load();
  },[user]);

  const saveActive = useCallback((game, frame, roll, pins, series, openSess, tournSess) => {
    try {
      if (game) {
        localStorage.setItem(ACTIVE_KEY, JSON.stringify({
          currentGame: game, currentFrame: frame, currentRoll: roll, standingPins: pins,
          activeSeries: series||null, activeOpenSession: openSess||null, activeTournamentSession: tournSess||null,
        }));
      } else {
        localStorage.removeItem(ACTIVE_KEY);
      }
    } catch(e){}
  },[]);

  const syncLeague = useCallback(async (league) => {
    if (!user) return;
    try {
      const { error } = await supabase.from("leagues").upsert(toLeagueRow(league));
      if (error) throw error;
    } catch(e) { setSyncError("League save failed — your data may not be backed up."); }
  },[user]);

  const syncGame = useCallback(async (game) => {
    if (!user) return;
    try {
      const { error } = await supabase.from("games").upsert(toGameRow(game));
      if (error) throw error;
      setSyncError(null);
    } catch(e) { setSyncError("Game save failed — your data may not be backed up."); }
  },[user]);

  const save = useCallback((newLeagues, newGames, changedLeague=null, changedGame=null)=>{
    setLeagues(newLeagues);
    setGames(newGames);
    if (!user) return;
    if (changedLeague) syncLeague(changedLeague);
    if (changedGame) syncGame(changedGame);
  },[user, syncLeague, syncGame]);

  // Auto-save in-progress game to localStorage
  useEffect(()=>{
    saveActive(currentGame, currentFrame, currentRoll, standingPins, activeSeries, activeOpenSession, activeTournamentSession);
  },[currentGame, currentFrame, currentRoll, standingPins, activeSeries, activeOpenSession, activeTournamentSession]);

  const abandonGame = () => {
    setCurrentGame(null); setCurrentFrame(0); setCurrentRoll(0);
    setStandingPins([1,2,3,4,5,6,7,8,9,10]);
    setActiveSeries(null); setActiveOpenSession(null); setActiveTournamentSession(null);
    saveActive(null);
    setView("home");
  };

  // ─── League actions ───
  const createLeague = (name, gamesPerSeries) => {
    const newLeague = emptyLeague(name, gamesPerSeries);
    save([...leagues, newLeague], games, newLeague, null);
  };

  const startSeries = (league) => {
    const seriesId = uuid();
    const series = { id: seriesId, league, completedGames: [] };
    setActiveSeries(series);
    beginGame(emptyGame("league", league.name, league.id, seriesId));
  };

  const startNextSeriesGame = () => {
    const league = activeSeries.league;
    const seriesId = activeSeries.id;
    beginGame(emptyGame("league", league.name, league.id, seriesId));
  };

  // ─── Game actions ───
  const beginGame = (game) => {
    setCurrentGame(game);
    setCurrentFrame(0); setCurrentRoll(0);
    setStandingPins([1,2,3,4,5,6,7,8,9,10]);
    setView("game");
  };

  const startOpenSession = () => {
    const sessionId = uuid();
    setActiveOpenSession({ id: sessionId, completedGames: [] });
    beginGame(emptyGame("open", "", null, sessionId));
  };

  const startNextOpenGame = () => {
    beginGame(emptyGame("open", "", null, activeOpenSession.id));
  };

  const endOpenSession = () => {
    setActiveOpenSession(null);
    setView("open");
  };

  const continueOpenSession = (session) => {
    setActiveOpenSession({ id: session[0].seriesId || session[0].id, completedGames: session });
    setView("open-session-next");
  };

  const startTournamentSession = (name) => {
    const sessionId = uuid();
    setActiveTournamentSession({ id: sessionId, name, completedGames: [] });
    beginGame(emptyGame("tournament", name, null, sessionId));
  };

  const startNextTournamentGame = () => {
    beginGame(emptyGame("tournament", activeTournamentSession.name, null, activeTournamentSession.id));
  };

  const endTournamentSession = () => {
    setActiveTournamentSession(null);
    setView("tournaments");
  };

  const continueTournamentSession = (session) => {
    const name = session[0].leagueName || "Tournament";
    setActiveTournamentSession({ id: session[0].seriesId || session[0].id, name, completedGames: session });
    setView("tournament-session-next");
  };

  const togglePin = (pinId) => {
    setStandingPins(prev=>prev.includes(pinId)?prev.filter(p=>p!==pinId):[...prev,pinId].sort((a,b)=>a-b));
  };

  const handleGameComplete = (completedGame) => {
    if (activeOpenSession) {
      const updated = { ...activeOpenSession, completedGames:[...activeOpenSession.completedGames, completedGame] };
      setActiveOpenSession(updated);
      setCurrentGame(completedGame);
      return;
    }
    setCurrentGame(null); saveActive(null);
    if (activeSeries) {
      const updatedSeries = { ...activeSeries, completedGames:[...activeSeries.completedGames, completedGame] };
      setActiveSeries(updatedSeries);
      if (updatedSeries.completedGames.length < activeSeries.league.gamesPerSeries) {
        setView("series-next");
      } else {
        setView("series-complete");
      }
    } else if (activeTournamentSession) {
      const updated = { ...activeTournamentSession, completedGames:[...activeTournamentSession.completedGames, completedGame] };
      setActiveTournamentSession(updated);
      setView("tournament-session-next");
    } else {
      setView("home");
    }
  };

  const recordRoll = (overridePins) => {
    if (!currentGame) return;
    const pins = overridePins !== undefined ? overridePins : standingPins;
    const allPins = currentRoll===0?[1,2,3,4,5,6,7,8,9,10]:currentGame.frames[currentFrame].pinsAfterFirst||[1,2,3,4,5,6,7,8,9,10];
    const knocked = allPins.filter(p=>!pins.includes(p)).length;
    const newGame = JSON.parse(JSON.stringify(currentGame));
    const frame = newGame.frames[currentFrame];
    frame.rolls.push(knocked);

    if (currentFrame<9) {
      if (currentRoll===0) {
        if (knocked===10) {
          frame.pinsLeft=[];
          setCurrentFrame(currentFrame+1); setCurrentRoll(0); setStandingPins([1,2,3,4,5,6,7,8,9,10]);
        } else {
          frame.pinsAfterFirst=[...standingPins]; frame.pinsLeft=[...standingPins];
          setCurrentRoll(1);
        }
      } else {
        frame.pinsLeft=frame.pinsLeft||[];
        frame.pinsAfterSecond=[...standingPins];
        setCurrentFrame(currentFrame+1); setCurrentRoll(0); setStandingPins([1,2,3,4,5,6,7,8,9,10]);
      }
    } else {
      const rolls=frame.rolls;
      if (rolls.length===1) {
        if(knocked===10){setStandingPins([1,2,3,4,5,6,7,8,9,10]);frame.pinsAfterFirst=[1,2,3,4,5,6,7,8,9,10];}
        else{frame.pinsAfterFirst=[...standingPins];}
        setCurrentRoll(1);
      } else if (rolls.length===2) {
        const r1=rolls[0],r2=rolls[1];
        if(r1===10||r1+r2>=10){
          const freshRack=(r2===10)||(r1!==10&&r1+r2===10);
          if(freshRack){frame.pinsAfterFirst=[1,2,3,4,5,6,7,8,9,10];setStandingPins([1,2,3,4,5,6,7,8,9,10]);}
          else{frame.pinsAfterFirst=[...standingPins];}
          setCurrentRoll(2);
        } else { newGame.complete=true; const ng=[...games,newGame]; save(leagues,ng,null,newGame); handleGameComplete(newGame); return; }
      } else if (rolls.length===3) {
        newGame.complete=true; const ng=[...games,newGame]; save(leagues,ng,null,newGame); handleGameComplete(newGame); return;
      }
    }
    setCurrentGame(newGame);
  };

  // ─── Frame edit actions ───
  const findGameById = (id) => {
    if (!id) return null;
    return games.find(g => g.id === id)
      || (selectedSeries||[]).find(g => g.id === id)
      || (selectedOpenSession||[]).find(g => g.id === id)
      || (selectedTournamentSession||[]).find(g => g.id === id)
      || null;
  };

  const startEditFrame = (fi, gameId = null) => {
    const game = gameId ? findGameById(gameId) : currentGame;
    const frame = game?.frames[fi];
    const wasStrike = frame?.rolls?.[0] === 10;
    const originalLeave = (!wasStrike && frame?.pinsAfterFirst?.length > 0)
      ? frame.pinsAfterFirst
      : [1,2,3,4,5,6,7,8,9,10];
    setEditingFrame(fi);
    setEditGameId(gameId);
    setEditStep(0);
    setEditPins(originalLeave);
    setEditData({ rolls:[], pinsLeft:[], pinsAfterFirst:[1,2,3,4,5,6,7,8,9,10] });
  };

  const cancelEdit = () => {
    setEditingFrame(null); setEditGameId(null); setEditStep(0);
    setEditPins([1,2,3,4,5,6,7,8,9,10]);
    setEditData({ rolls:[], pinsLeft:[], pinsAfterFirst:[] });
  };

  const commitEditFrame = (fi, data) => {
    if (editGameId) {
      const applyEdit = (g) => {
        const ng = JSON.parse(JSON.stringify(g));
        ng.frames[fi].rolls = data.rolls;
        ng.frames[fi].pinsLeft = data.pinsLeft;
        ng.frames[fi].pinsAfterFirst = data.pinsAfterFirst;
        ng.frames[fi].pinsAfterSecond = data.pinsAfterSecond;
        return ng;
      };
      const inGames = games.some(g => g.id === editGameId);
      let newGames;
      if (inGames) {
        newGames = games.map(g => g.id === editGameId ? applyEdit(g) : g);
      } else {
        const sourceGame = findGameById(editGameId);
        if (!sourceGame) { cancelEdit(); return; }
        newGames = [...games, applyEdit(sourceGame)];
      }
      const editedGame = newGames.find(g => g.id === editGameId);
      save(leagues, newGames, null, editedGame);
      const updated = g => g.id === editGameId ? editedGame : g;
      if (selectedSeries) setSelectedSeries(prev => prev.map(updated));
      if (selectedOpenSession) setSelectedOpenSession(prev => prev.map(updated));
      if (selectedTournamentSession) setSelectedTournamentSession(prev => prev.map(updated));
    } else {
      const newGame = JSON.parse(JSON.stringify(currentGame));
      const f = newGame.frames[fi];
      f.rolls = data.rolls; f.pinsLeft = data.pinsLeft; f.pinsAfterFirst = data.pinsAfterFirst; f.pinsAfterSecond = data.pinsAfterSecond;
      setCurrentGame(newGame);
      if (fi === currentFrame) {
        const isStrike = data.rolls[0] === 10;
        const frameComplete = fi < 9
          ? (isStrike || data.rolls.length >= 2)
          : data.rolls.length >= 2 && (data.rolls[0] === 10 || data.rolls[0] + data.rolls[1] >= 10
              ? data.rolls.length >= 3
              : true);
        if (frameComplete && fi < 9) {
          setCurrentFrame(fi + 1);
          setCurrentRoll(0);
          setStandingPins([1,2,3,4,5,6,7,8,9,10]);
        } else if (frameComplete && fi === 9) {
          newGame.complete = true;
          setCurrentGame(newGame);
          const ng = [...games.filter(g => g.id !== newGame.id), newGame];
          save(leagues, ng, null, newGame);
          handleGameComplete(newGame);
        } else {
          setCurrentRoll(data.rolls.length);
          setStandingPins(data.pinsAfterFirst?.length ? data.pinsAfterFirst : [1,2,3,4,5,6,7,8,9,10]);
        }
      }
    }
    cancelEdit();
  };

  const recordEditRoll = (overridePins) => {
    const fi = editingFrame;
    const pins = overridePins !== undefined ? overridePins : editPins;
    const allPins = editStep === 0 ? [1,2,3,4,5,6,7,8,9,10] : editData.pinsAfterFirst;
    const knocked = allPins.filter(p => !pins.includes(p)).length;
    const newRolls = [...editData.rolls, knocked];
    const newData = { ...editData, rolls: newRolls };

    if (fi < 9) {
      if (editStep === 0) {
        if (knocked === 10) {
          newData.pinsLeft = [];
          commitEditFrame(fi, newData);
        } else {
          newData.pinsAfterFirst = [...editPins];
          newData.pinsLeft = [...editPins];
          setEditData(newData);
          setEditStep(1);
          // Pre-populate ball 2 with stored pinsAfterSecond if available, else all remaining standing
          const origGame2 = editGameId ? findGameById(editGameId) : currentGame;
          const origFrame2 = origGame2?.frames[fi];
          const ball2Leave = origFrame2?.pinsAfterSecond != null
            ? origFrame2.pinsAfterSecond.filter(p => editPins.includes(p))
            : [...editPins];
          setEditPins(ball2Leave);
        }
      } else {
        newData.pinsAfterSecond = [...pins];
        commitEditFrame(fi, newData);
      }
    } else {
      // 10th frame
      if (editStep === 0) {
        if (knocked === 10) {
          newData.pinsAfterFirst = [1,2,3,4,5,6,7,8,9,10];
          setEditPins([1,2,3,4,5,6,7,8,9,10]);
        } else {
          newData.pinsAfterFirst = [...editPins];
        }
        setEditData(newData); setEditStep(1);
      } else if (editStep === 1) {
        if (newRolls[0] === 10 || newRolls[0] + knocked >= 10) {
          const freshRack=(knocked===10)||(newRolls[0]!==10&&newRolls[0]+knocked===10);
          if(freshRack){newData.pinsAfterFirst=[1,2,3,4,5,6,7,8,9,10];setEditPins([1,2,3,4,5,6,7,8,9,10]);}
          else{newData.pinsAfterFirst=[...editPins];}
          setEditData(newData); setEditStep(2);
        } else {
          commitEditFrame(fi, newData);
        }
      } else {
        commitEditFrame(fi, newData);
      }
    }
  };

  const toggleEditPin = (pinId) => {
    setEditPins(prev => prev.includes(pinId) ? prev.filter(p=>p!==pinId) : [...prev,pinId].sort((a,b)=>a-b));
  };

  const editHistoricalFrame = useCallback((updatedGame) => {
    const inGames = games.some(g => g.id === updatedGame.id);
    const newGames = inGames
      ? games.map(g => g.id === updatedGame.id ? updatedGame : g)
      : [...games, updatedGame];
    save(leagues, newGames, null, updatedGame);
    const updated = g => g.id === updatedGame.id ? updatedGame : g;
    if (selectedSeries) setSelectedSeries(prev => prev.map(updated));
    if (selectedOpenSession) setSelectedOpenSession(prev => prev.map(updated));
    if (selectedTournamentSession) setSelectedTournamentSession(prev => prev.map(updated));
  }, [games, leagues, save, selectedSeries, selectedOpenSession, selectedTournamentSession]);

  const resetData = async () => {
    if (confirm("Delete all game data? This cannot be undone.")) {
      setLeagues([]); setGames([]);
      localStorage.removeItem(STORAGE_KEY);
      localStorage.removeItem(ACTIVE_KEY);
      if (user) {
        await Promise.all([
          supabase.from("games").delete().eq("user_id", user.id),
          supabase.from("leagues").delete().eq("user_id", user.id),
        ]);
      }
    }
  };

  // ─── Nav config ───
  const viewTitles = {
    home:"", leagues:"LEAGUES", "league-new":"NEW LEAGUE",
    "league-detail": selectedLeague?.name||"LEAGUE",
    "series-detail":  selectedSeries?.[0]?.date||"SERIES",
    "series-stats":   "DATE STATISTICS",
    "league-stats":   "LEAGUE STATISTICS",
    open:"OPEN BOWLING", tournaments:"TOURNAMENTS",
    "open-session-detail": selectedOpenSession?.[0]?.date||"SESSION",
    "open-session-stats":  "SESSION STATS",
    "open-all-stats":      "ALL OPEN STATS",
    "tournaments-start":   "NEW TOURNAMENT",
    "tournament-session-detail": selectedTournamentSession?.[0]?.leagueName||"TOURNAMENT",
    "tournament-session-stats":  "TOURNAMENT STATS",
    "tournament-all-stats":      "ALL TOURNAMENT STATS",
    stats:"STATISTICS", settings:"SETTINGS", help:"HELP",
    "series-next":"", "series-complete":"", "tournament-session-next":"",
  };
  const backRoutes = {
    leagues:"home", "league-new":"leagues", "league-detail":"leagues", help:"home",
    "series-detail":"league-detail",
    "series-stats":"series-detail",
    "league-stats":"league-detail",
    "open-session-detail":"open",
    "open-session-stats":"open-session-detail",
    "open-all-stats":"open",
    "tournaments-start":"tournaments",
    "tournament-session-detail":"tournaments",
    "tournament-session-stats":"tournament-session-detail",
    "tournament-all-stats":"tournaments",
    open:"home", tournaments:"home", stats:"home", settings:"home",
  };
  const showHeader = !["series-next","series-complete","game","tournament-session-next"].includes(view);

  // Compute original frame display for edit overlay
  const _editOrigFrame = editingFrame !== null
    ? (editGameId ? findGameById(editGameId) : currentGame)?.frames[editingFrame]
    : null;
  const _origDisplayParts = (() => {
    const rolls = _editOrigFrame?.rolls || [];
    if (!rolls.length) return [];
    return rolls.map((r,i) => {
      if (editingFrame < 9) {
        if (i===0) return r===10?"X":r===0?"—":String(r);
        return (rolls[0]+r===10)?"/":r===0?"—":String(r);
      } else {
        if (i===0) return r===10?"X":r===0?"—":String(r);
        if (i===1) return rolls[0]!==10&&rolls[0]+r===10?"/":r===10?"X":r===0?"—":String(r);
        return r===10?"X":r===0?"—":String(r);
      }
    });
  })();

  if (authLoading || dataLoading) return (
    <div style={{minHeight:"100vh",display:"flex",alignItems:"center",justifyContent:"center",background:C.bg}}>
      <div style={{color:C.muted,fontFamily:"'Oswald',sans-serif",letterSpacing:3,fontSize:14}}>
        {authLoading ? "LOADING…" : "SYNCING DATA…"}
      </div>
    </div>
  );

  if (!user) return <AuthView onAuth={setUser}/>;

  return (
    <div style={{
      width:"100%", minHeight:"100vh",
      background:`linear-gradient(180deg,${C.bg} 0%,${C.card} 30%,${C.bg} 100%)`,
      color:C.cream, fontFamily:"'Oswald',sans-serif", position:"relative",
    }}>
      <link href="https://fonts.googleapis.com/css2?family=Oswald:wght@300;400;500;600;700&family=Playfair+Display:wght@700;900&display=swap" rel="stylesheet"/>

      {/* Grain */}
      <div style={{position:"fixed",top:0,left:0,right:0,bottom:0,background:"url('data:image/svg+xml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHdpZHRoPSIzMDAiIGhlaWdodD0iMzAwIj48ZmlsdGVyIGlkPSJhIiB4PSIwIiB5PSIwIj48ZmVUdXJidWxlbmNlIHR5cGU9ImZyYWN0YWxOb2lzZSIgYmFzZUZyZXF1ZW5jeT0iLjc1IiBzdGl0Y2hUaWxlcz0ic3RpdGNoIi8+PGZlQ29sb3JNYXRyaXggdHlwZT0ic2F0dXJhdGUiIHZhbHVlcz0iMCIvPjwvZmlsdGVyPjxyZWN0IHdpZHRoPSIzMDAiIGhlaWdodD0iMzAwIiBmaWx0ZXI9InVybCgjYSkiIG9wYWNpdHk9Ii4wNSIvPjwvc3ZnPg==')",pointerEvents:"none",zIndex:1}}/>

      {/* ─── Install Banner ─── */}
      {!isStandalone && !installDismissed && (
        <div style={{
          position:"fixed",bottom:0,left:0,right:0,zIndex:500,
          background:C.card,borderTop:`2px solid ${C.gold}`,
          padding:"16px 20px",display:"flex",flexDirection:"column",gap:10,
        }}>
          <div style={{display:"flex",justifyContent:"space-between",alignItems:"flex-start"}}>
            <div>
              <div style={{fontSize:16,fontWeight:600,color:C.gold,letterSpacing:1}}>Install PinTracker</div>
              <div style={{fontSize:13,color:C.muted,marginTop:4,lineHeight:1.4}}>
                {isIOS
                  ? <>Tap the <strong style={{color:C.cream}}>Share</strong> button ⬆ in Safari, then tap <strong style={{color:C.cream}}>"Add to Home Screen"</strong></>
                  : installPrompt
                    ? "Tap below to install — no app store needed"
                    : <>In Chrome, tap the <strong style={{color:C.cream}}>⋮ menu</strong> then <strong style={{color:C.cream}}>"Add to Home screen"</strong></>
                }
              </div>
            </div>
            <button onClick={dismissInstall} style={{background:"none",border:"none",color:C.muted,fontSize:22,cursor:"pointer",padding:"0 0 0 12px",lineHeight:1}}>✕</button>
          </div>
          {!isIOS && installPrompt && (
            <button onClick={handleInstall} style={{
              background:C.gold,color:"#1a1208",border:"none",borderRadius:10,
              padding:"12px 0",fontSize:16,fontWeight:700,cursor:"pointer",
              letterSpacing:1,width:"100%",
            }}>Add to Home Screen</button>
          )}
        </div>
      )}

      {/* ─── Historical Frame Edit Overlay ─── */}
      {editingFrame!==null&&editGameId!==null&&(
        <div style={{position:"fixed",top:0,left:0,right:0,bottom:0,background:C.overlay,zIndex:400,display:"flex",flexDirection:"column",justifyContent:"flex-end"}}>
          <div style={{background:C.card,borderRadius:"20px 20px 0 0",padding:"20px 20px 32px",borderTop:`2px solid #5a2020`}}>
            <div style={{display:"flex",justifyContent:"space-between",alignItems:"center",marginBottom:16}}>
              <div>
                <div style={{fontSize:14,color:"#c85050",textTransform:"uppercase",letterSpacing:2,fontFamily:"'Oswald',sans-serif",borderBottom:"2px solid #c85050",paddingBottom:4,display:"inline-block"}}>
                  Edit Frame {editingFrame+1}
                </div>
                <div style={{fontSize:15,color:C.muted,marginTop:4}}>Ball {editStep+1}</div>
                {_origDisplayParts.length>0&&(
                  <div style={{fontSize:15,color:C.muted,marginTop:3,display:"flex",alignItems:"baseline",gap:4,flexWrap:"wrap"}}>
                    <span>Was:</span>
                    {_origDisplayParts.map((part,i)=>(
                      <span key={i} style={{
                        color:i===editStep?C.text:C.muted,
                        borderBottom:i===editStep?`2px solid ${C.text}`:"none",
                        paddingBottom:i===editStep?1:0,
                      }}>{part}</span>
                    )).reduce((acc,el,i)=>i===0?[el]:[...acc,<span key={`d${i}`} style={{color:C.muted}}> · </span>,el],[])}
                  </div>
                )}
              </div>
              <button style={{background:C.gold,border:"none",color:C.btnText,cursor:"pointer",fontSize:14,fontFamily:"'Oswald',sans-serif",fontWeight:500,textTransform:"uppercase",letterSpacing:1,padding:"6px 14px",borderRadius:8}}
                onClick={cancelEdit}>Cancel</button>
            </div>
            <PinDiagram standing={editPins} onToggle={toggleEditPin} disabled={false}/>
            <div style={{marginTop:16,display:"flex",gap:8}}>
              <button style={{...btnSecondary(),flex:1,padding:"12px 8px",fontSize:14}} onClick={()=>recordEditRoll([])}>{editStep===0||editPins.length===10?"Strike":"Spare"}</button>
              <button style={{...btnPrimary(),flex:1,padding:"12px 8px",fontSize:14}} onClick={()=>recordEditRoll()}>Confirm</button>
            </div>
          </div>
        </div>
      )}


      {syncError&&(
        <div style={{position:"fixed",bottom:80,left:16,right:16,zIndex:500,background:"#3a1a1a",border:"1px solid #c85050",borderRadius:10,padding:"12px 16px",display:"flex",alignItems:"center",justifyContent:"space-between",gap:12}}>
          <span style={{fontSize:13,color:"#e88080",lineHeight:1.4}}>{syncError}</span>
          <button onClick={()=>setSyncError(null)} style={{background:"none",border:"none",color:"#c85050",cursor:"pointer",fontSize:18,lineHeight:1,padding:0,flexShrink:0}}>✕</button>
        </div>
      )}

      <div style={{position:"relative",zIndex:2,paddingBottom:(!isStandalone&&!installDismissed)?120:0}}>
        {/* Header */}
        {showHeader&&(
          <div style={{position:"sticky",top:0,zIndex:100,display:"flex",alignItems:"center",justifyContent:"center",padding:"20px 16px 20px",borderBottom:`1px solid #2a2018`,background:C.bg}}>
            {backRoutes[view]&&(
              <button onClick={()=>setView(backRoutes[view])} style={{
                position:"absolute",left:16,background:"none",border:"none",
                color:C.gold,cursor:"pointer",fontSize:22,lineHeight:1,padding:4,
              }}>‹</button>
            )}
            {view==="home"?(
              <div style={{textAlign:"center"}}>
                <h1 style={{fontFamily:"'Playfair Display',serif",fontSize:26,fontWeight:900,margin:0,letterSpacing:1,whiteSpace:"nowrap",display:"flex",alignItems:"center",justifyContent:"center",gap:8}}>
                  <span style={{background:`linear-gradient(145deg,${C.cream},${C.gold})`,WebkitBackgroundClip:"text",WebkitTextFillColor:"transparent"}}>PinTracker</span>
                </h1>
                <p style={{fontSize:14,letterSpacing:5,color:C.muted,textTransform:"uppercase",margin:"6px 0 0"}}>Bowling Scorekeeper</p>
              </div>
            ):(
              <h2 style={{fontFamily:"'Oswald',sans-serif",fontSize:17,fontWeight:600,color:C.gold,margin:0,letterSpacing:3,textTransform:"uppercase"}}>
                {viewTitles[view]||""}
              </h2>
            )}
            {view!=="home"&&(
              <button onClick={()=>setView("home")} style={{
                position:"absolute",right:16,background:"none",border:"none",
                color:C.muted,cursor:"pointer",fontSize:32,lineHeight:1,padding:4,
              }}>⌂</button>
            )}
          </div>
        )}

        <div style={{paddingTop: showHeader?40:0}}>

          {view==="home"&&(
            <HomeView leagues={leagues} games={games} onNavigate={v=>{
              if(v==="open") setView("open");
              else if(v==="stats") setView("stats");
              else if(v==="settings") setView("settings");
              else if(v==="leagues") setView("leagues");
              else if(v==="tournaments") setView("tournaments");
              else if(v==="help") setView("help");
            }}
            activeGame={currentGame&&!currentGame.complete?{frame:currentFrame,roll:currentRoll}:null}
            onResume={()=>setView("game")}
            onAbandon={abandonGame}
            />
          )}

          {view==="leagues"&&(
            <LeaguesView leagues={leagues} games={games}
              onNavigate={setView}
              onSelectLeague={setSelectedLeague}/>
          )}

          {view==="league-new"&&(
            <LeagueNewView onNavigate={setView} onCreate={createLeague}/>
          )}

          {view==="league-detail"&&selectedLeague&&(
            <LeagueDetailView league={selectedLeague} games={games}
              onStartSeries={startSeries}
              onSelectSeries={series=>{setSelectedSeries(series);setView("series-detail");}}
              onViewStats={()=>setView("league-stats")}/>
          )}

          {view==="league-stats"&&selectedLeague&&(
            <LeagueStatsView games={games.filter(g=>g.leagueId===selectedLeague.id&&g.complete)} leagues={leagues}/>
          )}

          {view==="series-detail"&&selectedSeries&&(
            <SeriesDetailView series={selectedSeries} league={selectedLeague}
              onViewStats={()=>setView("series-stats")}
              onFrameEdit={editHistoricalFrame}/>
          )}

          {view==="series-stats"&&selectedSeries&&(
            <SeriesStatsView series={selectedSeries}/>
          )}

          {view==="open"&&(
            <OpenSetupView games={games} onStart={startOpenSession}
              onSelectSession={s=>{setSelectedOpenSession(s);setView("open-session-detail");}}
              onViewAllStats={()=>setView("open-all-stats")}
              onContinueSession={continueOpenSession}/>
          )}

          {view==="open-session-detail"&&selectedOpenSession&&(
            <OpenSessionDetailView session={selectedOpenSession}
              onViewStats={()=>setView("open-session-stats")}
              onNewGame={()=>continueOpenSession(selectedOpenSession)}
              onFrameEdit={editHistoricalFrame}/>
          )}

          {view==="open-session-stats"&&selectedOpenSession&&(
            <div style={{padding:"0 16px 80px"}}>
              <GameStatsModule games={selectedOpenSession}/>
            </div>
          )}

          {view==="open-all-stats"&&(
            <div style={{padding:"0 16px 80px"}}>
              <GameStatsModule games={games.filter(g=>g.type==="open"&&g.complete)} showGameAvg={true} statsTitle="Open Play Statistics"/>
            </div>
          )}

          {view==="tournaments"&&(
            <TournamentsView games={games}
              onStart={()=>setView("tournaments-start")}
              onSelectSession={s=>{setSelectedTournamentSession(s);setView("tournament-session-detail");}}
              onViewAllStats={()=>setView("tournament-all-stats")}
              onContinueSession={continueTournamentSession}/>
          )}

          {view==="tournaments-start"&&(
            <TournamentStartView onStart={name=>{startTournamentSession(name);}}/>
          )}

          {view==="tournament-session-detail"&&selectedTournamentSession&&(
            <TournamentSessionDetailView session={selectedTournamentSession}
              onViewStats={()=>setView("tournament-session-stats")}
              onNewGame={()=>continueTournamentSession(selectedTournamentSession)}
              onFrameEdit={editHistoricalFrame}/>
          )}

          {view==="tournament-session-stats"&&selectedTournamentSession&&(
            <div style={{padding:"0 16px 80px"}}>
              <GameStatsModule games={selectedTournamentSession} statsTitle="Tournament Statistics"/>
            </div>
          )}

          {view==="tournament-all-stats"&&(
            <div style={{padding:"0 16px 80px"}}>
              <GameStatsModule games={games.filter(g=>g.type==="tournament"&&g.complete)} showGameAvg={true} statsTitle="Tournament Statistics"/>
            </div>
          )}

          {view==="tournament-session-next"&&activeTournamentSession&&(
            <TournamentSessionNextView activeTournamentSession={activeTournamentSession}
              onStartNext={startNextTournamentGame}
              onEnd={endTournamentSession}/>
          )}

          {view==="stats"&&<StatsView games={games} leagues={leagues}/>}

          {view==="settings"&&<SettingsView onResetData={resetData} theme={theme} onThemeChange={t=>{setTheme(t);try{localStorage.setItem("pinpal-theme",t);}catch(e){}}} onSignOut={async()=>{await supabase.auth.signOut();setUser(null);}}/>}
          {view==="help"&&<HelpView/>}

          {/* ─── Game ─── */}
          {view==="game"&&currentGame&&(
            <div style={{padding:"0 0 80px"}}>
              <div style={{position:"relative",display:"flex",justifyContent:"space-between",alignItems:"center",marginBottom:12,padding:"16px 16px 0"}}>
                <button style={{background:"none",border:"none",color:C.gold,cursor:"pointer",fontSize:16,padding:0,fontFamily:"'Oswald',sans-serif"}}
                  onClick={()=>setView("home")}>← Home</button>
                <span style={{position:"absolute",left:0,right:0,textAlign:"center",fontSize:17,color:C.muted,textTransform:"uppercase",letterSpacing:2,pointerEvents:"none"}}>
                  {activeSeries&&`Game ${activeSeries.completedGames.length+1}`}
                  {activeTournamentSession&&`Game ${activeTournamentSession.completedGames.length+1}`}
                  {activeOpenSession&&`Game ${activeOpenSession.completedGames.length+1}`}
                  {!activeSeries&&!activeTournamentSession&&!activeOpenSession&&"Game 1"}
                </span>
              </div>

              <div style={{padding:"0 5px"}}>
                <Scorecard frames={currentGame.frames} complete={currentGame.complete}
                  onFrameClick={fi=>{ if(fi<=currentFrame) startEditFrame(fi); }}
                  currentFrame={currentFrame}/>
              </div>

              {editingFrame!==null&&_origDisplayParts.length>0&&(
                <div style={{textAlign:"center",fontSize:14,color:C.muted,marginTop:8,display:"flex",alignItems:"baseline",justifyContent:"center",gap:4}}>
                  <span>Was:</span>
                  {_origDisplayParts.map((part,i)=>(
                    <span key={i} style={{
                      color: i===editStep?C.text:C.muted,
                      borderBottom: i===editStep?`2px solid ${C.text}`:"none",
                      paddingBottom: i===editStep?1:0,
                    }}>{part}</span>
                  )).reduce((acc,el,i)=>i===0?[el]:[...acc,<span key={`d${i}`} style={{color:C.muted}}> · </span>,el],[])}
                </div>
              )}

              {currentGame.complete && activeOpenSession ? (
                <div style={{padding:"24px 16px",textAlign:"center"}}>
                  <div style={{fontSize:13,color:C.muted,letterSpacing:3,textTransform:"uppercase",marginBottom:6}}>
                    Game {activeOpenSession.completedGames.length} Complete
                  </div>
                  <div style={{fontSize:72,fontWeight:700,color:C.gold,fontFamily:"'Oswald',sans-serif",lineHeight:1,marginBottom:12}}>
                    {calculateScore(currentGame.frames)}
                  </div>
                  {(() => {
                    const total = activeOpenSession.completedGames.reduce((t,g)=>t+calculateScore(g.frames),0);
                    const avg = (total / activeOpenSession.completedGames.length).toFixed(1);
                    return (
                      <div style={{display:"flex",justifyContent:"center",gap:32,marginBottom:24}}>
                        <div>
                          <div style={{fontSize:12,color:C.muted,letterSpacing:2,textTransform:"uppercase",marginBottom:2}}>Session Total</div>
                          <div style={{fontSize:22,fontWeight:300,color:C.cream,fontFamily:"'Oswald',sans-serif"}}>{total}</div>
                        </div>
                        <div>
                          <div style={{fontSize:12,color:C.muted,letterSpacing:2,textTransform:"uppercase",marginBottom:2}}>Average Today</div>
                          <div style={{fontSize:22,fontWeight:300,color:C.cream,fontFamily:"'Oswald',sans-serif"}}>{avg}</div>
                        </div>
                      </div>
                    );
                  })()}
                  <div style={{display:"flex",flexDirection:"column",gap:10,padding:"0 0"}}>
                    <button style={btnPrimary()} onClick={startNextOpenGame}>Bowl Another Game</button>
                    <button style={{...btnSecondary(),fontSize:14,letterSpacing:1}} onClick={endOpenSession}>End Session</button>
                  </div>
                </div>
              ) : (
                <div style={{padding:"20px 16px 24px",margin:"12px 16px 8px"}}>
                  <PinDiagram
                    standing={editingFrame!==null?editPins:standingPins}
                    onToggle={editingFrame!==null?toggleEditPin:togglePin}
                    disabled={false}/>
                  <div style={{marginTop:24,display:"flex",gap:8}}>
                    {editingFrame!==null?(
                      <>
                        <button style={{...btnSecondary(),flex:1,padding:"12px 8px",fontSize:15}} onClick={()=>recordEditRoll([])}>{editStep===0||editPins.length===10?"Strike":"Spare"}</button>
                        <button style={{...btnPrimary(),flex:1,padding:"12px 8px",fontSize:15}} onClick={()=>recordEditRoll()}>
                          {editingFrame<9?(editStep===0&&editData.rolls.length===0?"Next":"Confirm"):(editStep<2?"Next":"Confirm")}
                        </button>
                      </>
                    ):(
                      <>
                        <button style={{...btnSecondary(),flex:1,padding:"12px 8px",fontSize:15}} onClick={()=>recordRoll([])}>{currentRoll===0||standingPins.length===10?"Strike":"Spare"}</button>
                        <button style={{...btnPrimary(),flex:1,padding:"12px 8px",fontSize:15}} onClick={()=>recordRoll()}>Next</button>
                      </>
                    )}
                  </div>
                </div>
              )}

            </div>
          )}

          {view==="series-next"&&activeSeries&&(
            <SeriesNextView activeSeries={activeSeries} onStartNext={startNextSeriesGame}
              onExit={()=>{ setActiveSeries(null); setView("league-detail"); }}/>
          )}


          {view==="series-complete"&&activeSeries&&(
            <SeriesCompleteView activeSeries={activeSeries} onDone={()=>{
              setActiveSeries(null);
              setView("league-detail");
            }}/>
          )}

        </div>
      </div>
    </div>
  );
}
