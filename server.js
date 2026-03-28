'use strict';
const express = require('express');
const http = require('http');
const { Server } = require('socket.io');
const path = require('path');
const fs = require('fs');

const app = express();
const server = http.createServer(app);
const io = new Server(server);
const PORT = process.env.PORT || 3000;

app.use(express.static(path.join(__dirname, 'public')));

// ═══════════════════════════════════════════════════════
// DATA PERSISTENCE
// ═══════════════════════════════════════════════════════

const DATA_DIR = path.join(__dirname, 'data');
const USERS_FILE = path.join(DATA_DIR, 'users.json');
const TOURNAMENTS_FILE = path.join(DATA_DIR, 'tournaments.json');

if (!fs.existsSync(DATA_DIR)) fs.mkdirSync(DATA_DIR, { recursive: true });
if (!fs.existsSync(USERS_FILE)) fs.writeFileSync(USERS_FILE, '{}');
if (!fs.existsSync(TOURNAMENTS_FILE)) fs.writeFileSync(TOURNAMENTS_FILE, '{}');

function loadUsers() { try { return JSON.parse(fs.readFileSync(USERS_FILE, 'utf8')); } catch { return {}; } }
function saveUsers(u) { fs.writeFileSync(USERS_FILE, JSON.stringify(u, null, 2)); }
function loadTournaments() { try { return JSON.parse(fs.readFileSync(TOURNAMENTS_FILE, 'utf8')); } catch { return {}; } }
function saveTournaments(t) { fs.writeFileSync(TOURNAMENTS_FILE, JSON.stringify(t, null, 2)); }

// onlineSessions: email → socketId
const onlineSessions = new Map();

// ═══════════════════════════════════════════════════════
// CHESS ENGINE
// ═══════════════════════════════════════════════════════

const INIT = [
  ['r','n','b','q','k','b','n','r'],
  ['p','p','p','p','p','p','p','p'],
  [null,null,null,null,null,null,null,null],
  [null,null,null,null,null,null,null,null],
  [null,null,null,null,null,null,null,null],
  [null,null,null,null,null,null,null,null],
  ['P','P','P','P','P','P','P','P'],
  ['R','N','B','Q','K','B','N','R']
];

function clone(b) { return b.map(r => [...r]); }
function isUpper(p) { return p && p === p.toUpperCase(); }
function colOf(p) { return !p ? null : isUpper(p) ? 'white' : 'black'; }
function opp(c) { return c === 'white' ? 'black' : 'white'; }
function inB(r, c) { return r >= 0 && r < 8 && c >= 0 && c < 8; }

function kingPos(board, color) {
  const k = color === 'white' ? 'K' : 'k';
  for (let r = 0; r < 8; r++)
    for (let c = 0; c < 8; c++)
      if (board[r][c] === k) return [r, c];
  return null;
}

function attacked(board, r, c, byColor) {
  for (let fr = 0; fr < 8; fr++) {
    for (let fc = 0; fc < 8; fc++) {
      const p = board[fr][fc];
      if (!p || colOf(p) !== byColor) continue;
      const pt = p.toUpperCase();
      if (pt === 'P') {
        const d = byColor === 'white' ? -1 : 1;
        if (fr + d === r && (fc - 1 === c || fc + 1 === c)) return true;
      } else if (pt === 'N') {
        for (const [dr,dc] of [[-2,-1],[-2,1],[-1,-2],[-1,2],[1,-2],[1,2],[2,-1],[2,1]])
          if (fr+dr===r && fc+dc===c) return true;
      } else if (pt === 'K') {
        for (const [dr,dc] of [[-1,-1],[-1,0],[-1,1],[0,-1],[0,1],[1,-1],[1,0],[1,1]])
          if (fr+dr===r && fc+dc===c) return true;
      } else {
        const dirs = pt==='B'?[[-1,-1],[-1,1],[1,-1],[1,1]]:pt==='R'?[[-1,0],[1,0],[0,-1],[0,1]]:[[-1,-1],[-1,1],[1,-1],[1,1],[-1,0],[1,0],[0,-1],[0,1]];
        for (const [dr,dc] of dirs) {
          let nr=fr+dr,nc=fc+dc;
          while (inB(nr,nc)) {
            if (nr===r&&nc===c) return true;
            if (board[nr][nc]) break;
            nr+=dr; nc+=dc;
          }
        }
      }
    }
  }
  return false;
}

function inCheck(board, color) {
  const kp = kingPos(board, color);
  return kp ? attacked(board, kp[0], kp[1], opp(color)) : false;
}

function rawMoves(board, r, c, castling, ep) {
  const p = board[r][c]; if (!p) return [];
  const color = colOf(p); const pt = p.toUpperCase(); const moves = [];
  if (pt === 'P') {
    const dir = color==='white'?-1:1, start = color==='white'?6:1;
    if (inB(r+dir,c) && !board[r+dir][c]) { moves.push([r+dir,c]); if (r===start&&!board[r+2*dir][c]) moves.push([r+2*dir,c]); }
    for (const dc of [-1,1]) if (inB(r+dir,c+dc)) { const t=board[r+dir][c+dc]; if ((t&&colOf(t)!==color)||(ep&&ep[0]===r+dir&&ep[1]===c+dc)) moves.push([r+dir,c+dc]); }
  } else if (pt==='N') {
    for (const [dr,dc] of [[-2,-1],[-2,1],[-1,-2],[-1,2],[1,-2],[1,2],[2,-1],[2,1]]) { const nr=r+dr,nc=c+dc; if (inB(nr,nc)&&colOf(board[nr][nc])!==color) moves.push([nr,nc]); }
  } else if (pt==='K') {
    for (const [dr,dc] of [[-1,-1],[-1,0],[-1,1],[0,-1],[0,1],[1,-1],[1,0],[1,1]]) { const nr=r+dr,nc=c+dc; if (inB(nr,nc)&&colOf(board[nr][nc])!==color) moves.push([nr,nc]); }
    const rank=color==='white'?7:0, enemy=opp(color);
    if (r===rank&&c===4) {
      const ks=color==='white'?'K':'k', qs=color==='white'?'Q':'q';
      if (castling[ks]&&!board[rank][5]&&!board[rank][6]&&!attacked(board,rank,4,enemy)&&!attacked(board,rank,5,enemy)&&!attacked(board,rank,6,enemy)) moves.push([rank,6]);
      if (castling[qs]&&!board[rank][3]&&!board[rank][2]&&!board[rank][1]&&!attacked(board,rank,4,enemy)&&!attacked(board,rank,3,enemy)&&!attacked(board,rank,2,enemy)) moves.push([rank,2]);
    }
  } else {
    const dirs=pt==='B'?[[-1,-1],[-1,1],[1,-1],[1,1]]:pt==='R'?[[-1,0],[1,0],[0,-1],[0,1]]:[[-1,-1],[-1,1],[1,-1],[1,1],[-1,0],[1,0],[0,-1],[0,1]];
    for (const [dr,dc] of dirs) { let nr=r+dr,nc=c+dc; while(inB(nr,nc)){if(colOf(board[nr][nc])===color)break;moves.push([nr,nc]);if(board[nr][nc])break;nr+=dr;nc+=dc;} }
  }
  return moves;
}

function legalMoves(board, r, c, castling, ep) {
  const color = colOf(board[r][c]); if (!color) return [];
  return rawMoves(board,r,c,castling,ep).filter(([nr,nc])=>{ const nb=clone(board); applyMove(nb,r,c,nr,nc,ep,null); return !inCheck(nb,color); });
}

function allLegalMoves(board, color, castling, ep) {
  const moves = [];
  for (let r=0;r<8;r++) for (let c=0;c<8;c++) if (colOf(board[r][c])===color) legalMoves(board,r,c,castling,ep).forEach(m=>moves.push([r,c,...m]));
  return moves;
}

function applyMove(board, fr, fc, tr, tc, ep, promo) {
  const p=board[fr][fc]; const color=colOf(p); const pt=p.toUpperCase();
  if (pt==='P'&&ep&&tr===ep[0]&&tc===ep[1]) board[color==='white'?tr+1:tr-1][tc]=null;
  if (pt==='K') { if(fc===4&&tc===6){board[fr][5]=board[fr][7];board[fr][7]=null;} if(fc===4&&tc===2){board[fr][3]=board[fr][0];board[fr][0]=null;} }
  board[tr][tc]=promo||p; board[fr][fc]=null;
}

function makeMove(gs, fr, fc, tr, tc, promo) {
  const { board, turn, castling, ep } = gs;
  const p = board[fr][fc];
  if (!p || colOf(p)!==turn) return { error:'Not your piece' };
  const valid = legalMoves(board,fr,fc,castling,ep);
  if (!valid.some(([r,c])=>r===tr&&c===tc)) return { error:'Invalid move' };
  const pt = p.toUpperCase();
  const isPromo = pt==='P'&&(tr===0||tr===7);
  if (isPromo&&!promo) return { needsPromotion:true };
  const nb=clone(board); const captured=nb[tr][tc];
  let epCapture=null;
  if (pt==='P'&&ep&&tr===ep[0]&&tc===ep[1]) { const cr=turn==='white'?tr+1:tr-1; epCapture=nb[cr][tc]; }
  let newEp=null; if (pt==='P'&&Math.abs(tr-fr)===2) newEp=[(fr+tr)/2,fc];
  const nc={...castling};
  if (pt==='K'){if(turn==='white'){nc.K=false;nc.Q=false;}else{nc.k=false;nc.q=false;}}
  if (pt==='R'){if(fr===7&&fc===7)nc.K=false;if(fr===7&&fc===0)nc.Q=false;if(fr===0&&fc===7)nc.k=false;if(fr===0&&fc===0)nc.q=false;}
  applyMove(nb,fr,fc,tr,tc,ep,promo);
  const newTurn=opp(turn); const nextMoves=allLegalMoves(nb,newTurn,nc,newEp);
  const chk=inCheck(nb,newTurn);
  const status=nextMoves.length===0?(chk?'checkmate':'stalemate'):chk?'check':'playing';
  const capW=[...gs.capturedByWhite], capB=[...gs.capturedByBlack];
  const cap=captured||epCapture; if(cap){if(turn==='white')capW.push(cap);else capB.push(cap);}
  return { board:nb,turn:newTurn,castling:nc,ep:newEp,capturedByWhite:capW,capturedByBlack:capB,lastMove:{fr,fc,tr,tc},status,winner:status==='checkmate'?turn:null,inCheck:chk,checkKingPos:chk?kingPos(nb,newTurn):null };
}

// ═══════════════════════════════════════════════════════
// AI ENGINE
// ═══════════════════════════════════════════════════════

const PVAL = { P:100, N:320, B:330, R:500, Q:900, K:20000 };

const PST = {
  P:[[0,0,0,0,0,0,0,0],[50,50,50,50,50,50,50,50],[10,10,20,30,30,20,10,10],[5,5,10,25,25,10,5,5],[0,0,0,20,20,0,0,0],[5,-5,-10,0,0,-10,-5,5],[5,10,10,-20,-20,10,10,5],[0,0,0,0,0,0,0,0]],
  N:[[-50,-40,-30,-30,-30,-30,-40,-50],[-40,-20,0,0,0,0,-20,-40],[-30,0,10,15,15,10,0,-30],[-30,5,15,20,20,15,5,-30],[-30,0,15,20,20,15,0,-30],[-30,5,10,15,15,10,5,-30],[-40,-20,0,5,5,0,-20,-40],[-50,-40,-30,-30,-30,-30,-40,-50]],
  B:[[-20,-10,-10,-10,-10,-10,-10,-20],[-10,0,0,0,0,0,0,-10],[-10,0,5,10,10,5,0,-10],[-10,5,5,10,10,5,5,-10],[-10,0,10,10,10,10,0,-10],[-10,10,10,10,10,10,10,-10],[-10,5,0,0,0,0,5,-10],[-20,-10,-10,-10,-10,-10,-10,-20]],
  R:[[0,0,0,0,0,0,0,0],[5,10,10,10,10,10,10,5],[-5,0,0,0,0,0,0,-5],[-5,0,0,0,0,0,0,-5],[-5,0,0,0,0,0,0,-5],[-5,0,0,0,0,0,0,-5],[-5,0,0,0,0,0,0,-5],[0,0,0,5,5,0,0,0]],
  Q:[[-20,-10,-10,-5,-5,-10,-10,-20],[-10,0,0,0,0,0,0,-10],[-10,0,5,5,5,5,0,-10],[-5,0,5,5,5,5,0,-5],[0,0,5,5,5,5,0,-5],[-10,5,5,5,5,5,0,-10],[-10,0,5,0,0,0,0,-10],[-20,-10,-10,-5,-5,-10,-10,-20]],
  K:[[-30,-40,-40,-50,-50,-40,-40,-30],[-30,-40,-40,-50,-50,-40,-40,-30],[-30,-40,-40,-50,-50,-40,-40,-30],[-30,-40,-40,-50,-50,-40,-40,-30],[-20,-30,-30,-40,-40,-30,-30,-20],[-10,-20,-20,-20,-20,-20,-20,-10],[20,20,0,0,0,0,20,20],[20,30,10,0,0,10,30,20]]
};

function evalBoard(board, level) {
  let score = 0;
  for (let r=0;r<8;r++) for (let c=0;c<8;c++) {
    const p=board[r][c]; if (!p) continue;
    const w=isUpper(p); const pt=p.toUpperCase();
    let val=PVAL[pt]||0;
    if (level>=4&&PST[pt]) val+=w?PST[pt][r][c]:PST[pt][7-r][c];
    score+=w?val:-val;
  }
  return score;
}

function applyMoveAI(nb, fr, fc, tr, tc, nc, ep, color) {
  const p=nb[fr][fc]; const pt=p.toUpperCase(); let newEp=null;
  if (pt==='P'&&ep&&tr===ep[0]&&tc===ep[1]) nb[color==='white'?tr+1:tr-1][tc]=null;
  if (pt==='P'&&Math.abs(tr-fr)===2) newEp=[(fr+tr)/2,fc];
  if (pt==='K'){if(color==='white'){nc.K=false;nc.Q=false;}else{nc.k=false;nc.q=false;}if(fc===4&&tc===6){nb[fr][5]=nb[fr][7];nb[fr][7]=null;}if(fc===4&&tc===2){nb[fr][3]=nb[fr][0];nb[fr][0]=null;}}
  if (pt==='R'){if(fr===7&&fc===7)nc.K=false;if(fr===7&&fc===0)nc.Q=false;if(fr===0&&fc===7)nc.k=false;if(fr===0&&fc===0)nc.q=false;}
  const promo=(pt==='P'&&(tr===0||tr===7))?(color==='white'?'Q':'q'):null;
  nb[tr][tc]=promo||p; nb[fr][fc]=null;
  return newEp;
}

function minimax(board, depth, alpha, beta, isMax, castling, ep, level) {
  if (depth===0) return evalBoard(board,level);
  const color=isMax?'white':'black';
  const moves=allLegalMoves(board,color,castling,ep);
  if (!moves.length) return inCheck(board,color)?(isMax?-100000:100000):0;
  let best=isMax?-Infinity:Infinity;
  for (const [fr,fc,tr,tc] of moves) {
    const nb=clone(board); const nc={...castling};
    const newEp=applyMoveAI(nb,fr,fc,tr,tc,nc,ep,color);
    const score=minimax(nb,depth-1,alpha,beta,!isMax,nc,newEp,level);
    if (isMax){if(score>best)best=score;if(score>alpha)alpha=score;}else{if(score<best)best=score;if(score<beta)beta=score;}
    if (beta<=alpha) break;
  }
  return best;
}

function aiChooseMove(gs, level) {
  const { board, turn, castling, ep } = gs;
  let moves=[...allLegalMoves(board,turn,castling,ep)];
  if (!moves.length) return null;
  moves.sort(()=>Math.random()-0.5);
  if (level<=1) return moves[0];
  if (level===2) { const caps=moves.filter(([,,tr,tc])=>board[tr][tc]); return (caps.length?caps:moves)[0]; }
  const depth=level<=4?1:level<=6?2:level<=8?3:4;
  const isMax=turn==='white';
  if (level>=9) moves.sort((a,b)=>{ const va=board[a[2]][a[3]]?(PVAL[board[a[2]][a[3]].toUpperCase()]||0):0; const vb=board[b[2]][b[3]]?(PVAL[board[b[2]][b[3]].toUpperCase()]||0):0; return vb-va; });
  let best=moves[0], bestScore=isMax?-Infinity:Infinity;
  for (const [fr,fc,tr,tc] of moves) {
    const nb=clone(board); const nc={...castling};
    const newEp=applyMoveAI(nb,fr,fc,tr,tc,nc,ep,turn);
    const score=minimax(nb,depth-1,-Infinity,Infinity,!isMax,nc,newEp,level);
    if (isMax?score>bestScore:score<bestScore){bestScore=score;best=[fr,fc,tr,tc];}
  }
  return best;
}

// ═══════════════════════════════════════════════════════
// TIMERS
// ═══════════════════════════════════════════════════════

function startClocks(room) {
  if (!room.timeControl) { room.clocks=null; return; }
  room.clocks={ white:room.timeControl, black:room.timeControl, lastTick:Date.now(), interval:null };
  room.clocks.interval=setInterval(()=>{
    if (!room.clocks||!room.game) return;
    const g=room.game; if (g.status!=='playing'&&g.status!=='check'){stopClocks(room);return;}
    const elapsed=Date.now()-room.clocks.lastTick; const turn=g.turn;
    const tw=turn==='white'?Math.max(0,room.clocks.white-elapsed):room.clocks.white;
    const tb=turn==='black'?Math.max(0,room.clocks.black-elapsed):room.clocks.black;
    io.to(room.code).emit('time_update',{white:tw,black:tb});
    if (tw<=0&&turn==='white'){room.clocks.white=0;g.status='timeout';g.winner='black';stopClocks(room);io.to(room.code).emit('timeout',{loser:'white',winner:'black'});saveGameLog(room,'timeout');}
    else if (tb<=0&&turn==='black'){room.clocks.black=0;g.status='timeout';g.winner='white';stopClocks(room);io.to(room.code).emit('timeout',{loser:'black',winner:'white'});saveGameLog(room,'timeout');}
  },500);
}

function stopClocks(room) {
  if (room.clocks&&room.clocks.interval){clearInterval(room.clocks.interval);room.clocks.interval=null;}
}

function tickClock(room) {
  if (!room.clocks||!room.game) return;
  const elapsed=Date.now()-room.clocks.lastTick;
  room.clocks[room.game.turn]=Math.max(0,room.clocks[room.game.turn]-elapsed);
  room.clocks.lastTick=Date.now();
}

// ═══════════════════════════════════════════════════════
// GAME LOG HELPER
// ═══════════════════════════════════════════════════════

function saveGameLog(room, endReason) {
  if (!room.game) return;
  const users = loadUsers();
  const logEntry = {
    date: new Date().toISOString(),
    mode: room.mode,
    whiteName: room.names.white,
    blackName: room.names.black,
    winner: room.game.winner,
    endReason: endReason || room.game.status,
    timeControl: room.timeControl
  };
  // Save for white player if logged in
  if (room.whiteEmail && users[room.whiteEmail]) {
    const u = users[room.whiteEmail];
    u.gameLog = u.gameLog || [];
    u.gameLog.unshift({ ...logEntry, yourColor: 'white' });
    if (u.gameLog.length > 50) u.gameLog = u.gameLog.slice(0, 50);
    if (room.game.winner === 'white') u.stats.wins++;
    else if (room.game.winner === 'black') u.stats.losses++;
    else u.stats.draws++;
  }
  // Save for black player if logged in
  if (room.blackEmail && users[room.blackEmail]) {
    const u = users[room.blackEmail];
    u.gameLog = u.gameLog || [];
    u.gameLog.unshift({ ...logEntry, yourColor: 'black' });
    if (u.gameLog.length > 50) u.gameLog = u.gameLog.slice(0, 50);
    if (room.game.winner === 'black') u.stats.wins++;
    else if (room.game.winner === 'white') u.stats.losses++;
    else u.stats.draws++;
  }
  saveUsers(users);
}

// ═══════════════════════════════════════════════════════
// ROOM MANAGEMENT
// ═══════════════════════════════════════════════════════

const rooms = new Map();
const waitingQueues = new Map();

function genCode(){let c;do{c=Math.random().toString(36).substr(2,6).toUpperCase();}while(rooms.has(c));return c;}
function genId(){return Math.random().toString(36).substr(2,12);}
function genToken(){return Math.random().toString(36).substr(2,18)+Math.random().toString(36).substr(2,18);}

function makeRoom(opts){
  const code=genCode();
  const room={code,mode:opts.mode||'multiplayer',white:null,black:null,names:{white:'',black:''},
    whiteEmail:null,blackEmail:null,
    timeControl:opts.timeControl||null,clocks:null,ai:opts.ai||null,game:null,rematchVotes:null,
    tournamentId:opts.tournamentId||null,matchId:opts.matchId||null,
    reconnectTokens:{white:null,black:null},   // secure per-player tokens for mid-game rejoin
    disconnected:null,                          // {color,timer} when a player drops mid-game
  };
  rooms.set(code,room); return room;
}

function getRoomBySocket(id){for(const[,r]of rooms)if(r.white===id||r.black===id)return r;return null;}
function getColor(room,id){return room.white===id?'white':room.black===id?'black':null;}

function emitState(room){
  const g=room.game;
  io.to(room.code).emit('game_state',{board:g.board,turn:g.turn,status:g.status,winner:g.winner,lastMove:g.lastMove,capturedByWhite:g.capturedByWhite,capturedByBlack:g.capturedByBlack,inCheck:g.inCheck,checkKingPos:g.checkKingPos,timeWhite:room.clocks?room.clocks.white:null,timeBlack:room.clocks?room.clocks.black:null,whiteName:room.names.white,blackName:room.names.black});
}

function newGame(){
  return {board:INIT.map(r=>[...r]),turn:'white',castling:{K:true,Q:true,k:true,q:true},ep:null,capturedByWhite:[],capturedByBlack:[],lastMove:null,status:'playing',winner:null,inCheck:false,checkKingPos:null,pendingPromo:null};
}

function startGame(room){
  if (!rooms.has(room.code)) return;
  room.game=newGame();
  room.disconnected=null;
  // Fresh reconnect tokens each game
  room.reconnectTokens={white:genToken(),black:genToken()};
  startClocks(room);
  // Broadcast to room channel; each client identifies its color by socket.id
  io.to(room.code).emit('game_start',{
    whiteSocketId:room.white, blackSocketId:room.black,
    code:room.code, whiteName:room.names.white, blackName:room.names.black, timeControl:room.timeControl,
    reconnectTokens:room.reconnectTokens
  });
  emitState(room);
  if (room.mode==='pvc'&&room.ai.color==='white') setTimeout(()=>doAiMove(room),700);
}

function doToss(room,p1Id,p1Name,p2Id,p2Name,p1Email,p2Email){
  const p1White=Math.random()<0.5;
  room.white=p1White?p1Id:p2Id; room.black=p1White?p2Id:p1Id;
  room.names.white=p1White?p1Name:p2Name; room.names.black=p1White?p2Name:p1Name;
  room.whiteEmail=p1White?(p1Email||null):(p2Email||null);
  room.blackEmail=p1White?(p2Email||null):(p1Email||null);
  // Broadcast to the whole room channel so both players receive it regardless of socket ID changes.
  // Each client uses its own socket.id to determine which color it got.
  io.to(room.code).emit('toss_result',{
    whiteSocketId:room.white, blackSocketId:room.black,
    whiteName:room.names.white, blackName:room.names.black
  });
  setTimeout(()=>startGame(room),3500);
}

function doAiMove(room){
  const g=room.game; if(!g||(g.status!=='playing'&&g.status!=='check')) return;
  const move=aiChooseMove(g,room.ai.level); if(!move) return;
  const [fr,fc,tr,tc]=move; const p=g.board[fr][fc]; const pt=p.toUpperCase();
  const promo=(pt==='P'&&(tr===0||tr===7))?(room.ai.color==='white'?'Q':'q'):null;
  tickClock(room);
  if(room.clocks&&room.clocks[room.ai.color]<=0){
    room.clocks[room.ai.color]=0;g.status='timeout';g.winner=opp(room.ai.color);
    stopClocks(room);io.to(room.code).emit('timeout',{loser:room.ai.color,winner:opp(room.ai.color)});saveGameLog(room,'timeout');return;
  }
  const result=makeMove(g,fr,fc,tr,tc,promo);
  if(result.error)return;
  Object.assign(room.game,result);
  emitState(room);
  if(result.status==='checkmate'||result.status==='stalemate'){stopClocks(room);saveGameLog(room,result.status);}
}

// ═══════════════════════════════════════════════════════
// TOURNAMENT HELPERS
// ═══════════════════════════════════════════════════════

function buildBracket(size, players) {
  // players: array of {email, name}
  const shuffled = [...players].sort(() => Math.random() - 0.5);
  const matches = [];
  if (size === 4) {
    matches.push({matchId:'m0',round:'SF',p1:shuffled[0],p2:shuffled[1],winner:null,loser:null,feedsWinnerTo:'m2',winnerSlot:'p1',feedsLoserTo:'m3',loserSlot:'p1',roomCode:null,status:'pending'});
    matches.push({matchId:'m1',round:'SF',p1:shuffled[2],p2:shuffled[3],winner:null,loser:null,feedsWinnerTo:'m2',winnerSlot:'p2',feedsLoserTo:'m3',loserSlot:'p2',roomCode:null,status:'pending'});
    matches.push({matchId:'m2',round:'Final',p1:null,p2:null,winner:null,loser:null,feedsWinnerTo:null,feedsLoserTo:null,roomCode:null,status:'waiting'});
    matches.push({matchId:'m3',round:'3rd',p1:null,p2:null,winner:null,loser:null,feedsWinnerTo:null,feedsLoserTo:null,roomCode:null,status:'waiting'});
  } else if (size === 6) {
    // 3 groups → SF(A vs B winner) → Final(SF winner vs C winner); 3rd(SF loser vs C loser)
    matches.push({matchId:'m0',round:'Group A',p1:shuffled[0],p2:shuffled[1],winner:null,loser:null,feedsWinnerTo:'m3',winnerSlot:'p1',feedsLoserTo:null,loserSlot:null,roomCode:null,status:'pending'});
    matches.push({matchId:'m1',round:'Group B',p1:shuffled[2],p2:shuffled[3],winner:null,loser:null,feedsWinnerTo:'m3',winnerSlot:'p2',feedsLoserTo:null,loserSlot:null,roomCode:null,status:'pending'});
    matches.push({matchId:'m2',round:'Group C',p1:shuffled[4],p2:shuffled[5],winner:null,loser:null,feedsWinnerTo:'m4',winnerSlot:'p1',feedsLoserTo:'m5',loserSlot:'p2',roomCode:null,status:'pending'});
    matches.push({matchId:'m3',round:'SF',p1:null,p2:null,winner:null,loser:null,feedsWinnerTo:'m4',winnerSlot:'p2',feedsLoserTo:'m5',loserSlot:'p1',roomCode:null,status:'waiting'});
    matches.push({matchId:'m4',round:'Final',p1:null,p2:null,winner:null,loser:null,feedsWinnerTo:null,feedsLoserTo:null,roomCode:null,status:'waiting'});
    matches.push({matchId:'m5',round:'3rd',p1:null,p2:null,winner:null,loser:null,feedsWinnerTo:null,feedsLoserTo:null,roomCode:null,status:'waiting'});
  } else { // 8
    matches.push({matchId:'m0',round:'QF',p1:shuffled[0],p2:shuffled[1],winner:null,loser:null,feedsWinnerTo:'m4',winnerSlot:'p1',feedsLoserTo:null,loserSlot:null,roomCode:null,status:'pending'});
    matches.push({matchId:'m1',round:'QF',p1:shuffled[2],p2:shuffled[3],winner:null,loser:null,feedsWinnerTo:'m4',winnerSlot:'p2',feedsLoserTo:null,loserSlot:null,roomCode:null,status:'pending'});
    matches.push({matchId:'m2',round:'QF',p1:shuffled[4],p2:shuffled[5],winner:null,loser:null,feedsWinnerTo:'m5',winnerSlot:'p1',feedsLoserTo:null,loserSlot:null,roomCode:null,status:'pending'});
    matches.push({matchId:'m3',round:'QF',p1:shuffled[6],p2:shuffled[7],winner:null,loser:null,feedsWinnerTo:'m5',winnerSlot:'p2',feedsLoserTo:null,loserSlot:null,roomCode:null,status:'pending'});
    matches.push({matchId:'m4',round:'SF',p1:null,p2:null,winner:null,loser:null,feedsWinnerTo:'m6',winnerSlot:'p1',feedsLoserTo:'m7',loserSlot:'p1',roomCode:null,status:'waiting'});
    matches.push({matchId:'m5',round:'SF',p1:null,p2:null,winner:null,loser:null,feedsWinnerTo:'m6',winnerSlot:'p2',feedsLoserTo:'m7',loserSlot:'p2',roomCode:null,status:'waiting'});
    matches.push({matchId:'m6',round:'Final',p1:null,p2:null,winner:null,loser:null,feedsWinnerTo:null,feedsLoserTo:null,roomCode:null,status:'waiting'});
    matches.push({matchId:'m7',round:'3rd',p1:null,p2:null,winner:null,loser:null,feedsWinnerTo:null,feedsLoserTo:null,roomCode:null,status:'waiting'});
  }
  return matches;
}

function advanceBracket(tournamentId, matchId, winnerEmail) {
  const tournaments = loadTournaments();
  const t = tournaments[tournamentId];
  if (!t) return;
  const match = t.matches.find(m => m.matchId === matchId);
  if (!match) return;
  const loserEmail = match.p1.email === winnerEmail ? match.p2.email : match.p1.email;
  const winner = match.p1.email === winnerEmail ? match.p1 : match.p2;
  const loser = match.p1.email === winnerEmail ? match.p2 : match.p1;
  match.winner = winner;
  match.loser = loser;
  match.status = 'done';
  // Feed winner
  if (match.feedsWinnerTo) {
    const next = t.matches.find(m => m.matchId === match.feedsWinnerTo);
    if (next) { next[match.winnerSlot] = winner; if (next.p1 && next.p2) next.status = 'ready'; }
  }
  // Feed loser
  if (match.feedsLoserTo) {
    const next = t.matches.find(m => m.matchId === match.feedsLoserTo);
    if (next) { next[match.loserSlot] = loser; if (next.p1 && next.p2) next.status = 'ready'; }
  }
  // Check tournament complete
  const finalMatch = t.matches.find(m => m.round === 'Final');
  const thirdMatch = t.matches.find(m => m.round === '3rd');
  if (finalMatch && finalMatch.status === 'done' && (!thirdMatch || thirdMatch.status === 'done')) {
    t.status = 'complete';
    t.result = { first: finalMatch.winner, second: finalMatch.loser, third: thirdMatch ? thirdMatch.winner : null };
  }
  saveTournaments(tournaments);
  // Notify ready matches
  t.matches.filter(m => m.status === 'ready').forEach(m => {
    launchTournamentMatch(tournamentId, m.matchId);
  });
  // Broadcast update to all tournament participants
  broadcastTournamentUpdate(tournamentId);
}

function launchTournamentMatch(tournamentId, matchId) {
  const tournaments = loadTournaments();
  const t = tournaments[tournamentId];
  if (!t) return;
  const match = t.matches.find(m => m.matchId === matchId);
  if (!match || match.status !== 'ready' || match.roomCode) return;
  match.status = 'active';
  const room = makeRoom({ mode: 'multiplayer', tournamentId, matchId });
  match.roomCode = room.code;
  saveTournaments(tournaments);
  const s1Id = onlineSessions.get(match.p1.email);
  const s2Id = onlineSessions.get(match.p2.email);
  if (s1Id) { const s = io.sockets.sockets.get(s1Id); if (s) s.join(room.code); }
  if (s2Id) { const s = io.sockets.sockets.get(s2Id); if (s) s.join(room.code); }
  doToss(room, s1Id||'__offline__', match.p1.name, s2Id||'__offline__', match.p2.name, match.p1.email, match.p2.email);
  // Notify both players
  const payload = { tournamentId, matchId, matchRound: match.round, opponent: null };
  if (s1Id) { const s = io.sockets.sockets.get(s1Id); if (s) s.emit('tournament:match_ready', { ...payload, opponent: match.p2.name }); }
  if (s2Id) { const s = io.sockets.sockets.get(s2Id); if (s) s.emit('tournament:match_ready', { ...payload, opponent: match.p1.name }); }
}

function broadcastTournamentUpdate(tournamentId) {
  const tournaments = loadTournaments();
  const t = tournaments[tournamentId];
  if (!t) return;
  t.players.forEach(p => {
    const sid = onlineSessions.get(p.email);
    if (sid) { const s = io.sockets.sockets.get(sid); if (s) s.emit('tournament:updated', t); }
  });
}

function broadcastFriendStatus(email, online) {
  const users = loadUsers();
  const u = users[email];
  if (!u) return;
  (u.friends || []).forEach(friendEmail => {
    const sid = onlineSessions.get(friendEmail);
    if (sid) {
      const s = io.sockets.sockets.get(sid);
      if (s) s.emit('friends:online_status', { email, name: u.name, online });
    }
  });
}

// ═══════════════════════════════════════════════════════
// SOCKET HANDLERS
// ═══════════════════════════════════════════════════════

io.on('connection', (socket) => {
  console.log('[+]', socket.id);
  let sessionEmail = null; // email of logged-in user for this socket

  // ── AUTH ──────────────────────────────────────────────

  socket.on('auth:register', ({ name, gender, email, pin }) => {
    if (!name || !email || !pin) return socket.emit('auth:error', 'All fields required.');
    if (!/^\d{4}$/.test(pin)) return socket.emit('auth:error', 'PIN must be 4 digits.');
    if (!/^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(email)) return socket.emit('auth:error', 'Invalid email.');
    const users = loadUsers();
    if (users[email]) return socket.emit('auth:error', 'Email already registered.');
    users[email] = { userId: genId(), name: name.trim(), gender: gender || 'other', email, pin, createdAt: new Date().toISOString(), friends: [], friendRequests: { incoming: [], outgoing: [] }, gameLog: [], stats: { wins: 0, losses: 0, draws: 0 } };
    saveUsers(users);
    socket.emit('auth:registered', { name: users[email].name, email });
  });

  socket.on('auth:login', ({ email, pin }) => {
    const users = loadUsers();
    const u = users[email];
    if (!u || u.pin !== pin) return socket.emit('auth:error', 'Invalid email or PIN.');
    sessionEmail = email;
    onlineSessions.set(email, socket.id);
    broadcastFriendStatus(email, true);
    // Build friends list with online status
    const friendsList = (u.friends || []).map(fe => {
      const fu = users[fe];
      return { email: fe, name: fu ? fu.name : fe, online: onlineSessions.has(fe) };
    });
    // Pending incoming requests
    const incoming = (u.friendRequests?.incoming || []).map(fe => { const fu = users[fe]; return { email: fe, name: fu ? fu.name : fe }; });
    socket.emit('auth:logged_in', { userId: u.userId, name: u.name, email, gender: u.gender, stats: u.stats, gameLog: u.gameLog || [], friends: friendsList, incomingRequests: incoming });
  });

  socket.on('auth:restore_session', ({ email, pin }) => {
    const users = loadUsers();
    const u = users[email];
    if (!u || u.pin !== pin) return socket.emit('auth:error', 'Session expired.');
    sessionEmail = email;
    onlineSessions.set(email, socket.id);
    broadcastFriendStatus(email, true);
    const friendsList = (u.friends || []).map(fe => { const fu = users[fe]; return { email: fe, name: fu ? fu.name : fe, online: onlineSessions.has(fe) }; });
    const incoming = (u.friendRequests?.incoming || []).map(fe => { const fu = users[fe]; return { email: fe, name: fu ? fu.name : fe }; });
    socket.emit('auth:session_restored', { userId: u.userId, name: u.name, email, gender: u.gender, stats: u.stats, gameLog: u.gameLog || [], friends: friendsList, incomingRequests: incoming });
  });

  socket.on('auth:logout', () => {
    if (sessionEmail) { onlineSessions.delete(sessionEmail); broadcastFriendStatus(sessionEmail, false); sessionEmail = null; }
    socket.emit('auth:logged_out');
  });

  // ── FRIENDS ───────────────────────────────────────────

  socket.on('friends:send_request', ({ toEmail }) => {
    if (!sessionEmail) return socket.emit('auth:error', 'Not logged in.');
    const users = loadUsers();
    const from = users[sessionEmail];
    const to = users[toEmail];
    if (!to) return socket.emit('friends:error', 'User not found.');
    if (from.friends.includes(toEmail)) return socket.emit('friends:error', 'Already friends.');
    if (from.friendRequests.outgoing.includes(toEmail)) return socket.emit('friends:error', 'Request already sent.');
    from.friendRequests.outgoing.push(toEmail);
    to.friendRequests.incoming.push(sessionEmail);
    saveUsers(users);
    socket.emit('friends:request_sent', { toEmail, toName: to.name });
    const toSid = onlineSessions.get(toEmail);
    if (toSid) { const s = io.sockets.sockets.get(toSid); if (s) s.emit('friends:request_received', { fromEmail: sessionEmail, fromName: from.name }); }
  });

  socket.on('friends:accept', ({ fromEmail }) => {
    if (!sessionEmail) return;
    const users = loadUsers();
    const me = users[sessionEmail];
    const them = users[fromEmail];
    if (!me || !them) return;
    me.friendRequests.incoming = me.friendRequests.incoming.filter(e => e !== fromEmail);
    them.friendRequests.outgoing = them.friendRequests.outgoing.filter(e => e !== sessionEmail);
    if (!me.friends.includes(fromEmail)) me.friends.push(fromEmail);
    if (!them.friends.includes(sessionEmail)) them.friends.push(sessionEmail);
    saveUsers(users);
    socket.emit('friends:list_updated', { friends: me.friends.map(fe => { const fu = users[fe]; return { email: fe, name: fu ? fu.name : fe, online: onlineSessions.has(fe) }; }) });
    const theirSid = onlineSessions.get(fromEmail);
    if (theirSid) { const s = io.sockets.sockets.get(theirSid); if (s) s.emit('friends:list_updated', { friends: them.friends.map(fe => { const fu = users[fe]; return { email: fe, name: fu ? fu.name : fe, online: onlineSessions.has(fe) }; }) }); }
  });

  socket.on('friends:decline', ({ fromEmail }) => {
    if (!sessionEmail) return;
    const users = loadUsers();
    const me = users[sessionEmail];
    const them = users[fromEmail];
    if (me) me.friendRequests.incoming = me.friendRequests.incoming.filter(e => e !== fromEmail);
    if (them) them.friendRequests.outgoing = them.friendRequests.outgoing.filter(e => e !== sessionEmail);
    saveUsers(users);
  });

  socket.on('friends:challenge', ({ toEmail }) => {
    if (!sessionEmail) return;
    const users = loadUsers();
    const from = users[sessionEmail];
    const toSid = onlineSessions.get(toEmail);
    if (!toSid) return socket.emit('friends:error', 'Friend is offline.');
    const s = io.sockets.sockets.get(toSid);
    if (s) s.emit('friends:challenge_received', { fromEmail: sessionEmail, fromName: from ? from.name : sessionEmail });
  });

  socket.on('friends:challenge_respond', ({ fromEmail, accept }) => {
    if (!sessionEmail) return;
    const fromSid = onlineSessions.get(fromEmail);
    if (!accept) {
      if (fromSid) { const s = io.sockets.sockets.get(fromSid); if (s) s.emit('friends:challenge_declined', { byEmail: sessionEmail }); }
      return;
    }
    const users = loadUsers();
    const fromUser = users[fromEmail];
    const toUser = users[sessionEmail];
    if (!fromSid) return socket.emit('friends:error', 'Friend went offline.');
    const room = makeRoom({ mode: 'multiplayer', timeControl: null });
    const fromSock = io.sockets.sockets.get(fromSid);
    if (fromSock) fromSock.join(room.code);
    socket.join(room.code);
    doToss(room, fromSid, fromUser ? fromUser.name : fromEmail, socket.id, toUser ? toUser.name : sessionEmail, fromEmail, sessionEmail);
  });

  // ── TOURNAMENT ────────────────────────────────────────

  socket.on('tournament:create', ({ name, size }) => {
    if (!sessionEmail) return socket.emit('auth:error', 'Login required.');
    const validSizes = [4, 6, 8];
    if (!validSizes.includes(size)) return socket.emit('tournament:error', 'Invalid size.');
    const users = loadUsers();
    const creator = users[sessionEmail];
    if (!creator) return;
    const tournaments = loadTournaments();
    const tid = 'T' + genId().toUpperCase().substr(0,6);
    tournaments[tid] = {
      tournamentId: tid, name: name || `${creator.name}'s Tournament`,
      size, creatorEmail: sessionEmail, status: 'open',
      players: [{ email: sessionEmail, name: creator.name }],
      matches: [], result: null
    };
    saveTournaments(tournaments);
    socket.emit('tournament:created', tournaments[tid]);
  });

  socket.on('tournament:join', ({ tournamentId }) => {
    if (!sessionEmail) return socket.emit('auth:error', 'Login required.');
    const tournaments = loadTournaments();
    const t = tournaments[tournamentId];
    if (!t) return socket.emit('tournament:error', 'Tournament not found.');
    if (t.status !== 'open') return socket.emit('tournament:error', 'Tournament not open.');
    if (t.players.find(p => p.email === sessionEmail)) return socket.emit('tournament:error', 'Already joined.');
    if (t.players.length >= t.size) return socket.emit('tournament:error', 'Tournament full.');
    const users = loadUsers();
    const u = users[sessionEmail];
    t.players.push({ email: sessionEmail, name: u ? u.name : sessionEmail });
    saveTournaments(tournaments);
    broadcastTournamentUpdate(tournamentId);
    socket.emit('tournament:joined', t);
  });

  socket.on('tournament:start', ({ tournamentId }) => {
    if (!sessionEmail) return;
    const tournaments = loadTournaments();
    const t = tournaments[tournamentId];
    if (!t || t.creatorEmail !== sessionEmail) return socket.emit('tournament:error', 'Not your tournament.');
    if (t.players.length !== t.size) return socket.emit('tournament:error', `Need ${t.size} players.`);
    if (t.status !== 'open') return socket.emit('tournament:error', 'Already started.');
    t.matches = buildBracket(t.size, t.players);
    t.status = 'active';
    saveTournaments(tournaments);
    broadcastTournamentUpdate(tournamentId);
    // Launch first round matches
    t.matches.filter(m => m.status === 'pending').forEach(m => {
      m.status = 'ready';
      launchTournamentMatch(tournamentId, m.matchId);
    });
    saveTournaments(tournaments);
  });

  socket.on('tournament:get', ({ tournamentId }) => {
    const tournaments = loadTournaments();
    const t = tournaments[tournamentId];
    if (t) socket.emit('tournament:updated', t);
  });

  socket.on('tournament:list', () => {
    const tournaments = loadTournaments();
    const list = Object.values(tournaments).filter(t => t.status === 'open').map(t => ({ tournamentId: t.tournamentId, name: t.name, size: t.size, joined: t.players.length, creatorName: t.players[0]?.name || '' }));
    socket.emit('tournament:list', list);
  });

  // ── GAME ──────────────────────────────────────────────

  socket.on('create_room',({name,timeControl})=>{
    if(getRoomBySocket(socket.id))return;
    const room=makeRoom({mode:'multiplayer',timeControl:timeControl||null});
    room.white=socket.id; room._creatorName=name||'Player 1';
    room.whiteEmail=sessionEmail||null;
    socket.join(room.code);
    socket.emit('room_created',{code:room.code});
  });

  socket.on('join_room',({code,name})=>{
    const room=rooms.get((code||'').toUpperCase().trim());
    if(!room){socket.emit('join_error','Room not found');return;}
    if(room.mode!=='multiplayer'){socket.emit('join_error','Room not found');return;}
    if(room.game){socket.emit('join_error','Game already started');return;}
    if(room.black!==null&&room.black!==undefined){socket.emit('join_error','Room is full');return;}
    // Clear any pending cleanup timer since someone joined
    if(room._cleanupTimer){clearTimeout(room._cleanupTimer);room._cleanupTimer=null;}
    // If creator socket dropped but room survived, creator slot may be null — still start game
    // (creator will see "opponent disconnected" if they don't reconnect in time)
    socket.join(room.code);
    const creatorId=room.white||'__gone__';
    doToss(room,creatorId,room._creatorName||'Player 1',socket.id,name||'Player 2',room.whiteEmail,sessionEmail||null);
  });

  socket.on('quick_match',({name,timeControl})=>{
    if(getRoomBySocket(socket.id))return;
    const key=String(timeControl??'unlimited');
    if(waitingQueues.has(key)){
      const w=waitingQueues.get(key); waitingQueues.delete(key);
      if(!w.socket.connected){waitingQueues.set(key,{socket,name:name||'Player',email:sessionEmail});socket.emit('waiting',{code:'------'});return;}
      const room=makeRoom({mode:'multiplayer',timeControl:timeControl||null});
      w.socket.join(room.code); socket.join(room.code);
      doToss(room,w.socket.id,w.name,socket.id,name||'Player',w.email||null,sessionEmail||null);
    } else {
      const room=makeRoom({mode:'multiplayer',timeControl:timeControl||null});
      room.white=socket.id; room._creatorName=name||'Player';
      room.whiteEmail=sessionEmail||null;
      socket.join(room.code);
      waitingQueues.set(key,{socket,name:name||'Player',email:sessionEmail});
      socket.emit('waiting',{code:room.code});
    }
  });

  socket.on('pvc_game',({name,level,timeControl})=>{
    if(getRoomBySocket(socket.id))return;
    const aiLevel=Math.min(10,Math.max(1,parseInt(level)||5));
    const room=makeRoom({mode:'pvc',timeControl:timeControl||null});
    const playerWhite=Math.random()<0.5;
    const playerColor=playerWhite?'white':'black'; const aiColor=opp(playerColor);
    room.white=playerWhite?socket.id:'AI'; room.black=playerWhite?'AI':socket.id;
    room.names.white=playerWhite?(name||'You'):'Computer'; room.names.black=playerWhite?'Computer':(name||'You');
    if(playerWhite)room.whiteEmail=sessionEmail||null; else room.blackEmail=sessionEmail||null;
    room.ai={color:aiColor,level:aiLevel};
    socket.join(room.code);
    io.to(room.code).emit('toss_result',{whiteSocketId:room.white,blackSocketId:room.black,whiteName:room.names.white,blackName:room.names.black});
    setTimeout(()=>startGame(room),3500);
  });

  socket.on('select_piece',({row,col})=>{
    const room=getRoomBySocket(socket.id); if(!room||!room.game)return;
    const color=getColor(room,socket.id); const g=room.game;
    if(g.turn!==color)return; if(g.status!=='playing'&&g.status!=='check')return;
    socket.emit('valid_moves',{from:[row,col],moves:legalMoves(g.board,row,col,g.castling,g.ep)});
  });

  socket.on('make_move',({fr,fc,tr,tc})=>{
    const room=getRoomBySocket(socket.id); if(!room||!room.game)return;
    const color=getColor(room,socket.id); const g=room.game;
    if(!color||g.turn!==color)return; if(g.pendingPromo)return;
    const p=g.board[fr][fc]; const pt=p&&p.toUpperCase();
    const isPromoMove=pt==='P'&&(tr===0||tr===7);
    if(!isPromoMove){
      tickClock(room);
      if(room.clocks&&room.clocks[color]<=0){room.clocks[color]=0;g.status='timeout';g.winner=opp(color);stopClocks(room);io.to(room.code).emit('timeout',{loser:color,winner:opp(color)});saveGameLog(room,'timeout');return;}
    }
    const result=makeMove(g,fr,fc,tr,tc,null);
    if(result.error){socket.emit('invalid_move',result.error);return;}
    if(result.needsPromotion){g.pendingPromo={fr,fc,tr,tc};socket.emit('needs_promotion');return;}
    Object.assign(room.game,result);
    emitState(room);
    if(result.status==='checkmate'||result.status==='stalemate'){
      stopClocks(room);saveGameLog(room,result.status);
      if(room.tournamentId)advanceBracket(room.tournamentId,room.matchId,result.winner==='white'?room.whiteEmail:room.blackEmail);
    }
    if(room.mode==='pvc'&&(room.game.status==='playing'||room.game.status==='check')&&room.game.turn===room.ai.color){
      const delay=Math.min(1200,300+room.ai.level*80);
      setTimeout(()=>doAiMove(room),delay);
    }
  });

  socket.on('promote',({piece})=>{
    const room=getRoomBySocket(socket.id); if(!room||!room.game||!room.game.pendingPromo)return;
    const color=getColor(room,socket.id); const g=room.game;
    if(g.turn!==color)return;
    tickClock(room);
    if(room.clocks&&room.clocks[color]<=0){room.clocks[color]=0;g.status='timeout';g.winner=opp(color);stopClocks(room);io.to(room.code).emit('timeout',{loser:color,winner:opp(color)});saveGameLog(room,'timeout');return;}
    const {fr,fc,tr,tc}=g.pendingPromo; g.pendingPromo=null;
    const valid=color==='white'?['Q','R','B','N']:['q','r','b','n'];
    const promo=valid.includes(piece)?piece:(color==='white'?'Q':'q');
    const result=makeMove(g,fr,fc,tr,tc,promo);
    if(result.error)return;
    Object.assign(room.game,result);
    emitState(room);
    if(result.status==='checkmate'||result.status==='stalemate'){
      stopClocks(room);saveGameLog(room,result.status);
      if(room.tournamentId)advanceBracket(room.tournamentId,room.matchId,result.winner==='white'?room.whiteEmail:room.blackEmail);
    }
    if(room.mode==='pvc'&&(room.game.status==='playing'||room.game.status==='check')&&room.game.turn===room.ai.color)
      setTimeout(()=>doAiMove(room),600);
  });

  socket.on('rematch',()=>{
    const room=getRoomBySocket(socket.id); if(!room||!room.game)return;
    if(room.tournamentId)return; // no rematch in tournament
    if(room.mode==='pvc'){
      stopClocks(room);
      const pc=getColor(room,socket.id); const newPc=opp(pc); const newAi=opp(newPc);
      room.ai.color=newAi;
      if(newPc==='white'){room.white=socket.id;room.black='AI';room.names.white=room.names[pc];room.names.black='Computer';}
      else{room.white='AI';room.black=socket.id;room.names.white='Computer';room.names.black=room.names[pc];}
      io.to(room.code).emit('toss_result',{whiteSocketId:room.white,blackSocketId:room.black,whiteName:room.names.white,blackName:room.names.black});
      setTimeout(()=>startGame(room),3500); return;
    }
    if(!room.rematchVotes)room.rematchVotes=new Set();
    room.rematchVotes.add(socket.id);
    if(room.rematchVotes.size>=2){
      room.rematchVotes=null; stopClocks(room);
      doToss(room,room.white,room.names.white,room.black,room.names.black,room.whiteEmail,room.blackEmail);
    } else { socket.to(room.code).emit('rematch_requested'); }
  });

  socket.on('rejoin_game',({code,color,token})=>{
    const room=rooms.get((code||'').toUpperCase().trim());
    if(!room||!room.game){socket.emit('rejoin_failed','Game no longer available.');return;}
    if(!room.disconnected||room.disconnected.color!==color){socket.emit('rejoin_failed','No reconnection pending.');return;}
    if(!room.reconnectTokens||room.reconnectTokens[color]!==token){socket.emit('rejoin_failed','Invalid token.');return;}
    // Cancel the 90-second abandon timer
    if(room.disconnected.timer){clearTimeout(room.disconnected.timer);room.disconnected.timer=null;}
    room.disconnected=null;
    // Restore socket in room
    if(color==='white'){room.white=socket.id;if(sessionEmail)room.whiteEmail=sessionEmail;}
    else{room.black=socket.id;if(sessionEmail)room.blackEmail=sessionEmail;}
    socket.join(room.code);
    // Resume clocks from where they paused
    if(room.clocks){room.clocks.lastTick=Date.now();startClocks(room);}
    // Send current game state to the rejoining player
    socket.emit('game_rejoined',{color,code:room.code,whiteName:room.names.white,blackName:room.names.black,timeControl:room.timeControl,reconnectToken:token});
    emitState(room);
    // Tell the waiting opponent their partner is back
    socket.to(room.code).emit('opponent_reconnected');
    console.log(`[rejoin] ${color} rejoined room ${room.code}`);
  });

  socket.on('rejoin_room',({code})=>{
    // Creator reconnects to their waiting room after a socket drop
    const room=rooms.get((code||'').toUpperCase().trim());
    if(!room||room.game) return; // room gone or game started — can't rejoin
    if(room._creatorReconnectEmail&&room._creatorReconnectEmail===sessionEmail){
      room.white=socket.id; room.whiteEmail=sessionEmail;
      socket.join(room.code);
      socket.emit('room_created',{code:room.code});
    }
  });

  socket.on('disconnect',()=>{
    console.log('[-]',socket.id);
    if(sessionEmail&&onlineSessions.get(sessionEmail)===socket.id){
      onlineSessions.delete(sessionEmail);
      broadcastFriendStatus(sessionEmail,false);
    }
    for(const[key,e]of waitingQueues){if(e.socket.id===socket.id){waitingQueues.delete(key);break;}}
    const room=getRoomBySocket(socket.id);
    if(!room) return;
    const color=getColor(room,socket.id);
    stopClocks(room);
    const gameActive=room.game&&(room.game.status==='playing'||room.game.status==='check');
    if(gameActive&&room.mode==='multiplayer'){
      // ── Mid-game disconnect: give 90 seconds to rejoin ──
      // Null out the slot so getRoomBySocket won't match stale id
      if(color==='white') room.white=null; else room.black=null;
      // Notify the opponent — they see a countdown
      socket.to(room.code).emit('opponent_disconnected_temp',{color,seconds:90});
      // 90-second abandon timer
      const timer=setTimeout(()=>{
        if(!rooms.has(room.code)) return;
        if(room.disconnected&&room.disconnected.color===color){
          // They never came back — opponent wins
          if(room.game){room.game.status='abandoned';room.game.winner=opp(color);}
          saveGameLog(room,'abandoned');
          io.to(room.code).emit('opponent_abandoned',{loser:color,winner:opp(color)});
          rooms.delete(room.code);
        }
      },90000);
      room.disconnected={color,timer};
    } else if(room.game){
      // Game finished or PvC — just clean up
      socket.to(room.code).emit('opponent_disconnected');
      rooms.delete(room.code);
    } else {
      // Pre-game lobby: keep room alive 90s for creator reconnect
      if(color==='white'){ room._creatorReconnectEmail=room.whiteEmail; room.white=null; }
      else room.black=null;
      room._cleanupTimer=setTimeout(()=>{ if(rooms.has(room.code)&&!room.game) rooms.delete(room.code); },90000);
    }
  });
});

server.listen(PORT,()=>console.log(`\n  Chess 3D → http://localhost:${PORT}\n`));
