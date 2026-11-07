// Blockade online server: node server.js  (нужен пакет ws, переменная BOT_TOKEN для Telegram)
const http=require('http'),fs=require('fs'),path=require('path'),crypto=require('crypto');
const {WebSocketServer}=require('ws');
const PORT=process.env.PORT||3000,TOKEN=process.env.BOT_TOKEN||'',T0=180000;
const DB=path.join(__dirname,'ratings.json');
let ratings={};try{ratings=JSON.parse(fs.readFileSync(DB,'utf8'));}catch(e){}
const saveR=()=>fs.writeFile(DB,JSON.stringify(ratings),()=>{});
const getR=id=>ratings[id]||800;

const srv=http.createServer((q,s)=>{
  if(q.url==='/health'){s.end('ok');return;}
  fs.readFile(path.join(__dirname,'index.html'),(e,d)=>{
    if(e){s.writeHead(500);return s.end('index.html not found');}
    s.writeHead(200,{'Content-Type':'text/html; charset=utf-8'});s.end(d);
  });
});
const wss=new WebSocketServer({server:srv,maxPayload:4096});

// ---------- Правила (канонические координаты: игрок 0 снизу, идёт к ряду 0) ----------
const N=9,D=[[1,0],[-1,0],[0,1],[0,-1]];
const inside=(r,c)=>r>=0&&r<N&&c>=0&&c<N;
const grid=()=>Array.from({length:8},()=>Array(8).fill(0));
function blocked(r,c,nr,nc,H,V){
  if(nr!==r){const a=Math.min(r,nr);return (c<8&&H[a][c]>0)||(c>0&&H[a][c-1]>0);}
  const b=Math.min(c,nc);return (r<8&&V[r][b]>0)||(r>0&&V[r-1][b]>0);
}
function moves(me,opp,H,V){
  const out=[];
  for(const[dr,dc]of D){
    const nr=me.r+dr,nc=me.c+dc;
    if(!inside(nr,nc)||blocked(me.r,me.c,nr,nc,H,V))continue;
    if(nr===opp.r&&nc===opp.c){
      const jr=nr+dr,jc=nc+dc;
      if(inside(jr,jc)&&!blocked(nr,nc,jr,jc,H,V))out.push({r:jr,c:jc});
      else for(const[pr,pc]of D){
        if(pr*dr+pc*dc!==0)continue;
        const sr=nr+pr,sc=nc+pc;
        if(inside(sr,sc)&&!blocked(nr,nc,sr,sc,H,V))out.push({r:sr,c:sc});
      }
    }else out.push({r:nr,c:nc});
  }
  return out;
}
function pathLen(from,goal,H,V){
  const d=Array.from({length:N},()=>Array(N).fill(-1)),q=[[from.r,from.c]];d[from.r][from.c]=0;
  for(let i=0;i<q.length;i++){
    const[r,c]=q[i];if(r===goal)return d[r][c];
    for(const[dr,dc]of D){const nr=r+dr,nc=c+dc;
      if(inside(nr,nc)&&d[nr][nc]<0&&!blocked(r,c,nr,nc,H,V)){d[nr][nc]=d[r][c]+1;q.push([nr,nc]);}}
  }
  return Infinity;
}
function canWall(g,o,r,c){
  if((o!=='h'&&o!=='v')||r<0||c<0||r>7||c>7)return false;
  const{H,V}=g;if(H[r][c]||V[r][c])return false;
  if(o==='h'){if((c>0&&H[r][c-1])||(c<7&&H[r][c+1]))return false;}
  else if((r>0&&V[r-1][c])||(r<7&&V[r+1][c]))return false;
  const t=o==='h'?H:V;t[r][c]=9;
  const ok=pathLen(g.pos[0],0,H,V)<Infinity&&pathLen(g.pos[1],8,H,V)<Infinity;t[r][c]=0;return ok;
}

// ---------- Проверка пользователя Telegram ----------
function verify(initData){
  try{
    const p=new URLSearchParams(initData),hash=p.get('hash');p.delete('hash');
    const check=[...p.entries()].map(([k,v])=>`${k}=${v}`).sort().join('\n');
    const secret=crypto.createHmac('sha256','WebAppData').update(TOKEN).digest();
    const h=crypto.createHmac('sha256',secret).update(check).digest('hex');
    if(!hash||h!==hash)return null;
    if(Date.now()/1000-Number(p.get('auth_date'))>86400)return null;
    const u=JSON.parse(p.get('user'));return{id:'tg'+u.id,name:String(u.first_name||'Игрок').slice(0,20)};
  }catch(e){return null;}
}

// ---------- Игры ----------
const queue=[];
const send=(ws,o)=>{if(ws.readyState===1)ws.send(JSON.stringify(o));};
function flipW(M,i){
  const out=grid();
  for(let r=0;r<8;r++)for(let c=0;c<8;c++){
    const v=M[r][c];if(!v)continue;const rel=(v-1===i)?1:2;
    if(i===1)out[7-r][7-c]=rel;else out[r][c]=rel;
  }
  return out;
}
function view(g,i){
  const f=p=>i===1?{r:8-p.r,c:8-p.c}:{r:p.r,c:p.c};
  return{t:'state',me:f(g.pos[i]),opp:f(g.pos[1-i]),H:flipW(g.H,i),V:flipW(g.V,i),
    left:{p:g.left[i],a:g.left[1-i]},turn:g.turn===i?'p':'a',
    tm:{p:Math.max(0,g.tm[i]),a:Math.max(0,g.tm[1-i])},started:g.started};
}
const push=g=>g.p.forEach((w,i)=>send(w,view(g,i)));
function spend(g){const n=Date.now();if(g.started)g.tm[g.turn]-=n-g.last;g.last=n;}

function startGame(pair){
  const g={p:pair,pos:[{r:8,c:4},{r:0,c:4}],H:grid(),V:grid(),left:[10,10],turn:0,tm:[T0,T0],started:false,last:Date.now(),over:false};
  pair.forEach((w,i)=>{w.game=g;const o=pair[1-i].user;send(w,{t:'start',col:i,opp:{name:o.name,rating:getR(o.id)}});});
  push(g);
  g.timer=setInterval(()=>{if(g.over)return;spend(g);if(g.tm[g.turn]<=0)finish(g,1-g.turn,'time');},250);
}
function finish(g,winner,why){
  if(g.over)return;g.over=true;clearInterval(g.timer);
  const ids=g.p.map(w=>w.user.id),ra=getR(ids[0]),rb=getR(ids[1]);
  const E=1/(1+Math.pow(10,(rb-ra)/400)),d=Math.round(32*((winner===0?1:0)-E));
  ratings[ids[0]]=Math.max(100,ra+d);ratings[ids[1]]=Math.max(100,rb-d);saveR();
  g.p.forEach((w,i)=>{
    const win=winner===i;
    const text={goal:win?'ты дошёл до цели':'соперник дошёл до цели',time:win?'у соперника вышло время':'у тебя вышло время',
      resign:win?'соперник сдался или отключился':'ты сдался'}[why];
    send(w,{t:'end',win,why:text,rating:ratings[ids[i]],delta:ratings[ids[i]]-(i===0?ra:rb)});
    w.game=null;
  });
}

wss.on('connection',ws=>{
  ws.user=null;ws.game=null;
  ws.on('message',raw=>{
    let m;try{m=JSON.parse(raw);}catch(e){return;}
    if(m.t==='auth'){
      const u=TOKEN?verify(String(m.initData||'')):{id:'dev'+Math.random().toString(36).slice(2,8),name:String(m.name||'Игрок').slice(0,20)};
      if(!u)return send(ws,{t:'err',msg:'Ошибка авторизации: открой игру из Telegram'});
      ws.user=u;return send(ws,{t:'hello',rating:getR(u.id)});
    }
    if(!ws.user)return;
    if(m.t==='find'){
      if(ws.game||queue.includes(ws))return;
      let bi=-1,bd=1e9;
      queue.forEach((q,i)=>{if(q.user.id===ws.user.id)return;const d=Math.abs(getR(q.user.id)-getR(ws.user.id));if(d<bd){bd=d;bi=i;}});
      if(bi<0){queue.push(ws);return send(ws,{t:'wait'});}
      const o=queue.splice(bi,1)[0];startGame(Math.random()<0.5?[ws,o]:[o,ws]);
    }else if(m.t==='cancel'){const i=queue.indexOf(ws);if(i>=0)queue.splice(i,1);}
    else if(m.t==='resign'){const g=ws.game;if(g&&!g.over)finish(g,1-g.p.indexOf(ws),'resign');}
    else if(m.t==='move'||m.t==='wall'){
      const g=ws.game;if(!g||g.over)return;
      const i=g.p.indexOf(ws);if(g.turn!==i)return;
      spend(g);if(g.tm[i]<=0)return finish(g,1-i,'time');
      const r=m.r|0,c=m.c|0;
      if(m.t==='move'){
        if(!moves(g.pos[i],g.pos[1-i],g.H,g.V).some(x=>x.r===r&&x.c===c))return send(ws,view(g,i));
        g.pos[i]={r,c};if(r===(i===0?0:8)){return finish(g,i,'goal');}
      }else{
        if(g.left[i]<=0||!canWall(g,m.o,r,c))return send(ws,view(g,i));
        (m.o==='h'?g.H:g.V)[r][c]=i+1;g.left[i]--;
      }
      if(i===0)g.started=true;
      g.last=Date.now();g.turn=1-i;push(g);
    }
  });
  ws.on('close',()=>{
    const i=queue.indexOf(ws);if(i>=0)queue.splice(i,1);
    const g=ws.game;if(g&&!g.over)finish(g,1-g.p.indexOf(ws),'resign');
  });
});
srv.listen(PORT,()=>console.log('Blockade server on :'+PORT));
