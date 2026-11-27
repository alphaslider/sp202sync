(()=>{
const $=id=>document.getElementById(id),NUM_BANKS=4,BANK_NAMES=["A","B","C","D"],BEAT_CYCLE=[1,2,4,8,16,32],NUM_PADS=8,NUM_STEPS=16,NUM_PATS=8,NUM_BARS=16;
const GRADE_SPECS=[{name:"HI-FI",rate:31250,bits:12},{name:"STANDARD",rate:15625,bits:10},{name:"LO-FI 1",rate:7812,bits:8},{name:"LO-FI 2",rate:3906,bits:6}],BOTTOM_FX=["filter1","filter2","ringmod"];
let ac=null,masterGain,fxInput,lpfNode,hpfNode,lpfWet,hpfWet,thruGain,postFilterBus,ringGain,ringOsc,ringDepth,dryGain,delayLines=null,activeDelay=0,lastDelayTime=.18,delayXfadeUntil=0;
let extOn=false,extStream=null,extSrc=null,extGain=null,pitchOn=false,mainFx=null,ctrlTarget=null,htApi={};
const fxVals={pitch:.5,time:.5,delay:.5,filter1:.5,filter2:.5,ringmod:.5};
const getEchoParams=v=>({t:.08+Math.pow(v,1.35)*.34,fb:.18+v*.4,wet:.32+v*.28,lpf:4600-v*1600}),getTimeMult=()=>.65+fxVals.time*.7;
const mkPad=(b,p)=>({bank:b,pad:p,name:`EMPTY ${BANK_NAMES[b]}${p+1}`,buffer:null,cache:{},startNorm:0,endNorm:1,loopBeats:null,waveZoom:1,waveScroll:0,syncWarp:false,grade:0,stereo:false,gate:false,loop:false,reverse:false,vol:.85,pan:0,pitch:1,mute:false,solo:false,fxSend:false,activeVoice:null,gainNode:null,panNode:null,analyser:null,dryOut:null,fxOut:null});
const banks=Array.from({length:NUM_BANKS},(_,b)=>Array.from({length:NUM_PADS},(_,p)=>mkPad(b,p)));
const patterns=Array.from({length:NUM_PATS},()=>Array.from({length:NUM_BANKS},()=>Array.from({length:NUM_PADS},()=>new Array(NUM_STEPS).fill(0))));
const trackVel=Array.from({length:NUM_BANKS},()=>new Array(NUM_PADS).fill(.85));
const songBars=Array.from({length:NUM_BARS},()=>({pat:0,tracks:Array.from({length:NUM_BANKS},()=>new Array(NUM_PADS).fill(true))}));
let currentBank=0,selectedPad=0,currentPat=0,holdOn=false,remainMode=false,deleteMode=false,truncateMode=false,deleteTargetPad=null;
let resampleState=null,resampleTarget=null,resampleNode=null,resampleChunksL=[],resampleChunksR=[],resampleFrames=0,resampleIdx=1;
let bpm=90,baseBpm=90,displayedLedValue=90,swingPct=10,volVal=.85,lastTap=0,isPlaying=false,playMode="pat",currentStep=0,currentBar=0,uiStep=0,uiBar=0,nextStepTime=0,schedTimer=null;
let auditionSource=null,auditionEl=null,draggingSampleId=null,sampleIdCounter=1,syncGainWheel=()=>{};
const sampleRegistry=new Map(),folderTree={name:"ROOT",folders:{},files:[]},meterSegsUI=Array.from({length:NUM_PADS},()=>[]),faderAnimIds=new Array(NUM_PADS).fill(null);
const hud=$("hud"),stepLed=$("step-led"),drawer=$("explorer-drawer"),spExplorerBtn=$("btn-sp-explorer"),rackBpmInp=$("rack-bpm-inp"),waveBpmInp=$("wave-bpm-inp"),btnWaveBeats=$("btn-wave-beats");
const curPadObj=()=>banks[currentBank][selectedPad],hasSyncedPad=()=>banks.some(b=>b.some(p=>p.syncWarp&&p.buffer));
const rateToSemi=r=>12*Math.log2(Math.max(.25,r)),semiToRate=s=>Math.pow(2,s/12),fmtBpm=v=>Number.isFinite(v)?Number(v.toFixed(2)).toString():"";
const getMinNormGap=p=>(!p||!p.buffer||!p.buffer.duration)?.0001:Math.min(.05,.015/p.buffer.duration);
const getMaxZoomForPad=p=>(!p||!p.buffer||!p.buffer.duration)?64:Math.max(64,Math.min(2048,Math.ceil(p.buffer.duration/.04)));

(()=>{
  if(!$("sp202-seq-skin-css")){
    const st=document.createElement("style");st.id="sp202-seq-skin-css";
    st.textContent=`#seq-led-rack{display:grid;grid-template-columns:1.15fr 1.35fr .75fr;gap:10px;margin:0 0 10px;padding:8px 10px;background:linear-gradient(180deg,#1a1d22,#121418);border:1px solid #2b3038;border-top-color:#3a404a;border-radius:3px;box-shadow:inset 0 2px 6px rgba(0,0,0,.85),0 1px 0 rgba(255,255,255,.05)}.seq-led-bay{display:flex;flex-direction:column;align-items:center;justify-content:center;gap:4px;padding:4px 8px 6px;background:#0b0c0f;border:1px solid #262a31;border-top-color:#07080a;border-bottom-color:#353a44;border-radius:2px;box-shadow:inset 0 2px 8px rgba(0,0,0,.95);user-select:none}.seq-led-bay.interactive{cursor:ns-resize}.seq-led-bay.clickable{cursor:pointer}.seq-led-lbl{font:700 9px "Courier New",monospace;letter-spacing:1.4px;color:#e05a47;text-transform:uppercase;text-shadow:0 1px 1px #000}.seq-led-glass{position:relative;width:100%;height:34px;background:radial-gradient(ellipse at 50% 45%,#1b090c,#090405 78%,#050203);border:1px solid #1e1214;border-radius:2px;box-shadow:inset 0 1px 6px rgba(0,0,0,.95);overflow:hidden}.seq-led-glass::after{content:"";position:absolute;inset:0;background:linear-gradient(180deg,rgba(255,255,255,.06),transparent 48%);pointer-events:none}.seq-led-glass canvas{display:block;width:100%;height:100%}#seq-grid .seq-vel-sq{position:relative!important;width:22px!important;height:22px!important;min-width:22px!important;padding:0!important;border-radius:50%!important;background:radial-gradient(circle at 35% 30%,#383d46,#1a1d22 72%,#0d0f12)!important;border:1px solid #090b0d!important;box-shadow:0 2px 4px rgba(0,0,0,.85),inset 0 1px 1px rgba(255,255,255,.16),0 0 0 1px rgba(255,255,255,.05)!important;display:flex!important;align-items:center!important;justify-content:center!important;cursor:ns-resize!important;user-select:none!important}#seq-grid .seq-vel-cap{position:relative;width:16px;height:16px;border-radius:50%;background:radial-gradient(circle at 35% 30%,#2d323a,#14171b 85%);box-shadow:inset 0 1px 1px rgba(255,255,255,.18),0 1px 2px rgba(0,0,0,.9);pointer-events:none}#seq-grid .seq-vel-ptr{position:absolute;top:1.5px;left:50%;transform:translateX(-50%);width:2px;height:6px;border-radius:1px;background:#ff4e3a;box-shadow:0 0 4px rgba(255,70,50,.9)}#seq-grid .seq-row{border-bottom:1px solid rgba(255,255,255,.04);padding:3px 0}#seq-grid .step-num.beat{color:#e05a47!important;font-weight:700}#seq-grid .step-num.now{color:#ff3850!important;text-shadow:0 0 6px rgba(255,40,60,.9)}#seq-grid .step-cell{position:relative!important;background:linear-gradient(180deg,#d0d4da,#b8bec6 56%,#9ea5ae)!important;border:1px solid #12151a!important;border-radius:3px!important;box-shadow:inset 0 1px 0 rgba(255,255,255,.7),inset 0 -2px 2px rgba(0,0,0,.32),0 2px 3px rgba(0,0,0,.68)!important;transition:transform .04s ease,box-shadow .06s ease,filter .06s ease!important;overflow:hidden}#seq-grid .step-cell.beat-alt{background:linear-gradient(180deg,#b0b6be,#989fa9 56%,#808792)!important;box-shadow:inset 0 1px 0 rgba(255,255,255,.48),inset 0 -2px 2px rgba(0,0,0,.38),0 2px 3px rgba(0,0,0,.72)!important}#seq-grid .step-cell::before{content:"";position:absolute;top:4px;left:50%;transform:translateX(-50%);width:52%;height:4px;border-radius:1px;background:#4c515a;box-shadow:inset 0 1px 2px rgba(0,0,0,.88),0 1px 0 rgba(255,255,255,.35);pointer-events:none}#seq-grid .step-cell:active{transform:translateY(1px)}#seq-grid .step-cell.on{background:radial-gradient(circle at 50% 34%,#ffaa88,#ff6954 48%,#d93a32)!important;border-color:#2a0b09!important;box-shadow:inset 0 1px 1px rgba(255,230,215,.8),inset 0 -2px 3px rgba(135,18,14,.55),0 0 calc(3px + var(--v,.85)*10px) rgba(255,66,46,calc(.28 + var(--v,.85)*.55)),0 2px 3px rgba(0,0,0,.72)!important;filter:saturate(calc(.62 + var(--v,.85)*.52)) brightness(calc(.84 + var(--v,.85)*.24))}#seq-grid .step-cell.on::before{background:#ff261c;box-shadow:0 0 6px #ff3a2c,0 0 2px #fff2df}#seq-grid .step-cell.playhead::before{background:#ff4636!important;box-shadow:0 0 7px #ff3322,0 0 2px #ffe8cc!important}#seq-grid .step-cell.on.playhead::before{background:#fff3d6!important;box-shadow:0 0 8px #ffaa66,0 0 3px #fff!important}`;
    document.head.appendChild(st);
  }
  const sg=$("seq-grid");
  if(sg&&!$("seq-led-rack")){
    const r=document.createElement("div");r.id="seq-led-rack";
    r.innerHTML=`<div class="seq-led-bay"><div class="seq-led-lbl">BAR / BEAT</div><div class="seq-led-glass"><canvas id="seq-led-bar"></canvas></div></div><div class="seq-led-bay interactive" id="seq-bay-bpm" title="Drag Up/Down or Scroll to Adjust BPM"><div class="seq-led-lbl">BPM</div><div class="seq-led-glass"><canvas id="seq-led-bpm"></canvas></div></div><div class="seq-led-bay clickable" id="seq-bay-pat" title="Click to Cycle Pattern (P1–P8)"><div class="seq-led-lbl">PATTERN</div><div class="seq-led-glass"><canvas id="seq-led-pat"></canvas></div></div>`;
    sg.parentNode.insertBefore(r,sg);
  }
})();

const bpmCanvas=$("bpm-canvas"),seqBarCanvas=$("seq-led-bar"),seqBpmCanvas=$("seq-led-bpm"),seqPatCanvas=$("seq-led-pat");
const SEG_MAP={0:[1,1,1,1,1,1,0],1:[0,1,1,0,0,0,0],2:[1,1,0,1,1,0,1],3:[1,1,1,1,0,0,1],4:[0,1,1,0,0,1,1],5:[1,0,1,1,0,1,1],6:[1,0,1,1,1,1,1],7:[1,1,1,0,0,0,0],8:[1,1,1,1,1,1,1],9:[1,1,1,1,0,1,1],"-":[0,0,0,0,0,0,1]," ":[0,0,0,0,0,0,0],P:[1,1,0,0,1,1,1],A:[1,1,1,0,1,1,1],B:[0,0,1,1,1,1,1],C:[1,0,0,1,1,1,0],D:[0,1,1,1,1,0,1]};
function drawSeg(ctx,x,y,l,t,v){const h=t/2;ctx.beginPath();if(!v){ctx.moveTo(x+h,y);ctx.lineTo(x+l-h,y);ctx.lineTo(x+l,y+h);ctx.lineTo(x+l-h,y+t);ctx.lineTo(x+h,y+t);ctx.lineTo(x,y+h);}else{ctx.moveTo(x+h,y);ctx.lineTo(x+t,y+h);ctx.lineTo(x+t,y+l-h);ctx.lineTo(x+h,y+l);ctx.lineTo(x,y+l-h);ctx.lineTo(x,y+h);}ctx.closePath();ctx.fill();}
function drawSevenSegCanvas(cv,txt){
  if(!cv)return;const r=cv.getBoundingClientRect();if(!r.width||!r.height)return;
  const dpr=window.devicePixelRatio||1,w=r.width,h=r.height;
  if(cv.width!==Math.floor(w*dpr)||cv.height!==Math.floor(h*dpr)){cv.width=Math.floor(w*dpr);cv.height=Math.floor(h*dpr);}
  const ctx=cv.getContext("2d");ctx.setTransform(dpr,0,0,dpr,0,0);ctx.clearRect(0,0,w,h);
  const toks=[];for(let i=0;i<txt.length;i++){const ch=txt[i];if(ch==="."){if(toks.length&&!toks[toks.length-1].colon)toks[toks.length-1].dp=true;}else if(ch===":")toks.push({colon:true});else toks.push({ch,dp:false});}
  const padX=w*.06,padY=h*.13,digH=h-padY*2,totU=toks.reduce((a,t)=>a+(t.colon?.36:1),0)||1,unitW=Math.min((w-padX*2)/totU,digH*.56/.74);
  let curX=(w-unitW*totU)*.5;const thick=Math.max(2,digH*.13),gap=thick*.28;
  toks.forEach(tok=>{
    if(tok.colon){const cx=curX+unitW*.18,dr=Math.max(1.6,thick*.55);ctx.save();ctx.fillStyle="#ff2638";ctx.shadowColor="rgba(255,30,50,.95)";ctx.shadowBlur=Math.max(5,digH*.2);[.32,.68].forEach(fy=>{ctx.beginPath();ctx.arc(cx,padY+digH*fy,dr,0,Math.PI*2);ctx.fill();});ctx.restore();curX+=unitW*.36;return;}
    const digW=unitW*.72,ox=curX+(unitW-digW)*.5,segs=SEG_MAP[tok.ch]||SEG_MAP[" "];
    ctx.save();ctx.translate(ox+digW*.08,padY);ctx.transform(1,0,-.11,1,0,0);
    const hL=digW-thick*.9,vL=(digH-thick*1.1)/2,coords=[()=>drawSeg(ctx,thick*.45,0,hL,thick,0),()=>drawSeg(ctx,digW-thick,thick*.5+gap,vL-gap,thick,1),()=>drawSeg(ctx,digW-thick,digH/2+gap,vL-gap,thick,1),()=>drawSeg(ctx,thick*.45,digH-thick,hL,thick,0),()=>drawSeg(ctx,0,digH/2+gap,vL-gap,thick,1),()=>drawSeg(ctx,0,thick*.5+gap,vL-gap,thick,1),()=>drawSeg(ctx,thick*.45,(digH-thick)/2,hL,thick,0)];
    ctx.shadowBlur=0;ctx.fillStyle="rgba(65,14,18,.34)";coords.forEach(f=>f());
    ctx.fillStyle="#ff2638";ctx.shadowColor="rgba(255,30,50,.95)";ctx.shadowBlur=Math.max(6,digH*.22);
    segs.forEach((on,i)=>{if(on)coords[i]();});
    if(tok.dp){const dpR=Math.max(1.5,thick*.52);ctx.beginPath();ctx.arc(digW+thick*.65,digH-dpR,dpR,0,Math.PI*2);ctx.fill();}
    ctx.restore();curX+=unitW;
  });
}
const drawSevenSegDisplay=v=>{displayedLedValue=v;drawSevenSegCanvas(bpmCanvas,String(v==null?"---":Math.round(v)).padStart(3," ").slice(-3));};
function drawSeqDisplays(step=uiStep,bar=uiBar){uiStep=step;uiBar=bar;drawSevenSegCanvas(seqBarCanvas,`${String(bar+1).padStart(2,"0")}:${String(step+1).padStart(2,"0")}`);drawSevenSegCanvas(seqBpmCanvas,(bpm<100?" ":"")+bpm.toFixed(2));drawSevenSegCanvas(seqPatCanvas,`P${currentPat+1}`);}

if($("seq-bay-bpm")){
  $("seq-bay-bpm").onmousedown=e=>{e.preventDefault();const sy=e.clientY,sb=baseBpm,mv=ev=>updateBpm(sb+(sy-ev.clientY)*.35),up=()=>{window.removeEventListener("mousemove",mv);window.removeEventListener("mouseup",up);};window.addEventListener("mousemove",mv);window.addEventListener("mouseup",up);};
  $("seq-bay-bpm").addEventListener("wheel",e=>{e.preventDefault();updateBpm(baseBpm+(e.deltaY<0?1:-1));},{passive:false});
}
if($("seq-bay-pat"))$("seq-bay-pat").onclick=()=>{const b=$("pat-selector").querySelectorAll(".mini-btn");if(b[(currentPat+1)%NUM_PATS])b[(currentPat+1)%NUM_PATS].click();};

function getEffectivePadRate(pad){let r=pad.pitch;if(pitchOn&&pad.fxSend)r*=.5+fxVals.pitch*1.5;if(mainFx==="time"&&(pad.fxSend||pad.syncWarp))r*=getTimeMult();return Math.max(.25,r);}
function syncSequencerTimeWarp(){const m=(mainFx==="time"&&hasSyncedPad())?getTimeMult():1;bpm=Math.max(40,Math.min(240,Math.round(baseBpm*m*100)/100));if(document.activeElement!==rackBpmInp)rackBpmInp.value=fmtBpm(bpm);drawSevenSegDisplay(Math.round(bpm));drawSeqDisplays();}
function resolveLoopBeats(pad,rawDur){if(pad.loopBeats!==null)return pad.loopBeats;const ch=[4,8,2,16,1,32];for(const b of ch){const c=b*60/rawDur;if(c>=70&&c<=155)return b;}let best=4,minD=1e9;for(const b of ch){const d=Math.abs(b*60/rawDur-105);if(d<minD){minD=d;best=b;}}return best;}
function detectLoopBpm(pad){if(!pad||!pad.buffer)return null;const rawDur=(pad.endNorm-pad.startNorm)*pad.buffer.duration;if(rawDur<.05)return null;const beats=resolveLoopBeats(pad,rawDur),base=beats*60/rawDur,effRate=getEffectivePadRate(pad);return{bpm:base*effRate,padBpm:base*pad.pitch,baseBpm:base,beats,dur:rawDur/effRate};}
function showPadBpmOnDisplay(pad){const info=detectLoopBpm(pad);if(info){drawSevenSegDisplay(Math.round(info.bpm));if(document.activeElement!==waveBpmInp)waveBpmInp.value=fmtBpm(info.padBpm);waveBpmInp.disabled=false;btnWaveBeats.textContent=`${info.beats}B`;}else{drawSevenSegDisplay(bpm);waveBpmInp.value="";waveBpmInp.disabled=true;btnWaveBeats.textContent="--";}}
function setPadPitchRate(bIdx,pIdx,nr){const pad=banks[bIdx][pIdx];pad.pitch=Math.max(.5,Math.min(2,nr));if(ac&&pad.activeVoice){const eff=getEffectivePadRate(pad);pad.activeVoice.rate=eff;pad.activeVoice.src.playbackRate.setTargetAtTime(eff,ac.currentTime,.012);}if(bIdx===currentBank){const mt=$(`mix-tune-${pIdx}`);if(mt)mt.value=pad.pitch;if(pIdx===selectedPad){syncWaveEditorUI();showPadBpmOnDisplay(pad);}}}
function setPadTargetBpm(bIdx,pIdx,tBpm){const pad=banks[bIdx][pIdx],info=detectLoopBpm(pad);if(!info||!Number.isFinite(tBpm)||tBpm<=0)return;if(pad.loopBeats===null)pad.loopBeats=info.beats;const des=tBpm/info.baseBpm,cl=Math.max(.5,Math.min(2,des));setPadPitchRate(bIdx,pIdx,cl);const up=detectLoopBpm(pad);if(up){const s=rateToSemi(pad.pitch);hud.innerHTML=`BANK ${BANK_NAMES[bIdx]} PAD ${pIdx+1} BPM: <b>${up.padBpm.toFixed(2)} BPM</b> (${s>=0?"+":""}${s.toFixed(2)} st)${des!==cl?" (OCTAVE LIMIT)":""}`;}}
const stepPadBpm=d=>{const i=detectLoopBpm(curPadObj());if(i)setPadTargetBpm(currentBank,selectedPad,i.padBpm+d);};

function truncatePadSample(bIdx,pIdx){
  initAudio();const pad=banks[bIdx][pIdx];if(!pad||!pad.buffer){hud.innerHTML=`<b>TRUNCATE:</b> BANK ${BANK_NAMES[bIdx]} PAD ${pIdx+1} IS EMPTY`;return false;}
  const sb=pad.buffer,tl=sb.length,sF=Math.max(0,Math.min(tl-1,Math.floor(pad.startNorm*tl))),eF=Math.max(sF+1,Math.min(tl,Math.ceil(pad.endNorm*tl)));
  if(sF===0&&eF===tl){hud.innerHTML="<b>TRUNCATE:</b> MARK POINTS ALREADY AT FULL LENGTH";return false;}
  stopPadVoice(bIdx,pIdx);const nb=ac.createBuffer(sb.numberOfChannels,eF-sF,sb.sampleRate);
  for(let c=0;c<sb.numberOfChannels;c++)nb.getChannelData(c).set(sb.getChannelData(c).subarray(sF,eF));
  pad.buffer=nb;pad.cache={};pad.startNorm=0;pad.endNorm=1;resetPadZoom(pad);syncPadVisuals();syncWaveEditorUI();showPadBpmOnDisplay(pad);renderAllWaveCanvases();
  hud.innerHTML=`<b>TRUNCATED</b> BANK ${BANK_NAMES[bIdx]} PAD ${pIdx+1} (${pad.name}) → <b>${nb.duration.toFixed(3)} s</b>`;return true;
}

function renderDecimatedBuffer(ctx,sb,grade,rev){
  if(!sb)return null;const sr=sb.sampleRate,len=sb.length,nCh=sb.numberOfChannels,sp=GRADE_SPECS[grade],stepR=Math.max(1,sr/sp.rate),qL=Math.pow(2,sp.bits-1),out=ctx.createBuffer(nCh,len,sr);
  for(let c=0;c<nCh;c++){const src=sb.getChannelData(c),dst=out.getChannelData(c);let ph=stepR,hd=0;for(let i=0;i<len;i++){const si=rev?(len-1-i):i;ph+=1;if(ph>=stepR){ph-=stepR;let s=src[si];if(grade>=2)s=Math.tanh(s*(grade===3?1.55:1.25));hd=Math.round(s*qL)/qL;}dst[i]=hd;}}
  return out;
}
const getProcessedBuffer=p=>p.buffer?(p.cache[`${p.grade}_${p.reverse?1:0}`]||(p.cache[`${p.grade}_${p.reverse?1:0}`]=renderDecimatedBuffer(ac,p.buffer,p.grade,p.reverse))):null;
const getDisplayBuffer=p=>(!p||!p.buffer)?null:(p.grade===0||!ac)?p.buffer:(p.cache[`${p.grade}_0`]||(p.cache[`${p.grade}_0`]=renderDecimatedBuffer(ac,p.buffer,p.grade,false)));
function encodeWav16(ab){
  const nCh=ab.numberOfChannels,sr=ab.sampleRate,len=ab.length,ba=nCh*2,ds=len*ba,buf=new ArrayBuffer(44+ds),v=new DataView(buf),ws=(o,s)=>{for(let i=0;i<s.length;i++)v.setUint8(o+i,s.charCodeAt(i));};
  ws(0,"RIFF");v.setUint32(4,36+ds,true);ws(8,"WAVE");ws(12,"fmt ");v.setUint32(16,16,true);v.setUint16(20,1,true);v.setUint16(22,nCh,true);v.setUint32(24,sr,true);v.setUint32(28,sr*ba,true);v.setUint16(32,ba,true);v.setUint16(34,16,true);ws(36,"data");v.setUint32(40,ds,true);
  const chs=Array.from({length:nCh},(_,c)=>ab.getChannelData(c));let o=44;
  for(let i=0;i<len;i++)for(let c=0;c<nCh;c++){const s=Math.max(-1,Math.min(1,chs[c][i]));v.setInt16(o,s<0?s*0x8000:s*0x7FFF,true);o+=2;}
  return new Blob([buf],{type:"audio/wav"});
}
const triggerDownload=(b,fn)=>{const u=URL.createObjectURL(b),a=document.createElement("a");a.href=u;a.download=fn;document.body.appendChild(a);a.click();a.remove();setTimeout(()=>URL.revokeObjectURL(u),4e3);};
async function exportPadWav(withFx=true){
  initAudio();const pad=curPadObj();if(!pad||!pad.buffer){hud.innerHTML="<b>EXPORT:</b> SELECTED PAD IS EMPTY";return;}
  const sb=pad.buffer,sr=sb.sampleRate,nCh=sb.numberOfChannels,safe=(pad.name.replace(/[^\x20-\x7E]/g,"").trim()||`PAD_${BANK_NAMES[currentBank]}${selectedPad+1}`).replace(/[^A-Z0-9_-]/gi,"_");
  if(!withFx){const sF=Math.max(0,Math.min(sb.length-1,Math.floor(pad.startNorm*sb.length))),eF=Math.max(sF+1,Math.min(sb.length,Math.ceil(pad.endNorm*sb.length))),raw=ac.createBuffer(nCh,eF-sF,sr);for(let c=0;c<nCh;c++)raw.getChannelData(c).set(sb.getChannelData(c).subarray(sF,eF));const fn=`${safe}_RAW.wav`;triggerDownload(encodeWav16(raw),fn);hud.innerHTML=`EXPORTED RAW WAV: <b>${fn}</b> (${raw.duration.toFixed(3)}s)`;return;}
  const rate=getEffectivePadRate(pad),td=sb.duration,fS=pad.startNorm*td;let fE=pad.endNorm*td;if(fE-fS<.01)fE=Math.min(td,fS+.01);
  const sSec=pad.reverse?Math.max(0,td-fE):fS,eSec=pad.reverse?Math.min(td,td-fS):fE,segD=Math.max(.01,eSec-sSec),pDur=segD/rate,useM=pad.fxSend&&mainFx!==null,ep=getEchoParams(fxVals.delay),tail=(useM&&mainFx==="delay")?Math.min(2.6,ep.t*(2.5+ep.fb*5)):.02;
  const off=new OfflineAudioContext(2,Math.max(1,Math.ceil((pDur+tail)*sr)),sr),proc=renderDecimatedBuffer(off,sb,pad.grade,pad.reverse),src=off.createBufferSource();src.buffer=proc;src.playbackRate.value=rate;
  const mg=off.createGain();mg.gain.value=1;mg.channelCount=pad.stereo?2:1;mg.channelCountMode=pad.stereo?"max":"explicit";const cg=off.createGain();cg.gain.value=pad.vol;const pan=off.createStereoPanner();pan.pan.value=pad.pan;
  src.connect(mg);mg.connect(cg);cg.connect(pan);
  if(!useM)pan.connect(off.destination);else{
    const isL=mainFx==="filter1",isH=mainFx==="filter2",isR=mainFx==="ringmod",isD=mainFx==="delay",pb=off.createGain();
    if(isL||isH){const f=off.createBiquadFilter();f.type=isL?"lowpass":"highpass";f.Q.value=isL?4.2:3.5;f.frequency.value=Math.min(sr*.42,isL?95*Math.pow(145,fxVals.filter1):65*Math.pow(110,fxVals.filter2));pan.connect(f);f.connect(pb);}else pan.connect(pb);
    const rg=off.createGain();rg.gain.value=isR?.5:1;if(isR){const ro=off.createOscillator(),rd=off.createGain();ro.frequency.value=40+fxVals.ringmod*900;rd.gain.value=.5;ro.connect(rd);rd.connect(rg.gain);ro.start(0);}
    pb.connect(rg);rg.connect(off.destination);
    if(isD){const dn=off.createDelay(1.2),dl=off.createBiquadFilter(),df=off.createGain(),dw=off.createGain();dn.delayTime.value=ep.t;dl.type="lowpass";dl.frequency.value=ep.lpf;df.gain.value=ep.fb;dw.gain.value=ep.wet;rg.connect(dn);dn.connect(dl);dl.connect(df);df.connect(dn);dl.connect(dw);dw.connect(off.destination);}
  }
  src.start(0,sSec,segD);const ren=await off.startRendering(),info=detectLoopBpm(pad),sp=GRADE_SPECS[pad.grade],fn=`${safe}_${sp.name.replace(/\s+/g,"")}${info?`_${Math.round(info.bpm)}BPM`:""}${(pitchOn&&pad.fxSend?"_PITCH":"")+(useM?`_${mainFx.toUpperCase()}`:"")}.wav`;
  triggerDownload(encodeWav16(ren),fn);hud.innerHTML=`EXPORTED WAV: <b>${fn}</b> (${sp.name} · ${ren.duration.toFixed(3)}s)`;
}

function initAudio(){
  if(ac)return;ac=new(window.AudioContext||window.webkitAudioContext)({latencyHint:"interactive"});
  masterGain=ac.createGain();masterGain.gain.value=volVal;masterGain.connect(ac.destination);
  resampleNode=ac.createScriptProcessor(1024,2,2);const sink=ac.createGain();sink.gain.value=0;extGain=ac.createGain();extGain.gain.value=1;
  masterGain.connect(resampleNode);extGain.connect(resampleNode);resampleNode.connect(sink);sink.connect(ac.destination);
  resampleNode.onaudioprocess=e=>{
    if(resampleState!=="armed"&&resampleState!=="recording")return;
    const inL=e.inputBuffer.getChannelData(0),inR=e.inputBuffer.getChannelData(1);
    if(resampleState==="armed"){
      let ti=-1;for(let i=0;i<inL.length;i++)if(Math.abs(inL[i])>.0025||Math.abs(inR[i])>.0025){ti=i;break;}
      if(ti===-1)return;resampleState="recording";resampleChunksL=[];resampleChunksR=[];resampleFrames=0;syncPadVisuals();
      hud.innerHTML=`<b style="color:#ff3850">● ${extOn?"SAMPLING EXT":"RESAMPLING"}</b> TO BANK ${BANK_NAMES[resampleTarget.bank]} PAD ${resampleTarget.pad+1} — PRESS <b>REC</b> TO FINISH`;
      const sL=new Float32Array(inL.subarray(ti)),sR=new Float32Array(inR.subarray(ti));resampleChunksL.push(sL);resampleChunksR.push(sR);resampleFrames+=sL.length;return;
    }
    const cL=new Float32Array(inL),cR=new Float32Array(inR);resampleChunksL.push(cL);resampleChunksR.push(cR);resampleFrames+=cL.length;
    if(resampleFrames>=ac.sampleRate*30)finishResampleCapture();
  };
  fxInput=ac.createGain();lpfNode=ac.createBiquadFilter();lpfNode.type="lowpass";lpfNode.frequency.value=1800;lpfNode.Q.value=4.2;
  hpfNode=ac.createBiquadFilter();hpfNode.type="highpass";hpfNode.frequency.value=600;hpfNode.Q.value=3.5;
  lpfWet=ac.createGain();lpfWet.gain.value=0;hpfWet=ac.createGain();hpfWet.gain.value=0;thruGain=ac.createGain();thruGain.gain.value=1;postFilterBus=ac.createGain();
  fxInput.connect(thruGain);thruGain.connect(postFilterBus);fxInput.connect(lpfNode);lpfNode.connect(lpfWet);lpfWet.connect(postFilterBus);fxInput.connect(hpfNode);hpfNode.connect(hpfWet);hpfWet.connect(postFilterBus);
  ringGain=ac.createGain();ringGain.gain.value=1;ringOsc=ac.createOscillator();ringOsc.frequency.value=180;ringDepth=ac.createGain();ringDepth.gain.value=0;ringOsc.connect(ringDepth);ringDepth.connect(ringGain.gain);ringOsc.start();
  dryGain=ac.createGain();dryGain.gain.value=1;postFilterBus.connect(ringGain);ringGain.connect(dryGain);dryGain.connect(masterGain);
  const ep=getEchoParams(fxVals.delay);lastDelayTime=ep.t;
  delayLines=[0,1].map(()=>{const del=ac.createDelay(1.2),lpf=ac.createBiquadFilter(),fb=ac.createGain(),wet=ac.createGain(),inG=ac.createGain();del.delayTime.value=ep.t;lpf.type="lowpass";lpf.frequency.value=ep.lpf;fb.gain.value=0;wet.gain.value=0;inG.gain.value=0;ringGain.connect(inG);inG.connect(del);del.connect(lpf);lpf.connect(fb);fb.connect(del);lpf.connect(wet);wet.connect(masterGain);return{del,lpf,fb,wet,inG};});
  for(let b=0;b<NUM_BANKS;b++)for(let p=0;p<NUM_PADS;p++){const ch=banks[b][p];ch.gainNode=ac.createGain();ch.panNode=ac.createStereoPanner();ch.analyser=ac.createAnalyser();ch.analyser.fftSize=256;ch.fxOut=ac.createGain();ch.dryOut=ac.createGain();ch.gainNode.connect(ch.panNode);ch.panNode.connect(ch.analyser);ch.panNode.connect(ch.fxOut);ch.panNode.connect(ch.dryOut);ch.fxOut.connect(fxInput);ch.dryOut.connect(masterGain);}
  updateAllMixerNodes();applyFxRealtime();
}
async function toggleExtSource(force){
  initAudio();if(ac.state==="suspended")ac.resume();const next=force!==undefined?force:!extOn;
  if(!next){extOn=false;if(extSrc){try{extSrc.disconnect();}catch{}extSrc=null;}if(extStream){extStream.getTracks().forEach(t=>t.stop());extStream=null;}syncPadVisuals();hud.innerHTML="<b>EXT SOURCE OFF</b>";return;}
  if(!navigator.mediaDevices||!navigator.mediaDevices.getUserMedia){hud.innerHTML="<b>EXT SOURCE:</b> REQUIRES HTTPS OR LOCALHOST";return;}
  try{extStream=await navigator.mediaDevices.getUserMedia({audio:{echoCancellation:false,noiseSuppression:false,autoGainControl:false,latency:0}});extSrc=ac.createMediaStreamSource(extStream);extSrc.connect(extGain);extOn=true;syncPadVisuals();hud.innerHTML="<b>EXT SOURCE LIVE</b> (RAW · ZERO FEEDBACK) — PRESS <b>REC</b> TO SAMPLE";}
  catch(err){extOn=false;syncPadVisuals();hud.innerHTML=`<b>EXT SOURCE ERROR:</b> ${err.name||"DENIED"}`;}
}
function finishResampleCapture(){
  const tgt=resampleTarget,frames=resampleFrames,chL=resampleChunksL,chR=resampleChunksR;
  resampleState=null;resampleTarget=null;resampleChunksL=[];resampleChunksR=[];resampleFrames=0;syncPadVisuals();
  if(!tgt||frames<64){hud.innerHTML="<b>RESAMPLE CANCELLED:</b> NO AUDIO CAPTURED";return;}
  const fL=new Float32Array(frames),fR=new Float32Array(frames);let off=0;for(let i=0;i<chL.length;i++){fL.set(chL[i],off);fR.set(chR[i],off);off+=chL[i].length;}
  let eIdx=frames-1;while(eIdx>64&&Math.abs(fL[eIdx])<.0008&&Math.abs(fR[eIdx])<.0008)eIdx--;
  const fLen=Math.min(frames,eIdx+64),nb=ac.createBuffer(2,fLen,ac.sampleRate);nb.getChannelData(0).set(fL.subarray(0,fLen));nb.getChannelData(1).set(fR.subarray(0,fLen));
  const rName=`${extOn?"EXT":"RESAMP"}_${String(resampleIdx++).padStart(2,"0")}`;
  if(!folderTree.folders.RESAMPLED)folderTree.folders.RESAMPLED={name:"RESAMPLED",folders:{},files:[]};
  const sid="smp_"+(sampleIdCounter++),en={id:sid,name:`${rName}.wav`,buffer:nb};sampleRegistry.set(sid,en);folderTree.folders.RESAMPLED.files.push(en);renderSampleTree();
  assignBufferToPad(tgt.bank,tgt.pad,nb,rName);hud.innerHTML=`<b>CAPTURED</b> → BANK ${BANK_NAMES[tgt.bank]} PAD ${tgt.pad+1} [<b>${rName}</b> · ${nb.duration.toFixed(3)}s]`;
}
function updateAllMixerNodes(){
  if(!ac)return;const now=ac.currentTime;
  for(let b=0;b<NUM_BANKS;b++){const anySolo=banks[b].some(c=>c.solo);for(let p=0;p<NUM_PADS;p++){const ch=banks[b][p];if(!ch.gainNode)continue;ch.gainNode.gain.setTargetAtTime((anySolo?ch.solo:!ch.mute)?ch.vol:0,now,.012);ch.panNode.pan.setTargetAtTime(ch.pan,now,.012);ch.fxOut.gain.setTargetAtTime(ch.fxSend?1:0,now,.012);ch.dryOut.gain.setTargetAtTime(ch.fxSend?0:1,now,.012);}}
}
function applyFxRealtime(){
  syncSequencerTimeWarp();if(!ac)return;
  const now=ac.currentTime,tau=.02,isL=mainFx==="filter1",isH=mainFx==="filter2",isR=mainFx==="ringmod",isD=mainFx==="delay";
  thruGain.gain.setTargetAtTime((!isL&&!isH)?1:0,now,tau);lpfWet.gain.setTargetAtTime(isL?1:0,now,tau);hpfWet.gain.setTargetAtTime(isH?1:0,now,tau);
  if(isL)lpfNode.frequency.setTargetAtTime(Math.min(ac.sampleRate*.42,95*Math.pow(145,fxVals.filter1)),now,.025);
  if(isH)hpfNode.frequency.setTargetAtTime(Math.min(ac.sampleRate*.42,65*Math.pow(110,fxVals.filter2)),now,.025);
  ringGain.gain.setTargetAtTime(isR?.5:1,now,tau);ringDepth.gain.setTargetAtTime(isR?.5:0,now,tau);if(isR)ringOsc.frequency.setTargetAtTime(40+fxVals.ringmod*900,now,.02);
  if(delayLines){
    if(!isD)delayLines.forEach(d=>{d.inG.gain.setTargetAtTime(0,now,.02);d.wet.gain.setTargetAtTime(0,now,.03);d.fb.gain.setTargetAtTime(0,now,.03);});
    else{
      const ep=getEchoParams(fxVals.delay),cur=delayLines[activeDelay],nxtIdx=1-activeDelay,nxt=delayLines[nxtIdx];
      if(Math.abs(ep.t-lastDelayTime)>.005&&now>=delayXfadeUntil){lastDelayTime=ep.t;delayXfadeUntil=now+.045;nxt.del.delayTime.setValueAtTime(ep.t,now);nxt.lpf.frequency.setValueAtTime(ep.lpf,now);nxt.inG.gain.setTargetAtTime(1,now,.012);nxt.fb.gain.setTargetAtTime(ep.fb,now,.015);nxt.wet.gain.setTargetAtTime(ep.wet,now,.015);cur.inG.gain.setTargetAtTime(0,now,.012);cur.fb.gain.setTargetAtTime(0,now,.018);cur.wet.gain.setTargetAtTime(0,now,.018);activeDelay=nxtIdx;}
      else{cur.inG.gain.setTargetAtTime(1,now,.015);cur.lpf.frequency.setTargetAtTime(ep.lpf,now,.02);cur.fb.gain.setTargetAtTime(ep.fb,now,.02);cur.wet.gain.setTargetAtTime(ep.wet,now,.02);nxt.inG.gain.setTargetAtTime(0,now,.015);nxt.wet.gain.setTargetAtTime(0,now,.02);nxt.fb.gain.setTargetAtTime(0,now,.02);}
    }
  }
  for(let b=0;b<NUM_BANKS;b++)for(let p=0;p<NUM_PADS;p++){const ch=banks[b][p];if(ch.activeVoice){const r=getEffectivePadRate(ch);if(Math.abs(ch.activeVoice.rate-r)>.0001){ch.activeVoice.rate=r;ch.activeVoice.src.playbackRate.setTargetAtTime(r,now,.015);}}}
  if(curPadObj().fxSend||curPadObj().syncWarp)showPadBpmOnDisplay(curPadObj());
}

function updateDynamicDisplay(){
  for(let b=0;b<NUM_BANKS;b++)$(`led-bank-${b}`).classList.toggle("lit",b===currentBank);
  const pad=curPadObj();for(let g=0;g<4;g++)$(`led-grade-${g}`).classList.toggle("lit",pad.grade===g);
  $("led-mono-0").classList.toggle("lit",!pad.stereo);$("led-mono-1").classList.toggle("lit",pad.stereo);
  $("led-trig-0").classList.toggle("lit",!pad.gate);$("led-trig-1").classList.toggle("lit",pad.gate);
  $("led-loop-1").classList.toggle("lit",pad.loop);$("led-loop-0").classList.toggle("lit",!pad.loop);
  $("led-rev-0").classList.toggle("lit",!pad.reverse);$("led-rev-1").classList.toggle("lit",pad.reverse);
  const sp=GRADE_SPECS[pad.grade],sum=$("wave-mode-summary");
  if(sum)sum.textContent=`GRADE: ${sp.name} (${(sp.rate/1e3).toFixed(2)}kHz / ${sp.bits}-BIT) | ${pad.stereo?"STEREO":"MONO"} | ${pad.gate?"GATE":"TRIGGER"} | ${pad.loop?"LOOP":"ONE SHOT"} | ${pad.reverse?"REVERSE":"NORMAL"}`;
}
const hotSwapVoice=(b,p)=>{const pad=banks[b][p];if(!pad||!pad.activeVoice||!ac)return;const ph=getPlayheadNorm(pad);if(ph!==null)triggerPad(b,p,0,false,ph,pad.activeVoice.vel||1);};
$("blk-0").onclick=()=>{initAudio();const p=curPadObj();p.grade=(p.grade+1)%4;updateDynamicDisplay();hotSwapVoice(currentBank,selectedPad);renderAllWaveCanvases();const s=GRADE_SPECS[p.grade];hud.innerHTML=`GRADE: <b>${s.name} (${(s.rate/1e3).toFixed(2)}kHz · ${s.bits}-BIT)</b>`;};
$("blk-1").onclick=()=>{const p=curPadObj();p.stereo=!p.stereo;updateDynamicDisplay();if(p.activeVoice&&p.activeVoice.monoGain){p.activeVoice.monoGain.channelCount=p.stereo?2:1;p.activeVoice.monoGain.channelCountMode=p.stereo?"max":"explicit";}};
$("blk-2").onclick=()=>{curPadObj().gate=!curPadObj().gate;updateDynamicDisplay();};
$("blk-3").onclick=()=>{curPadObj().loop=!curPadObj().loop;updateDynamicDisplay();hotSwapVoice(currentBank,selectedPad);};
$("blk-4").onclick=()=>{curPadObj().reverse=!curPadObj().reverse;updateDynamicDisplay();hotSwapVoice(currentBank,selectedPad);renderAllWaveCanvases();};

function syncPadVisuals(){
  const aw=$("view-wave").classList.contains("active"),rs=resampleState==="select",ra=resampleState==="armed"||resampleState==="recording",ms=performance.now(),fp=`-${(ms%720).toFixed(1)}ms`,dp=`-${(ms%550).toFixed(1)}ms`;
  for(let p=0;p<NUM_PADS;p++){
    const pad=banks[currentBank][p],el=$(`pad-${p}`),hb=!!pad.buffer,pl=!!pad.activeVoice,tg=resampleTarget&&resampleTarget.bank===currentBank&&resampleTarget.pad===p;
    const fb=remainMode&&pad.fxSend,db=deleteMode&&hb&&deleteTargetPad!==p,ds=deleteMode&&hb&&deleteTargetPad===p,rb=rs&&!tg;
    if(fb&&!el.classList.contains("fx-blink-blue"))el.style.animationDelay=fp;else if((db&&!el.classList.contains("del-blink"))||(rb&&!el.classList.contains("rec-blink")))el.style.animationDelay=dp;else if(!fb&&!db&&!rb)el.style.animationDelay="";
    el.classList.toggle("has-sample",hb);el.classList.toggle("selected-pad",p===selectedPad);el.classList.toggle("lit",!remainMode&&!deleteMode&&!rs&&pl);
    el.classList.toggle("fx-blink-blue",fb);el.classList.toggle("del-blink",db);el.classList.toggle("del-selected",ds);el.classList.toggle("rec-blink",rb);el.classList.toggle("rec-selected",rs&&tg);el.classList.toggle("rec-armed",ra&&tg);
    const sn=$(`seq-pnum-${p}`);if(sn)sn.classList.toggle("lit",pl);
  }
  $("btn-remain").classList.toggle("lit-blue",remainMode);$("btn-del").classList.toggle("lit",deleteMode);$("btn-rec").classList.toggle("lit",rs);$("btn-rec").classList.toggle("rec-pulse",ra);
  $("btn-mark").classList.toggle("lit",truncateMode||aw);$("btn-source").classList.toggle("lit",extOn);$("btn-ab").classList.toggle("lit",currentBank===1);$("btn-cd").classList.toggle("lit",currentBank===3);
}
function stopPadVoice(b,p,when=0){const pad=banks[b][p];if(pad.activeVoice){try{pad.activeVoice.src.stop(when||0);}catch{}pad.activeVoice=null;if(b===currentBank){syncPadVisuals();if(p===selectedPad)renderAllWaveCanvases();}}}
function triggerPad(bIdx,pIdx,when=0,fromSeq=false,resumeNorm=null,vel=1){
  initAudio();if(ac.state==="suspended")ac.resume();
  const pad=banks[bIdx][pIdx],now=ac.currentTime,st=when>now?when:now,vd=Math.max(0,(st-now)*1e3);
  if(pad.activeVoice){const ov=pad.activeVoice;pad.activeVoice=null;if(resumeNorm!==null&&ov.monoGain){ov.monoGain.gain.setTargetAtTime(0,st,.004);try{ov.src.stop(st+.015);}catch{}}else try{ov.src.stop(st);}catch{}}
  const buf=getProcessedBuffer(pad);
  if(!buf){if(bIdx===currentBank&&!remainMode&&!deleteMode&&resampleState!=="select"){const el=$(`pad-${pIdx}`);el.classList.add("lit");setTimeout(()=>{if(!pad.activeVoice)syncPadVisuals();},140);}return;}
  const src=ac.createBufferSource();src.buffer=buf;const td=buf.duration,fS=pad.startNorm*td;let fE=pad.endNorm*td;if(fE-fS<.01)fE=Math.min(td,fS+.01);
  const sSec=pad.reverse?Math.max(0,td-fE):fS,eSec=pad.reverse?Math.min(td,td-fS):fE,segD=Math.max(.01,eSec-sSec),rate=getEffectivePadRate(pad);
  src.playbackRate.setValueAtTime(rate,st);const doL=pad.loop||holdOn;src.loop=doL;if(doL){src.loopStart=sSec;src.loopEnd=eSec;}
  const mg=ac.createGain();mg.channelCount=pad.stereo?2:1;mg.channelCountMode=pad.stereo?"max":"explicit";const vg=Math.max(.05,Math.min(1,vel));
  if(resumeNorm!==null){mg.gain.setValueAtTime(0,st);mg.gain.setTargetAtTime(vg,st,.004);}else mg.gain.setValueAtTime(vg,st);
  src.connect(mg);mg.connect(pad.gainNode);
  let off=sSec,pDur=segD;if(resumeNorm!==null){const cl=Math.max(pad.startNorm,Math.min(pad.endNorm,resumeNorm));off=pad.reverse?Math.max(sSec,Math.min(eSec-.005,td-cl*td)):Math.max(sSec,Math.min(eSec-.005,cl*td));pDur=Math.max(.01,eSec-off);}
  const vo={src,monoGain:mg,vel:vg,startTime:st-((off-sSec)/rate),fwdStartSec:fS,fwdEndSec:fE,segDur:segD,totalDur:td,rate,doLoop:doL,reverse:pad.reverse};
  pad.activeVoice=vo;if(doL)src.start(st,off);else if(fromSeq&&pad.gate)src.start(st,off,Math.min(pDur/rate,getStepDuration(currentStep))*rate);else src.start(st,off,pDur);
  if(bIdx===currentBank){if(vd<4)syncPadVisuals();else setTimeout(()=>{if(pad.activeVoice===vo)syncPadVisuals();},vd);}
  src.onended=()=>{if(pad.activeVoice===vo){pad.activeVoice=null;if(bIdx===currentBank){syncPadVisuals();if(pIdx===selectedPad)renderAllWaveCanvases();}}};
}
function getPlayheadNorm(pad){const v=pad&&pad.activeVoice;if(!v||!ac)return null;const el=(ac.currentTime-v.startTime)*v.rate;if(el<0||(!v.doLoop&&el>v.segDur))return null;const pos=v.doLoop?(el%v.segDur):el;return Math.max(0,Math.min(1,(v.reverse?(v.fwdEndSec-pos):(v.fwdStartSec+pos))/v.totalDur));}

const stopAudition=()=>{if(auditionSource){try{auditionSource.stop();}catch{}auditionSource=null;}if(auditionEl){auditionEl.classList.remove("auditioning");auditionEl=null;}};
function panicKillAll(){
  stopTransport();stopAudition();if(extOn)toggleExtSource(false);
  if(deleteMode||truncateMode){deleteMode=false;truncateMode=false;deleteTargetPad=null;}
  if(resampleState){resampleState=null;resampleTarget=null;resampleChunksL=[];resampleChunksR=[];resampleFrames=0;}
  for(let b=0;b<NUM_BANKS;b++)for(let p=0;p<NUM_PADS;p++)if(banks[b][p].activeVoice){try{banks[b][p].activeVoice.src.stop();}catch{}banks[b][p].activeVoice=null;}
  if(ac&&delayLines){const n=ac.currentTime;delayLines.forEach(d=>{d.inG.gain.cancelScheduledValues(n);d.fb.gain.cancelScheduledValues(n);d.wet.gain.cancelScheduledValues(n);d.inG.gain.setValueAtTime(0,n);d.fb.gain.setValueAtTime(0,n);d.wet.gain.setValueAtTime(0,n);});if(mainFx==="delay")setTimeout(()=>{if(mainFx==="delay")applyFxRealtime();},130);}
  syncPadVisuals();drawSevenSegDisplay(bpm);drawSeqDisplays(0,0);renderAllWaveCanvases();
  const c=$("btn-cancel");c.classList.add("lit");setTimeout(()=>c.classList.remove("lit"),180);hud.innerHTML="<b>CANCEL // PANIC KILL</b> — ALL AUDIO STOPPED";
}
function switchBank(nb){
  currentBank=nb;deleteMode=false;truncateMode=false;deleteTargetPad=null;
  document.querySelectorAll("#bank-selector [data-bank]").forEach(b=>b.classList.toggle("active",+b.dataset.bank===currentBank));
  ["seq-bank-lbl","mix-bank-lbl","arr-bank-lbl","drawer-bank-lbl"].forEach(id=>{if($(id))$(id).textContent=BANK_NAMES[currentBank];});
  updateDynamicDisplay();refreshAllBankUI(true);syncPadVisuals();syncWaveEditorUI();renderAllWaveCanvases();
}
$("btn-ab").onclick=()=>switchBank(currentBank===0?1:0);$("btn-cd").onclick=()=>switchBank(currentBank===2?3:2);
document.querySelectorAll("#bank-selector [data-bank]").forEach(b=>b.onclick=()=>switchBank(+b.dataset.bank));
$("btn-source").onclick=()=>toggleExtSource();
$("btn-rec").onclick=()=>{
  initAudio();if(ac.state==="suspended")ac.resume();if(remainMode)remainMode=false;if(deleteMode||truncateMode){deleteMode=false;truncateMode=false;deleteTargetPad=null;}
  if(resampleState===null){resampleState="select";resampleTarget={bank:currentBank,pad:selectedPad};syncPadVisuals();hud.innerHTML=`<b>${extOn?"EXT SAMPLE":"RESAMPLE"} TARGET:</b> BANK ${BANK_NAMES[currentBank]} PAD ${selectedPad+1} — CLICK PAD OR PRESS <b>REC</b> TO ARM`;return;}
  if(resampleState==="select"){if(!resampleTarget)resampleTarget={bank:currentBank,pad:selectedPad};resampleState="armed";resampleChunksL=[];resampleChunksR=[];resampleFrames=0;syncPadVisuals();hud.innerHTML=`<b>${extOn?"EXT SAMPLE":"RESAMPLE"} ARMED</b> → BANK ${BANK_NAMES[resampleTarget.bank]} PAD ${resampleTarget.pad+1} — WAITING FOR AUDIO...`;return;}
  if(resampleState==="armed"){resampleState=null;resampleTarget=null;syncPadVisuals();hud.innerHTML="<b>RESAMPLE DISARMED</b>";return;}
  if(resampleState==="recording")finishResampleCapture();
};
$("btn-del").onclick=()=>{
  if(remainMode)remainMode=false;if(resampleState){resampleState=null;resampleTarget=null;resampleChunksL=[];resampleChunksR=[];resampleFrames=0;}
  if(!deleteMode){deleteMode=true;truncateMode=false;deleteTargetPad=null;syncPadVisuals();hud.innerHTML="<b>DELETE ARMED:</b> CLICK PAD + <b>DEL</b> TO ERASE · OR PRESS <b>MARK</b> TO TRUNCATE";return;}
  if(truncateMode){const t=deleteTargetPad!==null?deleteTargetPad:selectedPad;deleteMode=false;truncateMode=false;deleteTargetPad=null;truncatePadSample(currentBank,t);syncPadVisuals();return;}
  if(deleteTargetPad!==null){const p=banks[currentBank][deleteTargetPad],di=deleteTargetPad;stopPadVoice(currentBank,di);Object.assign(p,{buffer:null,cache:{},startNorm:0,endNorm:1,loopBeats:null,waveZoom:1,waveScroll:0,syncWarp:false,pitch:1,name:`EMPTY ${BANK_NAMES[currentBank]}${di+1}`});deleteTargetPad=null;refreshAllBankUI();applyFxRealtime();syncPadVisuals();syncWaveEditorUI();renderAllWaveCanvases();hud.innerHTML=`<b>DELETED</b> BANK ${BANK_NAMES[currentBank]} PAD ${di+1}`;}
  else{deleteMode=false;truncateMode=false;syncPadVisuals();hud.innerHTML="<b>DELETE EXITED</b>";}
};
$("btn-remain").onclick=()=>{if(deleteMode||truncateMode){deleteMode=false;truncateMode=false;deleteTargetPad=null;}if(resampleState){resampleState=null;resampleTarget=null;}remainMode=!remainMode;syncPadVisuals();};
function switchTab(t){
  document.querySelectorAll("[data-tab]").forEach(b=>b.classList.toggle("active",b.dataset.tab===t));
  document.querySelectorAll(".view-panel").forEach(v=>v.classList.toggle("active",v.id===`view-${t}`));
  syncPadVisuals();if(t==="seq")requestAnimationFrame(()=>drawSeqDisplays());if(t==="wave"){syncWaveEditorUI();showPadBpmOnDisplay(curPadObj());requestAnimationFrame(renderAllWaveCanvases);}
}
$("btn-mark").onclick=()=>{
  if(deleteMode){truncateMode=!truncateMode;deleteTargetPad=truncateMode?(deleteTargetPad!==null?deleteTargetPad:(curPadObj().buffer?selectedPad:null)):null;syncPadVisuals();hud.innerHTML=truncateMode&&deleteTargetPad!==null?`<b>TRUNCATE ARMED:</b> BANK ${BANK_NAMES[currentBank]} PAD ${deleteTargetPad+1} — PRESS <b>DEL</b>`:"<b>DELETE ARMED</b>";return;}
  switchTab("wave");
};
document.querySelectorAll("[data-tab]").forEach(b=>b.onclick=()=>switchTab(b.dataset.tab));

function assignBufferToPad(bIdx,pIdx,buf,name){
  const pad=banks[bIdx][pIdx];Object.assign(pad,{buffer:buf,cache:{},startNorm:0,endNorm:1,loopBeats:null,waveZoom:1,waveScroll:0,syncWarp:false,pitch:1,name:name.replace(/\.[^.]+$/,"").slice(0,16).toUpperCase()});
  selectedPad=pIdx;refreshAllBankUI();syncPadVisuals();syncWaveEditorUI();showPadBpmOnDisplay(pad);renderAllWaveCanvases();triggerPad(bIdx,pIdx);
  const info=detectLoopBpm(pad);hud.innerHTML=`LOADED <b>${name}</b> → ${BANK_NAMES[bIdx]}${pIdx+1}${info?` // <b>${info.padBpm.toFixed(2)} BPM (${info.beats}B)</b>`:""}`;
}
function handlePadPress(idx){
  selectedPad=idx;const pad=banks[currentBank][idx];updateDynamicDisplay();syncWaveEditorUI();
  if(resampleState==="select"){resampleTarget={bank:currentBank,pad:idx};syncPadVisuals();hud.innerHTML=`<b>${extOn?"EXT SAMPLE":"RESAMPLE"} TARGET:</b> BANK ${BANK_NAMES[currentBank]} PAD ${idx+1} — PRESS <b>REC</b> TO ARM`;return;}
  if(deleteMode){if(!pad.buffer){hud.innerHTML=`<b>DELETE:</b> PAD ${idx+1} IS EMPTY`;return;}deleteTargetPad=idx;syncPadVisuals();hud.innerHTML=truncateMode?`<b>TRUNCATE ARMED:</b> PAD ${idx+1} — PRESS <b>DEL</b>`:`<b>DELETE TARGET:</b> PAD ${idx+1} — PRESS <b>DEL</b> OR <b>MARK</b>`;return;}
  if(remainMode){pad.fxSend=!pad.fxSend;updateAllMixerNodes();applyFxRealtime();syncPadVisuals();refreshMixerUI();return;}
  if(pad.loop&&pad.activeVoice){stopPadVoice(currentBank,idx);showPadBpmOnDisplay(pad);renderAllWaveCanvases();return;}
  triggerPad(currentBank,idx);showPadBpmOnDisplay(pad);renderAllWaveCanvases();
}
document.querySelectorAll(".pad").forEach(el=>{
  const idx=+el.dataset.pad;el.addEventListener("mousedown",()=>handlePadPress(idx));
  const rel=()=>{if(!remainMode&&!deleteMode&&resampleState!=="select"&&banks[currentBank][idx].gate&&!holdOn)stopPadVoice(currentBank,idx);};
  el.addEventListener("mouseup",rel);el.addEventListener("mouseleave",rel);
  el.addEventListener("dragenter",e=>{e.preventDefault();el.classList.add("drag-over");});
  el.addEventListener("dragover",e=>{e.preventDefault();e.dataTransfer.dropEffect="copy";el.classList.add("drag-over");});
  el.addEventListener("dragleave",()=>el.classList.remove("drag-over"));
  el.addEventListener("drop",async e=>{e.preventDefault();e.stopPropagation();el.classList.remove("drag-over");initAudio();const sid=draggingSampleId||e.dataTransfer.getData("text/plain");if(sid&&sampleRegistry.has(sid)){const en=sampleRegistry.get(sid);draggingSampleId=null;const b=await resolveSampleBuffer(en);if(b)assignBufferToPad(currentBank,idx,b,en.name);return;}const f=e.dataTransfer.files&&e.dataTransfer.files[0];if(f)assignBufferToPad(currentBank,idx,await ac.decodeAudioData(await f.arrayBuffer()),f.name);});
});

const syncBtn=$("btn-sync-bpm");
if(syncBtn&&!$("chk-wave-sync")){
  const lbl=document.createElement("label");lbl.style.cssText="display:inline-flex;align-items:center;gap:4px;font-size:10px;font-weight:700;color:#ffb899;cursor:pointer;background:#171a20;padding:4px 7px;border-radius:4px;box-shadow:inset 0 1px 4px rgba(0,0,0,.75)";lbl.title="Lock Pad + Sequencer Clock to TIME FX (Warp)";
  lbl.innerHTML=`<input type="checkbox" id="chk-wave-sync" style="accent-color:#ff2a3c;cursor:pointer;margin:0">SYNC`;syncBtn.after(lbl);
  $("chk-wave-sync").onchange=e=>{const p=curPadObj();p.syncWarp=e.target.checked;applyFxRealtime();hud.innerHTML=`BANK ${BANK_NAMES[currentBank]} PAD ${selectedPad+1} TIME SYNC: <b>${p.syncWarp?"ON":"OFF"}</b>`;};
}
const miniCanvas=$("mini-wave-canvas"),miniCtx=miniCanvas.getContext("2d"),waveCanvas=$("wave-canvas"),waveCtx=waveCanvas.getContext("2d"),rngStart=$("rng-start"),rngEnd=$("rng-end"),rngPitch=$("rng-pitch");
const fmtZoom=z=>z>=10?`${Math.round(z)}x`:`${Math.round(z*10)/10}x`;
function setWaveZoom(nz,anchor=.5){const p=curPadObj(),mz=getMaxZoomForPad(p),oS=1/p.waveZoom,cz=Math.max(1,Math.min(mz,nz)),nS=1/cz;p.waveZoom=cz;p.waveScroll=Math.max(0,Math.min(1-nS,p.waveScroll+anchor*oS-anchor*nS));$("lbl-zoom").textContent=fmtZoom(p.waveZoom);renderAllWaveCanvases();}
function resetPadZoom(p=curPadObj()){if(!p)return;p.waveZoom=1;p.waveScroll=0;if(p===curPadObj()&&$("lbl-zoom"))$("lbl-zoom").textContent="1x";}
function syncWaveEditorUI(){
  const p=curPadObj(),dur=p.buffer?p.buffer.duration:0,semi=rateToSemi(p.pitch),mz=getMaxZoomForPad(p);
  p.waveZoom=Math.max(1,Math.min(mz,p.waveZoom||1));p.waveScroll=Math.max(0,Math.min(1-1/p.waveZoom,p.waveScroll||0));
  $("lbl-zoom").textContent=fmtZoom(p.waveZoom);$("wave-pad-lbl").textContent=`BANK ${BANK_NAMES[currentBank]} · PAD ${selectedPad+1} [${p.name}]`;
  if($("chk-wave-sync"))$("chk-wave-sync").checked=!!p.syncWarp;
  rngStart.value=p.startNorm;rngEnd.value=p.endNorm;rngPitch.value=semi.toFixed(2);
  $("lbl-pad-pitch").textContent=`${semi>=0?"+":""}${semi.toFixed(2)} st`;$("lbl-start-ms").textContent=(p.startNorm*dur).toFixed(3)+" s";$("lbl-end-ms").textContent=(p.endNorm*dur).toFixed(3)+" s";
  const info=detectLoopBpm(p);if(info){if(document.activeElement!==waveBpmInp)waveBpmInp.value=fmtBpm(info.padBpm);waveBpmInp.disabled=false;btnWaveBeats.textContent=`${info.beats}B`;}else{waveBpmInp.value="";waveBpmInp.disabled=true;btnWaveBeats.textContent="--";}
  updateDynamicDisplay();syncGainWheel(false);
}
function drawMiniWave(){
  const wrap=$("mini-wave-wrap");if(!wrap||!wrap.clientWidth)return;const dpr=window.devicePixelRatio||1,w=wrap.clientWidth,h=wrap.clientHeight;
  if(miniCanvas.width!==Math.floor(w*dpr)||miniCanvas.height!==Math.floor(h*dpr)){miniCanvas.width=Math.floor(w*dpr);miniCanvas.height=Math.floor(h*dpr);}
  miniCtx.setTransform(dpr,0,0,dpr,0,0);miniCtx.fillStyle="#090b0e";miniCtx.fillRect(0,0,w,h);
  const p=curPadObj(),disp=getDisplayBuffer(p);if(!disp)return;
  const data=disp.getChannelData(0),step=Math.max(1,Math.floor(data.length/w));miniCtx.strokeStyle="rgba(224,90,71,.72)";miniCtx.lineWidth=1;miniCtx.beginPath();
  for(let x=0;x<w;x++){const idx=Math.floor(x/w*data.length);let mn=1,mx=-1;for(let k=0;k<step&&idx+k<data.length;k++){const v=data[idx+k];if(v<mn)mn=v;if(v>mx)mx=v;}miniCtx.moveTo(x,(1-mx)*.5*h);miniCtx.lineTo(x,(1-mn)*.5*h);}
  miniCtx.stroke();const sx=p.startNorm*w,ex=p.endNorm*w;miniCtx.fillStyle="rgba(0,0,0,.55)";miniCtx.fillRect(0,0,sx,h);miniCtx.fillRect(ex,0,w-ex,h);
  miniCtx.fillStyle="#4dff91";miniCtx.fillRect(sx,0,1.5,h);miniCtx.fillStyle="#ff3850";miniCtx.fillRect(ex-1.5,0,1.5,h);
  const vx=p.waveScroll*w,vw=Math.max(6,w/p.waveZoom);miniCtx.fillStyle="rgba(255,255,255,.14)";miniCtx.fillRect(vx,0,vw,h);miniCtx.strokeStyle="rgba(255,195,140,.9)";miniCtx.lineWidth=1.5;miniCtx.strokeRect(vx+.75,.75,vw-1.5,h-1.5);
  const ph=getPlayheadNorm(p);if(ph!==null){miniCtx.strokeStyle="#fff";miniCtx.beginPath();miniCtx.moveTo(ph*w,0);miniCtx.lineTo(ph*w,h);miniCtx.stroke();}
}
function drawWaveform(){
  const wrap=$("wave-wrap");if(!wrap||!wrap.clientWidth)return;const dpr=window.devicePixelRatio||1,w=wrap.clientWidth,h=wrap.clientHeight;
  if(waveCanvas.width!==Math.floor(w*dpr)||waveCanvas.height!==Math.floor(h*dpr)){waveCanvas.width=Math.floor(w*dpr);waveCanvas.height=Math.floor(h*dpr);}
  waveCtx.setTransform(dpr,0,0,dpr,0,0);waveCtx.fillStyle="#0b0d11";waveCtx.fillRect(0,0,w,h);waveCtx.strokeStyle="rgba(255,255,255,.05)";waveCtx.lineWidth=1;waveCtx.beginPath();waveCtx.moveTo(0,h/2);waveCtx.lineTo(w,h/2);for(let i=1;i<8;i++){waveCtx.moveTo(w/8*i,0);waveCtx.lineTo(w/8*i,h);}waveCtx.stroke();
  const p=curPadObj(),disp=getDisplayBuffer(p);
  if(!disp){waveCtx.fillStyle="#6d727b";waveCtx.font="bold 12px Courier New";waveCtx.textAlign="center";waveCtx.fillText("NO SAMPLE LOADED — DRAG AUDIO ONTO PAD",w/2,h/2+4);return;}
  const vS=p.waveScroll,vSp=1/p.waveZoom,vE=Math.min(1,vS+vSp),n2x=n=>(n-vS)/vSp*w,data=disp.getChannelData(0),sS=Math.floor(vS*data.length),eS=Math.floor(vE*data.length),vis=Math.max(1,eS-sS),step=Math.max(1,Math.floor(vis/w)),g=p.vol,sx=n2x(p.startNorm),ex=n2x(p.endNorm);
  waveCtx.fillStyle="rgba(0,0,0,.55)";if(sx>0)waveCtx.fillRect(0,0,Math.min(w,sx),h);if(ex<w)waveCtx.fillRect(Math.max(0,ex),0,w-Math.max(0,ex),h);
  const aL=Math.max(0,sx),aR=Math.min(w,ex);if(aR>aL){waveCtx.fillStyle="rgba(224,90,71,.08)";waveCtx.fillRect(aL,0,aR-aL,h);}
  waveCtx.strokeStyle=g>1.05?"#ff6844":"#e05a47";waveCtx.lineWidth=1.35;waveCtx.beginPath();
  if(vis<=w*2){for(let i=0;i<vis&&sS+i<data.length;i++){const x=i/Math.max(1,vis-1)*w,y=(1-Math.max(-1,Math.min(1,data[sS+i]*g)))*.5*h;i===0?waveCtx.moveTo(x,y):waveCtx.lineTo(x,y);}}
  else{for(let x=0;x<w;x++){const idx=sS+Math.floor(x/w*vis);let mn=1,mx=-1;for(let k=0;k<step&&idx+k<data.length;k++){const v=Math.max(-1,Math.min(1,data[idx+k]*g));if(v<mn)mn=v;if(v>mx)mx=v;}waveCtx.moveTo(x,(1-mx)*.5*h);waveCtx.lineTo(x,(1-mn)*.5*h);}}
  waveCtx.stroke();
  if(sx>=-4&&sx<=w+4){waveCtx.strokeStyle="#4dff91";waveCtx.lineWidth=2;waveCtx.beginPath();waveCtx.moveTo(sx,0);waveCtx.lineTo(sx,h);waveCtx.stroke();waveCtx.fillStyle="#4dff91";waveCtx.fillRect(sx,0,36,15);waveCtx.fillStyle="#08120c";waveCtx.font="bold 9px Courier New";waveCtx.textAlign="left";waveCtx.fillText("START",sx+4,10);}
  if(ex>=-4&&ex<=w+4){waveCtx.strokeStyle="#ff3850";waveCtx.lineWidth=2;waveCtx.beginPath();waveCtx.moveTo(ex,0);waveCtx.lineTo(ex,h);waveCtx.stroke();waveCtx.fillStyle="#ff3850";waveCtx.fillRect(Math.max(0,ex-28),h-15,28,15);waveCtx.fillStyle="#fff";waveCtx.font="bold 9px Courier New";waveCtx.textAlign="left";waveCtx.fillText("END",Math.max(4,ex-23),h-5);}
  const ph=getPlayheadNorm(p);if(ph!==null){const px=n2x(ph);if(px>=-2&&px<=w+2){waveCtx.save();waveCtx.strokeStyle="#fff";waveCtx.shadowColor="rgba(255,220,150,.95)";waveCtx.shadowBlur=8;waveCtx.lineWidth=2;waveCtx.beginPath();waveCtx.moveTo(px,0);waveCtx.lineTo(px,h);waveCtx.stroke();waveCtx.restore();}}
}
const renderAllWaveCanvases=()=>{if($("view-wave").classList.contains("active")){drawMiniWave();drawWaveform();}};

(()=>{
  const wrap=$("wave-wrap");if(!wrap||$("wave-gain-wheel"))return;
  if(!$("sp202-wave-gain-css")){const st=document.createElement("style");st.id="sp202-wave-gain-css";st.textContent=`#wave-wrap{position:relative!important}#wave-gain-wheel{position:absolute;top:8px;right:8px;z-index:8;display:flex;flex-direction:column;align-items:center;gap:3px;padding:5px 6px;background:rgba(15,17,22,.88);border:1px solid #323742;border-radius:4px;box-shadow:0 2px 8px rgba(0,0,0,.75);cursor:ns-resize;user-select:none}#wave-gain-wheel:hover{border-color:#e05a47}.wg-ring{width:26px;height:26px;border-radius:50%;background:radial-gradient(circle at 35% 30%,#383d46,#1a1d22 72%,#0d0f12);border:1px solid #090b0d;box-shadow:0 2px 4px rgba(0,0,0,.85),inset 0 1px 1px rgba(255,255,255,.16);display:flex;align-items:center;justify-content:center}.wg-cap{position:relative;width:19px;height:19px;border-radius:50%;background:radial-gradient(circle at 35% 30%,#2d323a,#14171b 85%);pointer-events:none}.wg-ptr{position:absolute;top:2px;left:50%;transform:translateX(-50%);width:2px;height:7px;border-radius:1px;background:#ff4e3a;box-shadow:0 0 5px rgba(255,70,50,.9)}.wg-lbl{font:700 8px "Courier New",monospace;color:#cfd4dc;letter-spacing:.5px;line-height:1}`;document.head.appendChild(st);}
  const MAX_GAIN=1.5,w=document.createElement("div");w.id="wave-gain-wheel";w.title="Sample Gain: Drag Up/Down or Scroll · Double-Click to Reset (85%)";w.innerHTML=`<div class="wg-ring"><div class="wg-cap" id="wg-cap"><div class="wg-ptr"></div></div></div><div class="wg-lbl" id="wg-lbl">85%</div>`;wrap.appendChild(w);
  syncGainWheel=(anim=false)=>{const p=curPadObj();if(!p)return;const cap=$("wg-cap"),lbl=$("wg-lbl");if(cap){cap.style.transition=anim?"transform .16s ease":"none";cap.style.transform=`rotate(${((Math.max(0,Math.min(1,p.vol/MAX_GAIN))-.5)*270).toFixed(1)}deg)`;}if(lbl)lbl.textContent=`${Math.round(p.vol*100)}%`;};
  const applyWG=(v,a=false)=>{const p=curPadObj();if(!p)return;p.vol=Math.max(0,Math.min(MAX_GAIN,Math.round(v*100)/100));updateAllMixerNodes();const mf=$(`mix-vol-${selectedPad}`);if(mf)mf.value=Math.min(parseFloat(mf.max)||1.2,p.vol);syncGainWheel(a);renderAllWaveCanvases();hud.innerHTML=`BANK ${BANK_NAMES[currentBank]} PAD ${selectedPad+1} GAIN: <b>${Math.round(p.vol*100)}%</b>`;};
  w.onmousedown=e=>{e.preventDefault();e.stopPropagation();initAudio();const sy=e.clientY,sv=curPadObj().vol,mv=ev=>applyWG(sv+(sy-ev.clientY)/110),up=()=>{window.removeEventListener("mousemove",mv);window.removeEventListener("mouseup",up);};window.addEventListener("mousemove",mv);window.addEventListener("mouseup",up);};
  w.addEventListener("wheel",e=>{e.preventDefault();e.stopPropagation();initAudio();applyWG(curPadObj().vol+(e.deltaY<0?.05:-.05));},{passive:false});
  w.ondblclick=e=>{e.stopPropagation();initAudio();applyWG(.85,true);};syncGainWheel(false);
})();

const waveFileMenu=$("wave-file-menu"),btnWaveFileMenu=$("btn-wave-file-menu"),closeWaveMenu=()=>{waveFileMenu.classList.remove("open");btnWaveFileMenu.classList.remove("active");};
btnWaveFileMenu.onclick=e=>{e.stopPropagation();btnWaveFileMenu.classList.toggle("active",waveFileMenu.classList.toggle("open"));};
window.addEventListener("mousedown",e=>{if(!e.target.closest("#wave-file-menu-wrap"))closeWaveMenu();});
$("menu-export-fx").onclick=()=>{closeWaveMenu();exportPadWav(true);};$("menu-export-raw").onclick=()=>{closeWaveMenu();exportPadWav(false);};
$("menu-truncate-pad").onclick=()=>{closeWaveMenu();truncatePadSample(currentBank,selectedPad);};$("menu-reset-marks").onclick=()=>{closeWaveMenu();$("btn-wave-reset").click();};
$("btn-pad-bpm-dn").onclick=()=>stepPadBpm(-1);$("btn-pad-bpm-up").onclick=()=>stepPadBpm(1);
const commitWaveBpm=()=>{const v=parseFloat(waveBpmInp.value);Number.isFinite(v)&&v>0?setPadTargetBpm(currentBank,selectedPad,v):syncWaveEditorUI();};
waveBpmInp.addEventListener("change",commitWaveBpm);waveBpmInp.addEventListener("keydown",e=>{if(e.key==="Enter"){commitWaveBpm();waveBpmInp.blur();}});
btnWaveBeats.onclick=()=>{const p=curPadObj(),i=detectLoopBpm(p);if(!i)return;p.loopBeats=BEAT_CYCLE[(BEAT_CYCLE.indexOf(i.beats)+1)%BEAT_CYCLE.length];syncWaveEditorUI();showPadBpmOnDisplay(p);};
$("btn-match-master").onclick=()=>setPadTargetBpm(currentBank,selectedPad,baseBpm);
$("btn-sync-bpm").onclick=()=>{const i=detectLoopBpm(curPadObj());if(i){updateBpm(i.padBpm);hud.innerHTML=`MASTER BPM LOCKED: <b>${baseBpm} BPM</b>`;}};
$("btn-zoom-in").onclick=()=>setWaveZoom(curPadObj().waveZoom*2,.5);$("btn-zoom-out").onclick=()=>setWaveZoom(curPadObj().waveZoom/2,.5);$("btn-zoom-fit").onclick=()=>{resetPadZoom();renderAllWaveCanvases();};
waveCanvas.addEventListener("wheel",e=>{e.preventDefault();const r=waveCanvas.getBoundingClientRect();setWaveZoom(curPadObj().waveZoom*(e.deltaY<0?1.45:1/1.45),Math.max(0,Math.min(1,(e.clientX-r.left)/r.width)));},{passive:false});
let dragMini=false,dragMark=null;
const panMini=e=>{const p=curPadObj(),r=miniCanvas.getBoundingClientRect(),n=Math.max(0,Math.min(1,(e.clientX-r.left)/r.width)),s=1/p.waveZoom;p.waveScroll=Math.max(0,Math.min(1-s,n-s/2));renderAllWaveCanvases();};
miniCanvas.onmousedown=e=>{dragMini=true;panMini(e);};
rngStart.oninput=()=>{const p=curPadObj();p.startNorm=Math.min(+rngStart.value,p.endNorm-getMinNormGap(p));syncWaveEditorUI();showPadBpmOnDisplay(p);renderAllWaveCanvases();};
rngEnd.oninput=()=>{const p=curPadObj();p.endNorm=Math.max(+rngEnd.value,p.startNorm+getMinNormGap(p));syncWaveEditorUI();showPadBpmOnDisplay(p);renderAllWaveCanvases();};
rngPitch.oninput=()=>setPadPitchRate(currentBank,selectedPad,semiToRate(+rngPitch.value));rngPitch.ondblclick=()=>setPadPitchRate(currentBank,selectedPad,1);
const cx2n=x=>{const p=curPadObj(),r=waveCanvas.getBoundingClientRect();return Math.max(0,Math.min(1,p.waveScroll+Math.max(0,Math.min(1,(x-r.left)/r.width))/p.waveZoom));};
waveCanvas.oncontextmenu=e=>e.preventDefault();
waveCanvas.onmousedown=e=>{const n=cx2n(e.clientX),p=curPadObj(),tol=.06/p.waveZoom;dragMark=e.button===2?"end":(Math.abs(n-p.endNorm)<Math.abs(n-p.startNorm)&&Math.abs(n-p.endNorm)<tol?"end":"start");applyMark(n);};
const applyMark=n=>{const p=curPadObj(),mg=getMinNormGap(p);if(dragMark==="start")p.startNorm=Math.min(n,p.endNorm-mg);else p.endNorm=Math.max(n,p.startNorm+mg);syncWaveEditorUI();showPadBpmOnDisplay(p);renderAllWaveCanvases();};
window.addEventListener("mousemove",e=>{if(dragMini)panMini(e);if(dragMark)applyMark(cx2n(e.clientX));});window.addEventListener("mouseup",()=>{dragMini=false;dragMark=null;});
$("btn-wave-audition").onclick=()=>triggerPad(currentBank,selectedPad);
$("btn-wave-reset").onclick=()=>{const p=curPadObj();p.startNorm=0;p.endNorm=1;p.loopBeats=null;setPadPitchRate(currentBank,selectedPad,1);resetPadZoom(p);syncWaveEditorUI();showPadBpmOnDisplay(p);renderAllWaveCanvases();};

function addFilesToTree(fl){
  const af=Array.from(fl).filter(f=>f.type.startsWith("audio/")||/\.(wav|mp3|ogg|flac|m4a|aif|aiff)$/i.test(f.name));
  af.forEach(file=>{const pts=(file.webkitRelativePath||("LOADED FILES/"+file.name)).split("/").filter(Boolean),name=pts.pop();let n=folderTree;pts.forEach(d=>{if(!n.folders[d])n.folders[d]={name:d,folders:{},files:[]};n=n.folders[d];});const id="smp_"+(sampleIdCounter++),en={id,name,file,buffer:null};sampleRegistry.set(id,en);n.files.push(en);});
  if(af.length){renderSampleTree();hud.innerHTML=`EXPLORER: ADDED <b>${af.length}</b> SAMPLE(S)`;}
}
async function resolveSampleBuffer(en){initAudio();if(en.buffer)return en.buffer;if(en.file)return en.buffer=await ac.decodeAudioData(await en.file.arrayBuffer());return null;}
async function auditionSample(en,el){initAudio();if(ac.state==="suspended")ac.resume();stopAudition();const b=await resolveSampleBuffer(en);if(!b)return;const s=ac.createBufferSource();s.buffer=b;s.connect(masterGain);s.start();auditionSource=s;auditionEl=el;el.classList.add("auditioning");s.onended=()=>{if(auditionSource===s)stopAudition();};}
function renderTreeNode(node,cont){
  Object.values(node.folders).forEach(sub=>{const h=document.createElement("div");h.className="tree-folder-hdr";h.textContent=`▾ ${sub.name}`;const c=document.createElement("div");c.className="tree-children";h.onclick=()=>{h.textContent=`${c.classList.toggle("collapsed")?"▸":"▾"} ${sub.name}`;};cont.append(h,c);renderTreeNode(sub,c);});
  node.files.forEach(en=>{const r=document.createElement("div");r.className="tree-file";r.draggable=true;r.innerHTML=`<span class="tree-file-name">${en.name}</span><span class="tree-file-tag">DRAG</span>`;r.onclick=()=>auditionSample(en,r);r.ondragstart=e=>{draggingSampleId=en.id;e.dataTransfer.setData("text/plain",en.id);e.dataTransfer.effectAllowed="copy";};r.ondragend=()=>{draggingSampleId=null;};cont.appendChild(r);});
}
function renderSampleTree(){const w=$("sample-tree");w.innerHTML="";if(!Object.keys(folderTree.folders).length&&!folderTree.files.length){w.innerHTML=`<div style="padding:18px 10px;text-align:center;font-size:10px;color:var(--silk-dim);line-height:1.6">NO SAMPLES LOADED<br>CLICK <b>LOAD FOLDER</b> OR <b>LOAD FILES</b><br>OR DROP AUDIO DIRECTLY ONTO PADS</div>`;return;}renderTreeNode(folderTree,w);}
(()=>{const h=$("explorer-drag-handle");let dx=0,dy=0,dr=false;h.onmousedown=e=>{if(e.target.closest(".drawer-close"))return;dr=true;const r=drawer.getBoundingClientRect();dx=e.clientX-r.left;dy=e.clientY-r.top;};window.addEventListener("mousemove",e=>{if(!dr)return;drawer.style.left=Math.max(0,Math.min(innerWidth-100,e.clientX-dx))+"px";drawer.style.top=Math.max(0,Math.min(innerHeight-60,e.clientY-dy))+"px";});window.addEventListener("mouseup",()=>{dr=false;});})();
const toggleDrawer=f=>{const o=f!==undefined?f:!drawer.classList.contains("open");drawer.classList.toggle("open",o);spExplorerBtn.classList.toggle("active",o);$("btn-open-explorer").classList.toggle("active",o);};
spExplorerBtn.onclick=()=>toggleDrawer();$("btn-open-explorer").onclick=()=>toggleDrawer();$("btn-close-drawer").onclick=()=>toggleDrawer(false);
$("btn-load-folder").onclick=()=>$("inp-folder").click();$("btn-load-files").onclick=()=>$("inp-files").click();
$("inp-folder").onchange=e=>{addFilesToTree(e.target.files);e.target.value="";};$("inp-files").onchange=e=>{addFilesToTree(e.target.files);e.target.value="";};

const getStepDuration=s=>{const b=60/bpm/4,sw=swingPct/100*b*.5;return s%2===0?b+sw:b-sw;};
function scheduleStep(step,bar,time){const pat=patterns[playMode==="song"?songBars[bar].pat:currentPat];for(let b=0;b<NUM_BANKS;b++)for(let p=0;p<NUM_PADS;p++){const v=pat[b][p][step];if(v>0&&(playMode!=="song"||songBars[bar].tracks[b][p]))triggerPad(b,p,time,true,null,v);}setTimeout(()=>{if(isPlaying)updatePlayheadUI(step,bar);},Math.max(0,(time-ac.currentTime)*1e3));}
function schedulerTick(){while(nextStepTime<ac.currentTime+.1){scheduleStep(currentStep,currentBar,nextStepTime);nextStepTime+=getStepDuration(currentStep);if(++currentStep>=NUM_STEPS){currentStep=0;if(playMode==="song")currentBar=(currentBar+1)%NUM_BARS;}}}
function startTransport(){initAudio();if(ac.state==="suspended")ac.resume();if(isPlaying)return;isPlaying=true;currentStep=0;currentBar=0;nextStepTime=ac.currentTime+.03;schedTimer=setInterval(schedulerTick,25);$("btn-play").classList.add("lit");drawSevenSegDisplay(bpm);drawSeqDisplays(0,0);}
function stopTransport(){isPlaying=false;if(schedTimer){clearInterval(schedTimer);schedTimer=null;}$("btn-play").classList.remove("lit");document.querySelectorAll(".step-num.now,.step-cell.playhead,.arr-bar-pat.now,.arr-cell.now").forEach(e=>e.classList.remove("now","playhead"));stepLed.textContent="01:01";drawSeqDisplays(0,0);}
function updatePlayheadUI(step,bar){stepLed.textContent=`${String(bar+1).padStart(2,"0")}:${String(step+1).padStart(2,"0")}`;drawSeqDisplays(step,bar);document.querySelectorAll(".step-num.now,.step-cell.playhead,.arr-bar-pat.now,.arr-cell.now").forEach(e=>e.classList.remove("now","playhead"));if($(`snum-${step}`))$(`snum-${step}`).classList.add("now");document.querySelectorAll(`.step-cell[data-step="${step}"]`).forEach(e=>e.classList.add("playhead"));if(playMode==="song"){if($(`arr-bp-${bar}`))$(`arr-bp-${bar}`).classList.add("now");document.querySelectorAll(`.arr-cell[data-bar="${bar}"]`).forEach(e=>e.classList.add("now"));}}

function updateVelSquareUI(p,v,anim=false){const sq=$(`seq-vel-${p}`);if(!sq)return;sq.style.setProperty("--v",v);sq.title=`Track Velocity: ${Math.round(v*100)}% (Drag, Scroll, or Dbl-Click)`;const cap=sq.querySelector(".seq-vel-cap");if(cap){cap.style.transition=anim?"transform .18s cubic-bezier(.22,1,.36,1)":"none";cap.style.transform=`rotate(${((Math.max(0,Math.min(1,(v-.15)/.85))-.5)*270).toFixed(1)}deg)`;}}
const applyStepCellUI=(c,v)=>{c.classList.toggle("on",v>0);v>0?c.style.setProperty("--v",v):c.style.removeProperty("--v");};
function buildPatternButtons(){const w=$("pat-selector");for(let i=0;i<NUM_PATS;i++){const b=document.createElement("button");b.className="hw-btn mini-btn"+(i===0?" active":"");b.textContent=`P${i+1}`;b.onclick=()=>{currentPat=i;w.querySelectorAll(".mini-btn").forEach((bt,idx)=>bt.classList.toggle("active",idx===i));$("seq-pat-label").textContent=`P${i+1}`;refreshSequencerUI();drawSeqDisplays();};w.appendChild(b);}}
function buildSequencerGrid(){
  const w=$("seq-grid");w.innerHTML="";const hdr=document.createElement("div");hdr.className="seq-step-nums";hdr.innerHTML="<div></div>";
  for(let s=0;s<NUM_STEPS;s++){const d=document.createElement("div");d.id=`snum-${s}`;d.className="step-num"+(s%4===0?" beat":"");d.textContent=s+1;hdr.appendChild(d);}w.appendChild(hdr);
  for(let p=0;p<NUM_PADS;p++){
    const row=document.createElement("div");row.className="seq-row";const info=document.createElement("div");info.className="seq-pad-info";
    info.innerHTML=`<span class="seq-pad-num" id="seq-pnum-${p}">A${p+1}</span><span class="seq-pad-name" id="seq-pname-${p}"></span><button class="seq-mute-mini" id="seq-mute-${p}" title="Mute">M</button><div class="seq-vel-sq" id="seq-vel-${p}"><div class="seq-vel-cap"><div class="seq-vel-ptr"></div></div></div>`;
    info.onmousedown=e=>{if(e.target.closest(".seq-mute-mini")||e.target.closest(".seq-vel-sq"))return;selectedPad=p;updateDynamicDisplay();syncWaveEditorUI();showPadBpmOnDisplay(banks[currentBank][p]);triggerPad(currentBank,p,0,false,null,trackVel[currentBank][p]);};
    info.querySelector(".seq-mute-mini").onclick=()=>{banks[currentBank][p].mute=!banks[currentBank][p].mute;updateAllMixerNodes();refreshMixerUI();refreshSequencerUI();};
    const vp=info.querySelector(".seq-vel-sq");
    vp.onmousedown=e=>{e.preventDefault();e.stopPropagation();const sy=e.clientY,sv=trackVel[currentBank][p],mv=ev=>{const nv=Math.max(.15,Math.min(1,sv+(sy-ev.clientY)/95));trackVel[currentBank][p]=nv;updateVelSquareUI(p,nv);hud.innerHTML=`TRACK ${BANK_NAMES[currentBank]}${p+1} VELOCITY: <b>${Math.round(nv*100)}%</b>`;},up=()=>{window.removeEventListener("mousemove",mv);window.removeEventListener("mouseup",up);};window.addEventListener("mousemove",mv);window.addEventListener("mouseup",up);};
    vp.addEventListener("wheel",e=>{e.preventDefault();e.stopPropagation();const nv=Math.max(.15,Math.min(1,trackVel[currentBank][p]+(e.deltaY<0?.05:-.05)));trackVel[currentBank][p]=nv;updateVelSquareUI(p,nv);},{passive:false});
    vp.ondblclick=e=>{e.stopPropagation();trackVel[currentBank][p]=.85;updateVelSquareUI(p,.85,true);};row.appendChild(info);
    for(let s=0;s<NUM_STEPS;s++){
      const c=document.createElement("button");c.className="step-cell"+(s%4===0?" beat-start":"")+(Math.floor(s/4)%2===1?" beat-alt":"");c.dataset.pad=p;c.dataset.step=s;
      c.onmousedown=e=>{e.preventDefault();const sy=e.clientY,iV=patterns[currentPat][currentBank][p][s];let moved=false,bV=iV>0?iV:trackVel[currentBank][p];const mv=ev=>{if(!moved&&Math.abs(ev.clientY-sy)<4)return;moved=true;const nv=Math.max(.15,Math.min(1,bV+(sy-ev.clientY)/90));patterns[currentPat][currentBank][p][s]=nv;trackVel[currentBank][p]=nv;applyStepCellUI(c,nv);updateVelSquareUI(p,nv);},up=()=>{window.removeEventListener("mousemove",mv);window.removeEventListener("mouseup",up);if(!moved){const nv=iV>0?0:trackVel[currentBank][p];patterns[currentPat][currentBank][p][s]=nv;applyStepCellUI(c,nv);if(nv>0)updateVelSquareUI(p,nv,true);}};window.addEventListener("mousemove",mv);window.addEventListener("mouseup",up);};
      row.appendChild(c);
    }
    w.appendChild(row);
  }
}
function refreshSequencerUI(anim=false){const bn=BANK_NAMES[currentBank],pat=patterns[currentPat][currentBank];for(let p=0;p<NUM_PADS;p++){$(`seq-pnum-${p}`).textContent=`${bn}${p+1}`;$(`seq-pname-${p}`).textContent=banks[currentBank][p].name;$(`seq-mute-${p}`).classList.toggle("muted",banks[currentBank][p].mute);updateVelSquareUI(p,trackVel[currentBank][p],anim);}document.querySelectorAll(".step-cell").forEach(c=>applyStepCellUI(c,pat[+c.dataset.pad][+c.dataset.step]));}

const cancelFaderAnim=i=>{if(faderAnimIds[i]!==null){cancelAnimationFrame(faderAnimIds[i]);faderAnimIds[i]=null;}};
function animateMixerFader(i,tv,dur=260){cancelFaderAnim(i);const el=$(`mix-vol-${i}`);if(!el)return;const fr=parseFloat(el.value);if(!Number.isFinite(fr)||Math.abs(tv-fr)<.003){el.value=tv;return;}const t0=performance.now(),step=n=>{const p=Math.min(1,(n-t0)/dur),ez=p<.5?4*p*p*p:1-Math.pow(-2*p+2,3)/2;el.value=(fr+(tv-fr)*ez).toFixed(3);if(p<1)faderAnimIds[i]=requestAnimationFrame(step);else{el.value=tv;faderAnimIds[i]=null;}};faderAnimIds[i]=requestAnimationFrame(step);}
function buildMixerUI(){
  const g=$("mixer-grid");g.innerHTML="";
  for(let i=0;i<NUM_PADS;i++){
    const s=document.createElement("div");s.className="mix-strip";
    s.innerHTML=`<div class="mix-ch-id" id="mix-chid-${i}">A${i+1}</div><div class="mix-ch-name" id="mix-pname-${i}"></div><div class="mix-param"><span class="mix-param-lbl">PAN</span><input type="range" class="mix-mini-slider" id="mix-pan-${i}" min="-1" max="1" step="0.05" value="0"></div><div class="mix-param"><span class="mix-param-lbl">TUNE</span><input type="range" class="mix-mini-slider" id="mix-tune-${i}" min="0.5" max="2.0" step="0.005" value="1"></div><div class="mix-fader-area"><div class="fader-track-wrap"><input type="range" class="v-fader" id="mix-vol-${i}" min="0" max="1.2" step="0.01" value="0.85" orient="vertical"></div><div class="led-meter" id="meter-${i}"></div></div><div class="mix-btns"><button class="mix-btn" id="mix-fx-${i}">FX</button></div><div class="mix-btns"><button class="mix-btn" id="mix-m-${i}">M</button><button class="mix-btn" id="mix-s-${i}">S</button></div>`;
    g.appendChild(s);const mEl=s.querySelector(`#meter-${i}`);meterSegsUI[i]=[];for(let k=0;k<12;k++){const d=document.createElement("div");d.className="meter-seg";mEl.appendChild(d);meterSegsUI[i].push(d);}
    const vs=s.querySelector(`#mix-vol-${i}`);vs.onmousedown=()=>cancelFaderAnim(i);vs.oninput=e=>{cancelFaderAnim(i);banks[currentBank][i].vol=+e.target.value;updateAllMixerNodes();};
    s.querySelector(`#mix-pan-${i}`).oninput=e=>{banks[currentBank][i].pan=+e.target.value;updateAllMixerNodes();};
    s.querySelector(`#mix-tune-${i}`).oninput=e=>setPadPitchRate(currentBank,i,+e.target.value);s.querySelector(`#mix-tune-${i}`).ondblclick=()=>setPadPitchRate(currentBank,i,1);
    s.querySelector(`#mix-fx-${i}`).onclick=()=>{banks[currentBank][i].fxSend=!banks[currentBank][i].fxSend;updateAllMixerNodes();applyFxRealtime();refreshMixerUI();syncPadVisuals();};
    s.querySelector(`#mix-m-${i}`).onclick=()=>{banks[currentBank][i].mute=!banks[currentBank][i].mute;updateAllMixerNodes();refreshMixerUI();refreshSequencerUI();};
    s.querySelector(`#mix-s-${i}`).onclick=()=>{banks[currentBank][i].solo=!banks[currentBank][i].solo;updateAllMixerNodes();refreshMixerUI();};
  }
}
function refreshMixerUI(af=false){const bn=BANK_NAMES[currentBank];for(let i=0;i<NUM_PADS;i++){const ch=banks[currentBank][i];$(`mix-chid-${i}`).textContent=`${bn}${i+1}`;$(`mix-pname-${i}`).textContent=ch.name;if(af)animateMixerFader(i,ch.vol);else{cancelFaderAnim(i);$(`mix-vol-${i}`).value=ch.vol;}$(`mix-pan-${i}`).value=ch.pan;$(`mix-tune-${i}`).value=ch.pitch;$(`mix-fx-${i}`).classList.toggle("fx-on",ch.fxSend);$(`mix-m-${i}`).classList.toggle("m-on",ch.mute);$(`mix-s-${i}`).classList.toggle("s-on",ch.solo);}}
function buildArrangerUI(){
  const w=$("arr-grid");w.innerHTML="";const hdr=document.createElement("div");hdr.className="arr-header-row";hdr.innerHTML=`<div style="font-size:9px;color:var(--silk-dim);padding-left:4px">BAR / PAT</div>`;
  for(let b=0;b<NUM_BARS;b++){const btn=document.createElement("button");btn.className="arr-bar-pat";btn.id=`arr-bp-${b}`;btn.textContent=`P${songBars[b].pat+1}`;btn.onclick=()=>{songBars[b].pat=(songBars[b].pat+1)%NUM_PATS;btn.textContent=`P${songBars[b].pat+1}`;};hdr.appendChild(btn);}w.appendChild(hdr);
  for(let t=0;t<NUM_PADS;t++){const row=document.createElement("div");row.className="arr-row";row.innerHTML=`<div class="arr-trk-lbl"><span id="arr-tid-${t}">A${t+1}</span><b id="arr-pname-${t}" style="font-weight:400;overflow:hidden;text-overflow:ellipsis"></b></div>`;for(let b=0;b<NUM_BARS;b++){const c=document.createElement("button");c.className="arr-cell";c.dataset.bar=b;c.dataset.track=t;c.onmousedown=()=>{const cur=songBars[b].tracks[currentBank][t];songBars[b].tracks[currentBank][t]=!cur;c.classList.toggle("on",!cur);};row.appendChild(c);}w.appendChild(row);}
}
function refreshArrangerUI(){const bn=BANK_NAMES[currentBank];for(let b=0;b<NUM_BARS;b++){const bp=$(`arr-bp-${b}`);if(bp)bp.textContent=`P${songBars[b].pat+1}`;}for(let t=0;t<NUM_PADS;t++){$(`arr-tid-${t}`).textContent=`${bn}${t+1}`;$(`arr-pname-${t}`).textContent=banks[currentBank][t].name;}document.querySelectorAll(".arr-cell").forEach(c=>c.classList.toggle("on",songBars[+c.dataset.bar].tracks[currentBank][+c.dataset.track]));}
const refreshAllBankUI=(a=false)=>{refreshSequencerUI(a);refreshMixerUI(a);refreshArrangerUI();};

const meterBuf=new Uint8Array(128);
function uiAnimLoop(){
  if(ac){
    if($("view-mix").classList.contains("active"))for(let i=0;i<NUM_PADS;i++){const ch=banks[currentBank][i];if(!ch.analyser)continue;ch.analyser.getByteTimeDomainData(meterBuf);let pk=0;for(let k=0;k<meterBuf.length;k++){const v=Math.abs(meterBuf[k]-128)/128;if(v>pk)pk=v;}const lit=Math.min(12,Math.round(pk*16));for(let s=0;s<12;s++)meterSegsUI[i][s].className=s<lit?(s>=9?"meter-seg on-high":"meter-seg on-low"):"meter-seg";}
    if($("view-wave").classList.contains("active")&&curPadObj().activeVoice){drawMiniWave();drawWaveform();}
  }
  requestAnimationFrame(uiAnimLoop);
}

const updateBpm=v=>{const p=parseFloat(v);if(!Number.isFinite(p))return;baseBpm=Math.max(40,Math.min(240,Math.round(p*100)/100));syncSequencerTimeWarp();};
$("btn-bpm-dn").onclick=()=>updateBpm(baseBpm-1);$("btn-bpm-up").onclick=()=>updateBpm(baseBpm+1);$("rack-bpm-dn").onclick=()=>updateBpm(baseBpm-1);$("rack-bpm-up").onclick=()=>updateBpm(baseBpm+1);
rackBpmInp.onchange=()=>updateBpm(rackBpmInp.value);rackBpmInp.onkeydown=e=>{if(e.key==="Enter"){updateBpm(rackBpmInp.value);rackBpmInp.blur();}};
$("btn-tap").onclick=()=>{const n=performance.now();if(lastTap&&n-lastTap<2e3)updateBpm(6e4/(n-lastTap));lastTap=n;};
$("btn-play").onclick=startTransport;$("btn-stop").onclick=stopTransport;
$("btn-mode-pat").onclick=()=>{playMode="pat";$("btn-mode-pat").classList.add("active");$("btn-mode-song").classList.remove("active");};
$("btn-mode-song").onclick=()=>{playMode="song";$("btn-mode-song").classList.add("active");$("btn-mode-pat").classList.remove("active");};
$("rng-swing").oninput=e=>{swingPct=+e.target.value;$("lbl-swing").textContent=`${swingPct}%`;};
if($("btn-seq-demo"))$("btn-seq-demo").style.display="none";
$("btn-seq-clear").onclick=()=>{patterns[currentPat][currentBank].forEach(r=>r.fill(0));refreshSequencerUI();};
$("btn-mix-reset").onclick=()=>{for(let i=0;i<NUM_PADS;i++)Object.assign(banks[currentBank][i],{vol:.85,pan:0,pitch:1,mute:false,solo:false});updateAllMixerNodes();applyFxRealtime();refreshMixerUI(true);refreshSequencerUI();syncWaveEditorUI();};
$("btn-arr-fill").onclick=()=>{songBars.forEach(b=>b.tracks[currentBank].fill(true));refreshArrangerUI();};
$("btn-arr-clear").onclick=()=>{songBars.forEach(b=>b.tracks[currentBank].fill(false));refreshArrangerUI();};

function setupKnob(id,init,getL,onCh){
  const w=$(id),cap=w.querySelector(".knob-cap");let val=init;
  const ren=(sh,a)=>{cap.style.transition=a?"transform .22s cubic-bezier(.22,1,.36,1)":"none";cap.style.transform=`rotate(${(val-.5)*270}deg)`;if(sh)hud.innerHTML=`<b>${getL()}:</b> ${Math.round(val*100)}%`;};
  ren(false,false);
  w.onmousedown=e=>{e.preventDefault();initAudio();const sy=e.clientY,sv=val,mv=ev=>{val=Math.max(0,Math.min(1,sv+(sy-ev.clientY)/140));ren(true,false);onCh(val);},up=()=>{window.removeEventListener("mousemove",mv);window.removeEventListener("mouseup",up);};window.addEventListener("mousemove",mv);window.addEventListener("mouseup",up);};
  w.addEventListener("wheel",e=>{e.preventDefault();initAudio();val=Math.max(0,Math.min(1,val+(e.deltaY<0?.03:-.03)));ren(true,false);onCh(val);},{passive:false});
  w.ondblclick=()=>{initAudio();val=init;ren(true,true);onCh(val);};
  return(nv,a=true)=>{val=Math.max(0,Math.min(1,nv));ren(false,a);};
}
setupKnob("knob-vol",volVal,()=>"MASTER VOLUME",v=>{volVal=v;if(masterGain)masterGain.gain.setTargetAtTime(v,ac.currentTime,.015);});
const setCtrlKnob=setupKnob("knob-ctrl",.5,()=>ctrlTarget?`FX CTRL (${ctrlTarget.toUpperCase()})`:"FX CONTROL",v=>{if(ctrlTarget)fxVals[ctrlTarget]=v;applyFxRealtime();});
const syncFxBtns=()=>{document.querySelectorAll(".fx-btn").forEach(b=>b.classList.toggle("lit",b.dataset.fx==="pitch"?pitchOn:b.dataset.fx===mainFx));setCtrlKnob(ctrlTarget?fxVals[ctrlTarget]:.5,true);};
document.querySelectorAll(".fx-btn").forEach(el=>el.onclick=()=>{
  initAudio();const fx=el.dataset.fx;
  if(fx==="pitch"){pitchOn=!pitchOn;if(pitchOn){if(mainFx&&!BOTTOM_FX.includes(mainFx))mainFx=null;ctrlTarget="pitch";}else ctrlTarget=mainFx;}
  else if(BOTTOM_FX.includes(fx)){mainFx=mainFx===fx?null:fx;ctrlTarget=mainFx||(pitchOn?"pitch":null);}
  else{pitchOn=false;mainFx=mainFx===fx?null:fx;ctrlTarget=mainFx;}
  syncFxBtns();applyFxRealtime();
  const al=[...(pitchOn?["PITCH"]:[]),...(mainFx?[mainFx.toUpperCase()]:[])];hud.innerHTML=al.length?`<b>FX ON:</b> ${al.join(" + ")} · CTRL → <b>${ctrlTarget.toUpperCase()} (${Math.round(fxVals[ctrlTarget]*100)}%)</b>`:"<b>FX OFF</b>";
});
$("btn-hold").onclick=e=>{holdOn=!holdOn;e.currentTarget.classList.toggle("lit",holdOn);for(let b=0;b<NUM_BANKS;b++)for(let p=0;p<NUM_PADS;p++)if(banks[b][p].activeVoice)hotSwapVoice(b,p);};
$("btn-cancel").onclick=panicKillAll;

window.addEventListener("keydown",e=>{if((document.activeElement&&document.activeElement.tagName==="INPUT")||e.repeat)return;if(e.key>="1"&&e.key<="8")handlePadPress(+e.key-1);if(e.code==="Escape")panicKillAll();if(e.code==="Space"){e.preventDefault();isPlaying?stopTransport():startTransport();}});
window.addEventListener("keyup",e=>{if(document.activeElement&&document.activeElement.tagName==="INPUT")return;if(e.key>="1"&&e.key<="8"){const i=+e.key-1;if(banks[currentBank][i].gate&&!holdOn)stopPadVoice(currentBank,i);}});
window.addEventListener("resize",()=>requestAnimationFrame(()=>{drawSevenSegDisplay(displayedLedValue);drawSeqDisplays();renderAllWaveCanvases();}));

renderSampleTree();buildPatternButtons();buildSequencerGrid();buildMixerUI();buildArrangerUI();refreshAllBankUI();updateDynamicDisplay();syncPadVisuals();
requestAnimationFrame(()=>{drawSevenSegDisplay(bpm);drawSeqDisplays(0,0);renderAllWaveCanvases();});requestAnimationFrame(uiAnimLoop);

// HYBRID SONG TIMELINE + OPT-IN WARP + INTEGRATED LANE VU METERS
(()=>{
  const arrGrid=$("arr-grid");if(!arrGrid||$("hybrid-song-shell"))return;
  const TOTAL_BARS=64,TOTAL_STEPS=TOTAL_BARS*NUM_STEPS,NUM_LANES=8,LANE_H=52,HDR_W=94,VU_SEGS=8;
  if(!$("sp202-hybrid-song-css")){
    const st=document.createElement("style");st.id="sp202-hybrid-song-css";
    st.textContent=`#view-song.active.ht-fill-mode,#view-arr.active.ht-fill-mode{display:flex!important;flex-direction:column!important;height:100%!important;min-height:0!important}#view-song.ht-fill-mode #btn-arr-fill,#view-song.ht-fill-mode #btn-arr-clear,#view-arr.ht-fill-mode #btn-arr-fill,#view-arr.ht-fill-mode #btn-arr-clear{display:none!important}#hybrid-mode-bar{display:flex;flex-wrap:wrap;gap:5px;align-items:center;margin:0 0 6px;padding:5px 8px;background:#14161a;border:1px solid #2b3038;border-radius:3px;flex-shrink:0}#hybrid-mode-bar .h-btn{background:#232730;color:#cfd4dc;border:1px solid #3c4250;border-radius:2px;padding:4px 8px;font:700 10px "Courier New",monospace;cursor:pointer;letter-spacing:.4px}#hybrid-mode-bar .h-btn:hover{border-color:#e05a47}#hybrid-mode-bar .h-btn.active{background:#e05a47;color:#111;border-color:#ff7866}#hybrid-mode-bar .h-btn.cyan.active{background:#00d2ff;color:#081216;border-color:#7cebff}#hybrid-mode-bar .h-btn.amber.active{background:#ff9d47;color:#111;border-color:#ffbe7d}#hybrid-mode-bar .h-lbl{font:700 10px "Courier New",monospace;color:#8e96a4;min-width:36px;text-align:center}#hybrid-song-shell{display:none;flex:1 1 auto;min-height:240px;background:#121418;border:1px solid #2b3038;border-radius:3px;overflow:auto;position:relative;user-select:none;scrollbar-color:#3a404d #0e1014;scrollbar-width:thin}#hybrid-song-shell::-webkit-scrollbar{width:9px;height:9px}#hybrid-song-shell::-webkit-scrollbar-track{background:#0e1014}#hybrid-song-shell::-webkit-scrollbar-thumb{background:#343a46;border-radius:3px;border:2px solid #0e1014}#hybrid-song-shell::-webkit-scrollbar-thumb:hover{background:#e05a47}#hybrid-song-shell::-webkit-scrollbar-corner{background:#0e1014}#hybrid-song-shell.open{display:block}#ht-inner{position:relative;min-width:100%}.ht-top-sticky{position:sticky;top:0;z-index:8;background:#0c0e11}.ht-loop-row{display:flex;height:19px;background:#090b0e;border-bottom:1px solid #232730}.ht-loop-hdr{width:${HDR_W}px;flex-shrink:0;position:sticky;left:0;z-index:9;background:#121419;border-right:1px solid #2b3038;font:700 9px "Courier New",monospace;color:#ff9d47;display:flex;align-items:center;justify-content:center;letter-spacing:.8px}.ht-loop-gutter{position:relative;flex-shrink:0;height:100%;cursor:crosshair}.ht-loop-bar{position:absolute;top:2px;bottom:2px;background:rgba(255,157,71,.26);border:1px solid #ff9d47;border-radius:2px;cursor:grab;display:flex;align-items:center;justify-content:center;font:700 8px "Courier New",monospace;color:#ffd9b3;overflow:hidden;white-space:nowrap}.ht-loop-bar.auto{background:rgba(77,255,145,.18);border-color:#4dff91;color:#b8ffd2}.ht-loop-l,.ht-loop-r{position:absolute;top:0;bottom:0;width:7px;cursor:ew-resize;background:rgba(255,255,255,.18)}.ht-loop-l{left:0}.ht-loop-r{right:0}.ht-ruler-row{display:flex;height:22px;background:#0c0e11;border-bottom:1px solid #2b3038}.ht-ruler-hdr{width:${HDR_W}px;flex-shrink:0;position:sticky;left:0;z-index:9;background:#14171d;border-right:1px solid #2b3038;font:700 9px "Courier New",monospace;color:#6d7482;display:flex;align-items:center;justify-content:center}.ht-ruler{display:flex;flex-shrink:0;cursor:pointer}.ht-bar{flex-shrink:0;border-left:1px solid #485060;padding:4px 5px;font:700 10px "Courier New",monospace;color:#ff9d47;overflow:hidden;white-space:nowrap}.ht-bar:hover{background:rgba(255,157,71,.08)}#ht-lanes{position:relative}.ht-lane{display:flex;height:${LANE_H}px;border-bottom:1px solid #232730}.ht-lane.muted{opacity:.42}.ht-lane-hdr{width:${HDR_W}px;flex-shrink:0;position:sticky;left:0;z-index:5;background:#171a20;border-right:1px solid #2b3038;padding:4px 4px 4px 6px;font:700 10px "Courier New",monospace;color:#9aa1ae;display:flex;flex-direction:row;align-items:center;justify-content:space-between;gap:4px}.ht-hdr-left{display:flex;flex-direction:column;justify-content:space-between;height:100%;min-width:0}.ht-lane-btns{display:flex;gap:3px}.ht-ms{background:#232730;color:#8e96a4;border:1px solid #353b47;border-radius:2px;font:700 9px "Courier New",monospace;padding:1px 5px;cursor:pointer}.ht-ms.m-on{background:#e05a47;color:#111;border-color:#ff7866}.ht-ms.s-on{background:#ff9d47;color:#111;border-color:#ffc185}.ht-lane-vu{width:8px;height:42px;flex-shrink:0;background:#090b0e;border:1px solid #262a33;border-radius:2px;padding:1px;display:flex;flex-direction:column-reverse;gap:1px;box-shadow:inset 0 1px 3px rgba(0,0,0,.9)}.ht-vu-seg{flex:1;border-radius:1px;background:#1a1e24;transition:background .04s linear}.ht-vu-seg.on-g{background:#34e87a;box-shadow:0 0 4px rgba(52,232,122,.7)}.ht-vu-seg.on-y{background:#ffb02e;box-shadow:0 0 4px rgba(255,176,46,.75)}.ht-vu-seg.on-r{background:#ff2e44;box-shadow:0 0 5px rgba(255,46,68,.9)}.ht-canvas{position:relative;flex-shrink:0;background-color:#15181d}.ht-clip{position:absolute;top:4px;height:44px;box-sizing:border-box;border-radius:2px;padding:0;cursor:move;overflow:hidden;display:flex;flex-direction:column;justify-content:space-between;font:700 9px "Courier New",monospace}.ht-clip.wave{background:rgba(0,210,255,.12);box-shadow:inset 0 0 0 1px #00d2ff;color:#baf2ff}.ht-clip.seq{background:rgba(255,59,59,.16);box-shadow:inset 0 0 0 1px #ff4a3d;color:#ffd0cc}.ht-clip.selected{outline:1.5px dashed #fff;outline-offset:-1px;box-shadow:0 0 10px rgba(255,255,255,.35);z-index:4}.ht-clip-lbl{padding:2px 10px 0 4px;line-height:13px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;pointer-events:none}.ht-vis{height:26px;width:100%;display:flex;align-items:center;pointer-events:none;overflow:hidden}.ht-wave-cv{display:block;width:100%;height:26px}.ht-spip{flex:none;height:14px;box-sizing:border-box;background:rgba(255,74,61,.12);border-right:1px solid rgba(0,0,0,.45)}.ht-spip.beat{background:rgba(255,74,61,.2)}.ht-spip.rep{border-left:1.5px solid rgba(255,157,71,.75)}.ht-spip.on{background:#ff3b3b;box-shadow:inset 0 0 4px rgba(255,230,210,.55)}.ht-resize{position:absolute;right:0;top:0;width:8px;height:100%;cursor:ew-resize;z-index:3}.ht-resize:hover{background:rgba(255,157,71,.45);border-left:1px solid #ff9d47}#ht-marquee{display:none;position:absolute;border:1.5px dashed #ff9d47;background:rgba(255,157,71,.12);pointer-events:none;z-index:12}#ht-playhead{position:absolute;top:0;bottom:0;left:${HDR_W}px;width:2px;background:#ff2638;box-shadow:0 0 8px #ff2638;pointer-events:none;z-index:11}`;
    document.head.appendChild(st);
  }

  let timelineActive=false,timelineWarp=false,toolMode="DRAG",snapSteps=4,stepPx=14,tlStep=0,loopAuto=true,loopStart=0,loopEnd=32,nextClipId=3,clipboard=[];
  let laneState=Array.from({length:NUM_LANES},()=>({mute:false,solo:false}));
  const selectedIds=new Set(),undoStack=[],activeWaveSources=new Set(),lanePeaks=new Float32Array(NUM_LANES),vuBuf=new Uint8Array(256);
  let laneMeterSegs=Array.from({length:NUM_LANES},()=>[]);
  let clips=[{id:1,lane:0,kind:"seq",pat:0,bank:0,startStep:0,lengthSteps:16,label:"SEQ P1 (A)"},{id:2,lane:0,kind:"seq",pat:0,bank:0,startStep:16,lengthSteps:16,label:"SEQ P1 (A)"}];
  const stopTimelineWaves=()=>{activeWaveSources.forEach(s=>{try{s.stop();}catch{}});activeWaveSources.clear();};
  const kickLaneVU=(lane,lvl,time)=>{const ms=ac&&typeof time==="number"?Math.max(0,(time-ac.currentTime)*1e3):0;setTimeout(()=>{if(lvl>lanePeaks[lane])lanePeaks[lane]=lvl;},ms);};

  function triggerTimelineWave(clip,time){
    initAudio();if(ac.state==="suspended")ac.resume();const pad=banks[clip.bank]?.[clip.pad],buf=pad?getProcessedBuffer(pad):null;if(!buf)return;
    const td=buf.duration,fS=pad.startNorm*td;let fE=pad.endNorm*td;if(fE-fS<.01)fE=Math.min(td,fS+.01);
    const sSec=pad.reverse?Math.max(0,td-fE):fS,eSec=pad.reverse?Math.min(td,td-fS):fE,segD=Math.max(.01,eSec-sSec),tDur=Math.max(.02,clip.lengthSteps*(60/bpm/4));
    const rate=timelineWarp?Math.max(.25,Math.min(4,segD/tDur)):getEffectivePadRate(pad);
    const playDur=timelineWarp?tDur:Math.min(segD/rate,tDur);
    const src=ac.createBufferSource();src.buffer=buf;src.playbackRate.setValueAtTime(rate,time);
    const mg=ac.createGain();mg.channelCount=pad.stereo?2:1;mg.channelCountMode=pad.stereo?"max":"explicit";
    mg.gain.setValueAtTime(.9,time);mg.gain.setValueAtTime(.9,time+Math.max(.01,playDur-.008));mg.gain.linearRampToValueAtTime(.0001,time+playDur);
    src.connect(mg);mg.connect(pad.gainNode);activeWaveSources.add(src);src.onended=()=>activeWaveSources.delete(src);
    src.start(time,sSec,segD);src.stop(time+playDur+.005);
    kickLaneVU(clip.lane,Math.min(1,.9*(pad.vol??.85)),time);
  }

  const pushUndo=()=>{undoStack.push(structuredClone(clips));if(undoStack.length>40)undoStack.shift();};
  const performUndo=()=>{if(!undoStack.length){hud.innerHTML="TIMELINE: NOTHING TO UNDO";return;}clips=undoStack.pop();selectedIds.clear();renderTimeline();hud.innerHTML=`TIMELINE: <b>UNDO</b> (${undoStack.length} LEFT)`;};
  const copySel=()=>{if(!selectedIds.size)return;clipboard=clips.filter(c=>selectedIds.has(c.id)).map(c=>structuredClone(c));hud.innerHTML=`TIMELINE: COPIED <b>${clipboard.length}</b> CLIP(S)`;};
  const cutSel=()=>{if(!selectedIds.size)return;pushUndo();clipboard=clips.filter(c=>selectedIds.has(c.id)).map(c=>structuredClone(c));clips=clips.filter(c=>!selectedIds.has(c.id));selectedIds.clear();renderTimeline();hud.innerHTML=`TIMELINE: CUT <b>${clipboard.length}</b> CLIP(S)`;};
  const pasteSel=()=>{if(!clipboard.length)return;pushUndo();const ms=Math.min(...clipboard.map(c=>c.startStep));selectedIds.clear();clipboard.forEach(s=>{const ns=Math.min(TOTAL_STEPS-snapSteps,tlStep+(s.startStep-ms)),nc={...structuredClone(s),id:nextClipId++,startStep:ns,lengthSteps:Math.min(s.lengthSteps,TOTAL_STEPS-ns)};clips.push(nc);selectedIds.add(nc.id);});renderTimeline();hud.innerHTML=`TIMELINE: PASTED <b>${clipboard.length}</b> CLIP(S)`;};
  const dupSel=()=>{if(!selectedIds.size)return;pushUndo();const grp=clips.filter(c=>selectedIds.has(c.id)),minS=Math.min(...grp.map(c=>c.startStep)),maxE=Math.max(...grp.map(c=>c.startStep+c.lengthSteps)),shift=maxE-minS;selectedIds.clear();grp.forEach(c=>{const ns=Math.min(TOTAL_STEPS-snapSteps,c.startStep+shift),nc={...structuredClone(c),id:nextClipId++,startStep:ns,lengthSteps:Math.min(c.lengthSteps,TOTAL_STEPS-ns)};clips.push(nc);selectedIds.add(nc.id);});renderTimeline();};
  const delSel=()=>{if(!selectedIds.size)return;pushUndo();clips=clips.filter(c=>!selectedIds.has(c.id));selectedIds.clear();renderTimeline();};
  const selAll=()=>{selectedIds.clear();clips.forEach(c=>selectedIds.add(c.id));renderTimeline();};
  const clearClips=()=>{if(!clips.length)return;pushUndo();clips=[];selectedIds.clear();renderTimeline();};
  const snap=s=>Math.max(0,Math.min(TOTAL_STEPS-snapSteps,Math.round(s/snapSteps)*snapSteps)),snapEnd=s=>Math.max(snapSteps,Math.min(TOTAL_STEPS,Math.round(s/snapSteps)*snapSteps));
  const getLoopBounds=()=>loopAuto?{start:0,end:Math.max(NUM_STEPS,Math.min(TOTAL_STEPS,clips.length?Math.max(...clips.map(c=>c.startStep+c.lengthSteps)):NUM_STEPS))}:{start:loopStart,end:Math.max(loopStart+snapSteps,loopEnd)};

  function drawRealClipWaveform(cv,bIdx,pIdx,cssW){
    const h=26,w=Math.max(4,Math.round(cssW)),dpr=window.devicePixelRatio||1;cv.width=Math.floor(w*dpr);cv.height=Math.floor(h*dpr);
    const ctx=cv.getContext("2d");ctx.setTransform(dpr,0,0,dpr,0,0);ctx.clearRect(0,0,w,h);ctx.strokeStyle="rgba(0,210,255,.22)";ctx.lineWidth=1;ctx.beginPath();ctx.moveTo(0,h/2);ctx.lineTo(w,h/2);ctx.stroke();
    const pad=banks[bIdx]?.[pIdx],disp=pad?(getDisplayBuffer(pad)||pad.buffer):null;if(!disp)return;
    const data=disp.getChannelData(0),sI=Math.max(0,Math.min(data.length-1,Math.floor(pad.startNorm*data.length))),eI=Math.max(sI+1,Math.min(data.length,Math.ceil(pad.endNorm*data.length))),sp=eI-sI,spp=sp/w,st=Math.max(1,Math.floor(spp/24));
    ctx.strokeStyle="#00e5ff";ctx.lineWidth=1;ctx.beginPath();
    for(let x=0;x<w;x++){const p0=Math.floor(x*spp),p1=Math.max(p0+1,Math.floor((x+1)*spp));let mn=1,mx=-1;for(let k=p0;k<p1&&k<sp;k+=st){const v=data[pad.reverse?(eI-1-k):(sI+k)];if(v<mn)mn=v;if(v>mx)mx=v;}if(mn>mx){mn=0;mx=0;}const yT=(1-mx)*.46*h+h*.04,yB=(1-mn)*.46*h+h*.04;ctx.moveTo(x+.5,yT);ctx.lineTo(x+.5,Math.max(yT+1,yB));}
    ctx.stroke();
  }
  const getPadDefaultSteps=pad=>(!pad||!pad.buffer)?16:Math.max(snapSteps,Math.min(64,Math.round(Math.round(((pad.endNorm-pad.startNorm)*pad.buffer.duration/Math.max(.25,pad.pitch))/(60/bpm/4))/snapSteps)*snapSteps||snapSteps));

  const bar=document.createElement("div");bar.id="hybrid-mode-bar";
  bar.innerHTML=`<button class="h-btn active" id="ht-mode-grid">CLASSIC</button><button class="h-btn" id="ht-mode-tl">TIMELINE</button><span style="width:1px;height:16px;background:#2b3038"></span><button class="h-btn active" id="ht-tool-drag">SELECT</button><button class="h-btn cyan" id="ht-tool-pad">PAD [A1]</button><button class="h-btn" id="ht-tool-seq">SEQ [P1]</button><button class="h-btn" id="ht-snap">SNAP: 1/4B</button><button class="h-btn amber active" id="ht-loop-auto">LOOP: AUTO</button><button class="h-btn cyan" id="ht-warp-btn" title="Opt-in: Stretch blue PAD clips to grid width (OFF respects Pad Pitch)">WARP: OFF</button><span style="width:1px;height:16px;background:#2b3038"></span><button class="h-btn" id="ht-undo">UNDO</button><button class="h-btn" id="ht-zoom-out">-</button><span class="h-lbl" id="ht-zoom-lbl">100%</span><button class="h-btn" id="ht-zoom-in">+</button><button class="h-btn" id="ht-clear">CLR</button>`;
  const shell=document.createElement("div");shell.id="hybrid-song-shell";
  shell.innerHTML=`<div id="ht-inner"><div id="ht-playhead"></div><div class="ht-top-sticky"><div class="ht-loop-row"><div class="ht-loop-hdr">LOOP</div><div class="ht-loop-gutter" id="ht-loop-gutter"></div></div><div class="ht-ruler-row"><div class="ht-ruler-hdr">SEEK BAR</div><div class="ht-ruler" id="ht-ruler"></div></div></div><div id="ht-lanes"></div><div id="ht-marquee"></div></div>`;
  arrGrid.parentNode.insertBefore(bar,arrGrid);arrGrid.parentNode.insertBefore(shell,arrGrid);

  const syncWarpUI=()=>{const wb=$("ht-warp-btn");if(wb){wb.classList.toggle("active",timelineWarp);wb.textContent=`WARP: ${timelineWarp?"ON":"OFF"}`;}const mb=$("mb-opt-warp");if(mb)mb.textContent=`TIMELINE WARP-TO-GRID: ${timelineWarp?"ON":"OFF"}`;};
  const setWarp=v=>{timelineWarp=!!v;syncWarpUI();hud.innerHTML=`TIMELINE WARP-TO-GRID: <b>${timelineWarp?"ON (STRETCH TO CLIP)":"OFF (RESPECTS PAD PITCH)"}</b>`;};
  const updateBrushLabels=()=>{const pb=$("ht-tool-pad"),sb=$("ht-tool-seq");if(pb)pb.textContent=`PAD [${BANK_NAMES[currentBank]}${selectedPad+1}]`;if(sb)sb.textContent=`SEQ [P${currentPat+1}]`;};
  window.addEventListener("click",updateBrushLabels);window.addEventListener("keydown",updateBrushLabels);
  document.querySelectorAll('[data-tab="song"],[data-tab="arr"]').forEach(b=>b.addEventListener("click",()=>{if(timelineActive)requestAnimationFrame(renderTimeline);}));

  function setZoom(np,cx=null){const op=stepPx;stepPx=Math.max(3,Math.min(32,np));if(stepPx===op)return;const r=shell.getBoundingClientRect(),ax=cx!==null?(cx-r.left-HDR_W):(shell.clientWidth-HDR_W)/2,sa=(shell.scrollLeft+Math.max(0,ax))/op;$("ht-zoom-lbl").textContent=`${Math.round(stepPx/14*100)}%`;renderTimeline();shell.scrollLeft=Math.max(0,sa*stepPx-Math.max(0,ax));}
  function renderLoopGutter(totalW){
    const g=$("ht-loop-gutter");g.style.width=`${totalW}px`;g.innerHTML="";const lb=getLoopBounds(),lBar=document.createElement("div");
    lBar.className=`ht-loop-bar ${loopAuto?"auto":""}`;lBar.style.left=`${lb.start*stepPx}px`;lBar.style.width=`${Math.max(12,(lb.end-lb.start)*stepPx)}px`;
    lBar.innerHTML=`<div class="ht-loop-l"></div><span>${loopAuto?"AUTO":"LOOP"} (${((lb.end-lb.start)/16).toFixed(1)}B)</span><div class="ht-loop-r"></div>`;
    lBar.onmousedown=e=>{e.stopPropagation();const isL=e.target.classList.contains("ht-loop-l"),isR=e.target.classList.contains("ht-loop-r"),sx=e.clientX,oS=lb.start,oE=lb.end,sp=oE-oS;loopAuto=false;$("ht-loop-auto").classList.remove("active");$("ht-loop-auto").textContent="LOOP: CUSTOM";const mv=ev=>{const ds=Math.round((ev.clientX-sx)/stepPx);if(isL){loopStart=Math.max(0,Math.min(oE-snapSteps,snap(oS+ds)));loopEnd=oE;}else if(isR){loopStart=oS;loopEnd=Math.max(oS+snapSteps,snapEnd(oE+ds));}else{const ns=Math.max(0,Math.min(TOTAL_STEPS-sp,snap(oS+ds)));loopStart=ns;loopEnd=ns+sp;}renderLoopGutter(totalW);},up=()=>{window.removeEventListener("mousemove",mv);window.removeEventListener("mouseup",up);};window.addEventListener("mousemove",mv);window.addEventListener("mouseup",up);};
    g.onmousedown=e=>{if(e.target!==g)return;const r=g.getBoundingClientRect(),s0=snap(Math.floor((e.clientX-r.left)/stepPx));loopAuto=false;loopStart=s0;loopEnd=Math.min(TOTAL_STEPS,s0+snapSteps);$("ht-loop-auto").classList.remove("active");$("ht-loop-auto").textContent="LOOP: CUSTOM";renderLoopGutter(totalW);const mv=ev=>{const cur=snapEnd(Math.ceil((ev.clientX-r.left)/stepPx));if(cur>=s0){loopStart=s0;loopEnd=Math.max(s0+snapSteps,cur);}else{loopStart=Math.max(0,snap(Math.floor((ev.clientX-r.left)/stepPx)));loopEnd=Math.max(loopStart+snapSteps,s0);}renderLoopGutter(totalW);},up=()=>{window.removeEventListener("mousemove",mv);window.removeEventListener("mouseup",up);};window.addEventListener("mousemove",mv);window.addEventListener("mouseup",up);};
    g.ondblclick=()=>{loopAuto=true;$("ht-loop-auto").classList.add("active");$("ht-loop-auto").textContent="LOOP: AUTO";renderLoopGutter(totalW);};g.appendChild(lBar);
  }
  function startMarquee(e){
    const ir=$("ht-inner").getBoundingClientRect(),lr=$("ht-lanes").getBoundingClientRect(),mq=$("ht-marquee"),sx=e.clientX,sy=e.clientY;
    if(!e.shiftKey)selectedIds.clear();mq.style.display="block";
    const ub=ev=>{const x1=Math.min(sx,ev.clientX),y1=Math.min(sy,ev.clientY),x2=Math.max(sx,ev.clientX),y2=Math.max(sy,ev.clientY);mq.style.left=`${x1-ir.left}px`;mq.style.top=`${y1-ir.top}px`;mq.style.width=`${x2-x1}px`;mq.style.height=`${y2-y1}px`;const gx1=x1-lr.left-HDR_W,gx2=x2-lr.left-HDR_W,gy1=y1-lr.top,gy2=y2-lr.top;if(!e.shiftKey)selectedIds.clear();clips.forEach(c=>{const cx1=c.startStep*stepPx,cx2=(c.startStep+c.lengthSteps)*stepPx,cy1=c.lane*LANE_H+4,cy2=c.lane*LANE_H+48;if(cx1<gx2&&cx2>gx1&&cy1<gy2&&cy2>gy1)selectedIds.add(c.id);});document.querySelectorAll(".ht-clip").forEach(el=>el.classList.toggle("selected",selectedIds.has(+el.dataset.cid)));};
    ub(e);const up=()=>{mq.style.display="none";window.removeEventListener("mousemove",ub);window.removeEventListener("mouseup",up);};window.addEventListener("mousemove",ub);window.addEventListener("mouseup",up);
  }

  function renderTimeline(){
    updateBrushLabels();const totalW=TOTAL_STEPS*stepPx,barW=NUM_STEPS*stepPx,beatW=4*stepPx;$("ht-inner").style.width=`${HDR_W+totalW}px`;renderLoopGutter(totalW);
    const ruler=$("ht-ruler");ruler.style.width=`${totalW}px`;ruler.innerHTML="";
    for(let b=0;b<TOTAL_BARS;b++){const bm=document.createElement("div");bm.className="ht-bar";bm.style.width=`${barW}px`;bm.textContent=barW>=54?`BAR ${b+1}`:`${b+1}`;ruler.appendChild(bm);}
    ruler.onmousedown=e=>{const r=ruler.getBoundingClientRect();tlStep=snap(Math.floor((e.clientX-r.left)/stepPx));if($("ht-playhead"))$("ht-playhead").style.left=`${HDR_W+tlStep*stepPx}px`;updatePlayheadUI(tlStep%NUM_STEPS,Math.floor(tlStep/NUM_STEPS));};
    const lanesEl=$("ht-lanes");lanesEl.innerHTML="";laneMeterSegs=Array.from({length:NUM_LANES},()=>[]);
    const anySolo=laneState.some(ls=>ls.solo);
    const gBg=stepPx>=8?`linear-gradient(to right,rgba(255,255,255,.14) 1px,transparent 1px),linear-gradient(to right,rgba(255,255,255,.05) 1px,transparent 1px),linear-gradient(to right,rgba(255,255,255,.02) 1px,transparent 1px)`:`linear-gradient(to right,rgba(255,255,255,.14) 1px,transparent 1px),linear-gradient(to right,rgba(255,255,255,.04) 1px,transparent 1px)`;
    const gSz=stepPx>=8?`${barW}px 100%,${beatW}px 100%,${stepPx}px 100%`:`${barW}px 100%,${beatW}px 100%`;

    for(let l=0;l<NUM_LANES;l++){
      const ls=laneState[l],isM=anySolo?!ls.solo:ls.mute,row=document.createElement("div");row.className=`ht-lane ${isM?"muted":""}`;
      const hdr=document.createElement("div");hdr.className="ht-lane-hdr";
      hdr.innerHTML=`<div class="ht-hdr-left"><span>LANE 0${l+1}</span><div class="ht-lane-btns"><button class="ht-ms ${ls.mute?"m-on":""}">M</button><button class="ht-ms ${ls.solo?"s-on":""}">S</button></div></div><div class="ht-lane-vu"></div>`;
      const [mB,sB]=hdr.querySelectorAll(".ht-ms");mB.onclick=()=>{ls.mute=!ls.mute;renderTimeline();};sB.onclick=()=>{ls.solo=!ls.solo;renderTimeline();};
      const vu=hdr.querySelector(".ht-lane-vu");for(let s=0;s<VU_SEGS;s++){const d=document.createElement("div");d.className="ht-vu-seg";vu.appendChild(d);laneMeterSegs[l].push(d);}
      row.appendChild(hdr);

      const cv=document.createElement("div");cv.className="ht-canvas";cv.style.width=`${totalW}px`;cv.style.backgroundImage=gBg;cv.style.backgroundSize=gSz;
      cv.onmousedown=e=>{
        if(e.button!==0||e.target!==cv)return;if(toolMode==="DRAG"){startMarquee(e);return;}pushUndo();
        const r=cv.getBoundingClientRect(),st=snap(Math.floor((e.clientX-r.left)/stepPx));
        const nc=toolMode==="PAINT_PAD"?{id:nextClipId++,lane:l,kind:"wave",bank:currentBank,pad:selectedPad,startStep:st,lengthSteps:Math.min(getPadDefaultSteps(banks[currentBank][selectedPad]),TOTAL_STEPS-st),label:`${BANK_NAMES[currentBank]}${selectedPad+1} ${banks[currentBank][selectedPad].name.slice(0,12)}`}:{id:nextClipId++,lane:l,kind:"seq",pat:currentPat,bank:currentBank,startStep:st,lengthSteps:Math.min(16,TOTAL_STEPS-st),label:`SEQ P${currentPat+1} (${BANK_NAMES[currentBank]})`};
        clips.push(nc);selectedIds.clear();selectedIds.add(nc.id);renderTimeline();
      };

      clips.filter(c=>c.lane===l).forEach(clip=>{
        const el=document.createElement("div"),cW=clip.lengthSteps*stepPx;
        el.className=`ht-clip ${clip.kind} ${selectedIds.has(clip.id)?"selected":""}`;el.dataset.cid=clip.id;el.style.left=`${clip.startStep*stepPx}px`;el.style.width=`${cW}px`;
        const lbl=clip.kind==="wave"?`${BANK_NAMES[clip.bank]}${clip.pad+1} ${(banks[clip.bank]?.[clip.pad]?.name||"").slice(0,12)}`:clip.label;
        el.innerHTML=`<div class="ht-clip-lbl">${lbl}</div><div class="ht-vis"></div><div class="ht-resize"></div>`;
        const vis=el.querySelector(".ht-vis");
        if(clip.kind==="wave"){const wCv=document.createElement("canvas");wCv.className="ht-wave-cv";vis.appendChild(wCv);drawRealClipWaveform(wCv,clip.bank,clip.pad,cW);}
        else if(stepPx>=4){const pg=patterns[clip.pat][clip.bank];for(let s=0;s<clip.lengthSteps;s++){const pip=document.createElement("div");pip.className=`ht-spip${pg.some(pr=>pr[s%NUM_STEPS]>0)?" on":""}${s%4===0?" beat":""}${s>0&&s%NUM_STEPS===0?" rep":""}`;pip.style.width=`${stepPx}px`;vis.appendChild(pip);}}
        el.oncontextmenu=e=>{e.preventDefault();pushUndo();clips=clips.filter(c=>c.id!==clip.id);selectedIds.delete(clip.id);renderTimeline();};
        el.onmousedown=e=>{
          if(e.button!==0)return;e.stopPropagation();const isR=e.target.classList.contains("ht-resize");
          if(e.shiftKey&&!isR)selectedIds.has(clip.id)?selectedIds.delete(clip.id):selectedIds.add(clip.id);else if(!selectedIds.has(clip.id)){selectedIds.clear();selectedIds.add(clip.id);}
          renderTimeline();const sx=e.clientX,sy=e.clientY;let moved=false,grp=clips.filter(c=>selectedIds.has(c.id)),orig=grp.map(c=>({c,s:c.startStep,l:c.lane,len:c.lengthSteps}));
          const mv=ev=>{
            const ds=Math.round((ev.clientX-sx)/stepPx),dl=Math.round((ev.clientY-sy)/LANE_H);
            if(!moved&&(ds!==0||(!isR&&dl!==0))){moved=true;pushUndo();if(!isR&&ev.altKey){const cl=grp.map(c=>({...structuredClone(c),id:nextClipId++}));clips.push(...cl);selectedIds.clear();cl.forEach(x=>selectedIds.add(x.id));grp=cl;orig=grp.map(c=>({c,s:c.startStep,l:c.lane,len:c.lengthSteps}));}}
            if(!moved)return;
            if(isR){const t=orig.find(o=>o.c.id===clip.id)||orig[0];t.c.lengthSteps=Math.max(snapSteps,Math.min(TOTAL_STEPS-t.c.startStep,Math.round((t.len+ds)/snapSteps)*snapSteps));}
            else{const cDs=Math.max(-Math.min(...orig.map(o=>o.s)),Math.min(TOTAL_STEPS-Math.max(...orig.map(o=>o.s+o.len)),Math.round(ds/snapSteps)*snapSteps)),cDl=Math.max(-Math.min(...orig.map(o=>o.l)),Math.min(NUM_LANES-1-Math.max(...orig.map(o=>o.l)),dl));orig.forEach(o=>{o.c.startStep=o.s+cDs;o.c.lane=o.l+cDl;});}
            renderTimeline();
          },up=()=>{window.removeEventListener("mousemove",mv);window.removeEventListener("mouseup",up);};
          window.addEventListener("mousemove",mv);window.addEventListener("mouseup",up);
        };
        cv.appendChild(el);
      });
      row.appendChild(cv);lanesEl.appendChild(row);
    }
    if($("ht-playhead"))$("ht-playhead").style.left=`${HDR_W+tlStep*stepPx}px`;
  }

  window.addEventListener("keydown",e=>{
    if(!timelineActive||(document.activeElement&&document.activeElement.tagName==="INPUT"))return;
    const ctrl=e.ctrlKey||e.metaKey,k=e.key.toLowerCase();
    if(ctrl&&k==="z"){e.preventDefault();performUndo();}
    else if(ctrl&&k==="c"){e.preventDefault();copySel();}
    else if(ctrl&&k==="x"){e.preventDefault();cutSel();}
    else if(ctrl&&k==="v"){e.preventDefault();pasteSel();}
    else if(ctrl&&k==="d"){e.preventDefault();dupSel();}
    else if(ctrl&&k==="a"){e.preventDefault();selAll();}
    else if((e.key==="Delete"||e.key==="Backspace")&&selectedIds.size){e.preventDefault();delSel();}
  });

  const setTool=m=>{toolMode=m;$("ht-tool-drag").classList.toggle("active",m==="DRAG");$("ht-tool-pad").classList.toggle("active",m==="PAINT_PAD");$("ht-tool-seq").classList.toggle("active",m==="PAINT_SEQ");};
  const songView=$("view-song")||$("view-arr");
  const setTimelineMode=on=>{timelineActive=!!on;arrGrid.style.display=on?"none":"";shell.classList.toggle("open",on);if(songView)songView.classList.toggle("ht-fill-mode",on);$("ht-mode-tl").classList.toggle("active",on);$("ht-mode-grid").classList.toggle("active",!on);if(on)renderTimeline();};
  $("ht-mode-grid").onclick=()=>setTimelineMode(false);$("ht-mode-tl").onclick=()=>setTimelineMode(true);
  $("ht-tool-drag").onclick=()=>setTool("DRAG");$("ht-tool-pad").onclick=()=>setTool("PAINT_PAD");$("ht-tool-seq").onclick=()=>setTool("PAINT_SEQ");
  $("ht-snap").onclick=e=>{const v=[1,4,16],l=["1/16","1/4B","1 BAR"],ni=(v.indexOf(snapSteps)+1)%3;snapSteps=v[ni];e.target.textContent=`SNAP: ${l[ni]}`;};
  $("ht-loop-auto").onclick=e=>{loopAuto=true;e.target.classList.add("active");e.target.textContent="LOOP: AUTO";renderTimeline();};
  $("ht-warp-btn").onclick=()=>setWarp(!timelineWarp);
  $("ht-undo").onclick=performUndo;$("ht-zoom-in").onclick=()=>setZoom(stepPx+3);$("ht-zoom-out").onclick=()=>setZoom(stepPx-3);$("ht-clear").onclick=clearClips;
  shell.addEventListener("wheel",e=>{if(e.shiftKey)return;e.preventDefault();setZoom(stepPx+(e.deltaY<0?2:-2),e.clientX);},{passive:false});
  const resetPH=()=>{stopTimelineWaves();tlStep=getLoopBounds().start;if($("ht-playhead"))$("ht-playhead").style.left=`${HDR_W+tlStep*stepPx}px`;};
  $("btn-stop").addEventListener("click",resetPH);$("btn-cancel").addEventListener("click",resetPH);

  htApi={
    undo:performUndo,cut:cutSel,copy:copySel,paste:pasteSel,dup:dupSel,del:delSel,selAll,clear:clearClips,
    toggleMode:()=>setTimelineMode(!timelineActive),setMode:setTimelineMode,
    setLoopAuto:()=>{loopAuto=true;$("ht-loop-auto").classList.add("active");$("ht-loop-auto").textContent="LOOP: AUTO";renderTimeline();},
    toggleWarp:()=>setWarp(!timelineWarp),setWarp,getWarp:()=>timelineWarp,
    getState:()=>({timelineActive,timelineWarp,snapSteps,loopAuto,loopStart,loopEnd,laneState:structuredClone(laneState),clips:structuredClone(clips)}),
    setState:st=>{
      if(!st)return;
      if(Array.isArray(st.clips)){clips=structuredClone(st.clips);nextClipId=clips.reduce((m,c)=>Math.max(m,c.id||0),0)+1;}
      if(Array.isArray(st.laneState)&&st.laneState.length===NUM_LANES)laneState=structuredClone(st.laneState);
      loopAuto=st.loopAuto!==undefined?!!st.loopAuto:true;loopStart=st.loopStart||0;loopEnd=st.loopEnd||32;
      if(st.snapSteps)snapSteps=st.snapSteps;
      $("ht-loop-auto").classList.toggle("active",loopAuto);$("ht-loop-auto").textContent=loopAuto?"LOOP: AUTO":"LOOP: CUSTOM";
      setWarp(!!st.timelineWarp);setTimelineMode(!!st.timelineActive);selectedIds.clear();renderTimeline();
    }
  };

  const _origScheduleStep=scheduleStep;
  scheduleStep=function(step,bar,time){
    if(playMode!=="song"||!timelineActive)return _origScheduleStep(step,bar,time);
    const lb=getLoopBounds();if(tlStep<lb.start||tlStep>=lb.end)tlStep=lb.start;const gStep=tlStep;tlStep=(tlStep+1>=lb.end)?lb.start:tlStep+1;
    const anySolo=laneState.some(ls=>ls.solo);
    clips.forEach(c=>{
      const ls=laneState[c.lane];if(!ls||(anySolo?!ls.solo:ls.mute))return;
      if(c.kind==="wave"&&c.startStep===gStep)triggerTimelineWave(c,time);
      else if(c.kind==="seq"&&gStep>=c.startStep&&gStep<c.startStep+c.lengthSteps){
        const lStep=(gStep-c.startStep)%NUM_STEPS,pat=patterns[c.pat][c.bank];
        for(let p=0;p<NUM_PADS;p++){const v=pat[p][lStep];if(v>0){triggerPad(c.bank,p,time,true,null,v);if(banks[c.bank][p].buffer)kickLaneVU(c.lane,Math.min(1,v*(banks[c.bank][p].vol??.85)),time);}}
      }
    });
    setTimeout(()=>{if(!isPlaying)return;updatePlayheadUI(gStep%NUM_STEPS,Math.floor(gStep/NUM_STEPS));if($("ht-playhead"))$("ht-playhead").style.left=`${HDR_W+gStep*stepPx}px`;},Math.max(0,(time-ac.currentTime)*1e3));
  };

  function tickLaneVUs(){
    if(shell.classList.contains("open")&&shell.offsetParent!==null){
      const anySolo=laneState.some(ls=>ls.solo);
      for(let l=0;l<NUM_LANES;l++){
        const segs=laneMeterSegs[l];if(!segs.length)continue;
        let pk=0;
        if(ac&&!(anySolo?!laneState[l].solo:laneState[l].mute)){
          const seen=new Set();
          for(const c of clips){
            if(c.lane!==l)continue;
            const pads=c.kind==="wave"?[c.pad]:[0,1,2,3,4,5,6,7];
            for(const p of pads){
              const key=`${c.bank}:${p}`;if(seen.has(key))continue;seen.add(key);
              const an=banks[c.bank]?.[p]?.analyser;if(!an)continue;
              an.getByteTimeDomainData(vuBuf);
              for(let k=0;k<vuBuf.length;k+=2){const v=Math.abs(vuBuf[k]-128)/128;if(v>pk)pk=v;}
            }
          }
        }
        lanePeaks[l]=pk>lanePeaks[l]?pk:Math.max(0,lanePeaks[l]*.86);
        const lit=Math.min(VU_SEGS,Math.round(lanePeaks[l]*9));
        for(let s=0;s<VU_SEGS;s++)segs[s].className=s<lit?(s>=7?"ht-vu-seg on-r":s>=5?"ht-vu-seg on-y":"ht-vu-seg on-g"):"ht-vu-seg";
      }
    }
    requestAnimationFrame(tickLaneVUs);
  }
  requestAnimationFrame(tickLaneVUs);
})();

// TOP MENUBAR (FILE / EDIT / OPTIONS) + PROJECT SAVE/LOAD
(()=>{
  if($("sp202-menubar"))return;
  const st=document.createElement("style");st.id="sp202-menubar-css";
  st.textContent=`#sp202-menubar{position:sticky;top:0;z-index:9000;display:flex;align-items:center;gap:2px;height:26px;padding:0 8px;background:#121418;border-bottom:1px solid #2b3038;font:700 10px "Courier New",monospace;color:#cfd4dc;user-select:none}.mb-wrap{position:relative}.mb-btn{background:transparent;border:1px solid transparent;color:#cfd4dc;padding:3px 9px;font:700 10px "Courier New",monospace;letter-spacing:.6px;cursor:pointer}.mb-btn:hover,.mb-wrap.open .mb-btn{background:#232730;border-color:#3a404d;color:#fff}.mb-drop{display:none;position:absolute;top:100%;left:0;min-width:225px;background:#16191f;border:1px solid #353b47;box-shadow:0 6px 18px rgba(0,0,0,.85);padding:3px 0;z-index:9100}.mb-wrap.open .mb-drop{display:block}.mb-item{display:flex;justify-content:space-between;align-items:center;width:100%;background:none;border:none;color:#cfd4dc;padding:5px 10px;font:700 10px "Courier New",monospace;text-align:left;cursor:pointer}.mb-item:hover{background:#e05a47;color:#111}.mb-sep{height:1px;background:#2b3038;margin:3px 0}.mb-key{opacity:.65;font-size:9px;margin-left:12px}.mb-right{margin-left:auto;color:#7e8796;font-size:9px;letter-spacing:.8px}`;
  document.head.appendChild(st);

  const abToB64=ab=>{const u=new Uint8Array(ab);let s="",c=0x8000;for(let i=0;i<u.length;i+=c)s+=String.fromCharCode.apply(null,u.subarray(i,i+c));return btoa(s);};
  const b64ToAb=b64=>{const s=atob(b64),u=new Uint8Array(s.length);for(let i=0;i<s.length;i++)u[i]=s.charCodeAt(i);return u.buffer;};

  async function saveProject(){
    hud.innerHTML="<b>SAVING PROJECT...</b>";
    const bankData=await Promise.all(banks.map(b=>Promise.all(b.map(async p=>{
      let wavB64=null;
      if(p.buffer)wavB64=abToB64(await encodeWav16(p.buffer).arrayBuffer());
      return{name:p.name,startNorm:p.startNorm,endNorm:p.endNorm,loopBeats:p.loopBeats,syncWarp:p.syncWarp,grade:p.grade,stereo:p.stereo,gate:p.gate,loop:p.loop,reverse:p.reverse,vol:p.vol,pan:p.pan,pitch:p.pitch,mute:p.mute,solo:p.solo,fxSend:p.fxSend,wavB64};
    }))));
    const proj={ver:1,baseBpm,swingPct,volVal,fxVals:{...fxVals},pitchOn,mainFx,ctrlTarget,patterns,trackVel,songBars,timeline:htApi.getState?htApi.getState():null,banks:bankData};
    const fn=`sp202sync_${Math.round(baseBpm)}bpm_${new Date().toISOString().slice(0,10)}.sp202.json`;
    triggerDownload(new Blob([JSON.stringify(proj)],{type:"application/json"}),fn);
    hud.innerHTML=`<b>SAVED PROJECT:</b> ${fn}`;
  }

  async function loadProject(file){
    if(!file)return;
    initAudio();panicKillAll();
    try{
      const proj=JSON.parse(await file.text());
      if(proj.baseBpm)baseBpm=proj.baseBpm;
      if(proj.swingPct!==undefined){swingPct=proj.swingPct;if($("rng-swing"))$("rng-swing").value=swingPct;if($("lbl-swing"))$("lbl-swing").textContent=`${swingPct}%`;}
      if(proj.fxVals)Object.assign(fxVals,proj.fxVals);
      pitchOn=!!proj.pitchOn;mainFx=proj.mainFx||null;ctrlTarget=proj.ctrlTarget||null;syncFxBtns();
      if(Array.isArray(proj.patterns))for(let i=0;i<NUM_PATS;i++)for(let b=0;b<NUM_BANKS;b++)for(let p=0;p<NUM_PADS;p++)if(proj.patterns[i]?.[b]?.[p])patterns[i][b][p]=proj.patterns[i][b][p].slice(0,NUM_STEPS);
      if(Array.isArray(proj.trackVel))for(let b=0;b<NUM_BANKS;b++)if(proj.trackVel[b])trackVel[b]=proj.trackVel[b].slice(0,NUM_PADS);
      if(Array.isArray(proj.songBars))for(let i=0;i<NUM_BARS;i++)if(proj.songBars[i]){songBars[i].pat=proj.songBars[i].pat||0;if(proj.songBars[i].tracks)songBars[i].tracks=structuredClone(proj.songBars[i].tracks);}
      if(Array.isArray(proj.banks)){
        for(let b=0;b<NUM_BANKS;b++)for(let p=0;p<NUM_PADS;p++){
          const src=proj.banks[b]?.[p],dst=banks[b][p];if(!src)continue;
          let buf=null;if(src.wavB64)buf=await ac.decodeAudioData(b64ToAb(src.wavB64));
          Object.assign(dst,{buffer:buf,cache:{},waveZoom:1,waveScroll:0,name:src.name||`EMPTY ${BANK_NAMES[b]}${p+1}`,startNorm:src.startNorm??0,endNorm:src.endNorm??1,loopBeats:src.loopBeats??null,syncWarp:!!src.syncWarp,grade:src.grade||0,stereo:!!src.stereo,gate:!!src.gate,loop:!!src.loop,reverse:!!src.reverse,vol:src.vol??.85,pan:src.pan??0,pitch:src.pitch??1,mute:!!src.mute,solo:!!src.solo,fxSend:!!src.fxSend});
        }
      }
      if(proj.timeline&&htApi.setState)htApi.setState(proj.timeline);
      updateAllMixerNodes();applyFxRealtime();refreshAllBankUI(true);updateDynamicDisplay();syncPadVisuals();syncWaveEditorUI();renderAllWaveCanvases();
      hud.innerHTML=`<b>LOADED PROJECT:</b> ${file.name}`;
    }catch(err){hud.innerHTML=`<b>LOAD ERROR:</b> ${err.message||"INVALID PROJECT FILE"}`;}
  }

  function newProject(){
    if(!confirm("Start a new empty project? Unsaved changes will be cleared."))return;
    panicKillAll();baseBpm=90;swingPct=10;pitchOn=false;mainFx=null;ctrlTarget=null;
    Object.keys(fxVals).forEach(k=>fxVals[k]=.5);syncFxBtns();
    for(let b=0;b<NUM_BANKS;b++)for(let p=0;p<NUM_PADS;p++){const ch=banks[b][p];Object.assign(ch,{buffer:null,cache:{},startNorm:0,endNorm:1,loopBeats:null,waveZoom:1,waveScroll:0,syncWarp:false,grade:0,stereo:false,gate:false,loop:false,reverse:false,vol:.85,pan:0,pitch:1,mute:false,solo:false,fxSend:false,name:`EMPTY ${BANK_NAMES[b]}${p+1}`});trackVel[b][p]=.85;}
    for(let i=0;i<NUM_PATS;i++)for(let b=0;b<NUM_BANKS;b++)for(let p=0;p<NUM_PADS;p++)patterns[i][b][p].fill(0);
    songBars.forEach(sb=>{sb.pat=0;sb.tracks.forEach(t=>t.fill(true));});
    if(htApi.setState)htApi.setState({timelineActive:false,timelineWarp:false,loopAuto:true,loopStart:0,loopEnd:32,clips:[{id:1,lane:0,kind:"seq",pat:0,bank:0,startStep:0,lengthSteps:16,label:"SEQ P1 (A)"}]});
    updateAllMixerNodes();applyFxRealtime();refreshAllBankUI(true);updateDynamicDisplay();syncPadVisuals();syncWaveEditorUI();renderAllWaveCanvases();
    hud.innerHTML="<b>NEW PROJECT INITIALIZED</b>";
  }

  const projInp=document.createElement("input");projInp.type="file";projInp.accept=".json,.sp202.json";projInp.style.display="none";
  projInp.onchange=e=>{loadProject(e.target.files[0]);e.target.value="";};document.body.appendChild(projInp);

  const mb=document.createElement("div");mb.id="sp202-menubar";
  mb.innerHTML=`
    <div class="mb-wrap" data-mb="file"><button class="mb-btn">FILE</button><div class="mb-drop">
      <button class="mb-item" id="mb-new">NEW PROJECT</button>
      <button class="mb-item" id="mb-save">SAVE PROJECT (.SP202.JSON)</button>
      <button class="mb-item" id="mb-load">LOAD PROJECT...</button>
      <div class="mb-sep"></div>
      <button class="mb-item" id="mb-exp-fx">EXPORT PAD WAV (FX)</button>
      <button class="mb-item" id="mb-exp-raw">EXPORT PAD WAV (RAW)</button>
      <div class="mb-sep"></div>
      <button class="mb-item" id="mb-ld-fld">LOAD SAMPLE FOLDER...</button>
      <button class="mb-item" id="mb-ld-fls">LOAD AUDIO FILES...</button>
    </div></div>
    <div class="mb-wrap" data-mb="edit"><button class="mb-btn">EDIT</button><div class="mb-drop">
      <button class="mb-item" id="mb-undo">UNDO TIMELINE<span class="mb-key">CTRL+Z</span></button>
      <div class="mb-sep"></div>
      <button class="mb-item" id="mb-cut">CUT CLIPS<span class="mb-key">CTRL+X</span></button>
      <button class="mb-item" id="mb-copy">COPY CLIPS<span class="mb-key">CTRL+C</span></button>
      <button class="mb-item" id="mb-paste">PASTE AT PLAYHEAD<span class="mb-key">CTRL+V</span></button>
      <button class="mb-item" id="mb-dup">DUPLICATE CLIPS<span class="mb-key">CTRL+D</span></button>
      <button class="mb-item" id="mb-sall">SELECT ALL CLIPS<span class="mb-key">CTRL+A</span></button>
      <button class="mb-item" id="mb-del">DELETE SELECTED<span class="mb-key">DEL</span></button>
      <div class="mb-sep"></div>
      <button class="mb-item" id="mb-tmode">TOGGLE CLASSIC / TIMELINE</button>
      <button class="mb-item" id="mb-lauto">RESET LOOP TO AUTO</button>
      <button class="mb-item" id="mb-clrtl">CLEAR TIMELINE CLIPS</button>
      <button class="mb-item" id="mb-clrpat">CLEAR CURRENT PATTERN</button>
    </div></div>
    <div class="mb-wrap" data-mb="opt"><button class="mb-btn">OPTIONS</button><div class="mb-drop">
      <button class="mb-item" id="mb-opt-warp">TIMELINE WARP-TO-GRID: OFF</button>
      <div class="mb-sep"></div>
      <button class="mb-item" id="mb-opt-exp">TOGGLE SAMPLE EXPLORER</button>
      <button class="mb-item" id="mb-opt-panic">PANIC KILL ALL AUDIO<span class="mb-key">ESC</span></button>
    </div></div>
    <span class="mb-right">SP-202 SYNC</span>`;
  document.body.prepend(mb);

  const closeMenus=()=>mb.querySelectorAll(".mb-wrap.open").forEach(w=>w.classList.remove("open"));
  mb.querySelectorAll(".mb-wrap").forEach(w=>{
    w.querySelector(".mb-btn").onclick=e=>{e.stopPropagation();const o=w.classList.contains("open");closeMenus();if(!o)w.classList.add("open");};
    w.onmouseenter=()=>{if(mb.querySelector(".mb-wrap.open")){closeMenus();w.classList.add("open");}};
  });
  window.addEventListener("mousedown",e=>{if(!e.target.closest("#sp202-menubar"))closeMenus();});
  const bind=(id,fn)=>{const el=$(id);if(el)el.onclick=()=>{closeMenus();fn();};};

  bind("mb-new",newProject);bind("mb-save",saveProject);bind("mb-load",()=>projInp.click());
  bind("mb-exp-fx",()=>exportPadWav(true));bind("mb-exp-raw",()=>exportPadWav(false));
  bind("mb-ld-fld",()=>$("inp-folder").click());bind("mb-ld-fls",()=>$("inp-files").click());
  bind("mb-undo",()=>htApi.undo&&htApi.undo());bind("mb-cut",()=>htApi.cut&&htApi.cut());bind("mb-copy",()=>htApi.copy&&htApi.copy());
  bind("mb-paste",()=>htApi.paste&&htApi.paste());bind("mb-dup",()=>htApi.dup&&htApi.dup());bind("mb-sall",()=>htApi.selAll&&htApi.selAll());
  bind("mb-del",()=>htApi.del&&htApi.del());bind("mb-tmode",()=>htApi.toggleMode&&htApi.toggleMode());bind("mb-lauto",()=>htApi.setLoopAuto&&htApi.setLoopAuto());
  bind("mb-clrtl",()=>htApi.clear&&htApi.clear());bind("mb-clrpat",()=>{$("btn-seq-clear").click();});
  bind("mb-opt-warp",()=>htApi.toggleWarp&&htApi.toggleWarp());bind("mb-opt-exp",()=>toggleDrawer());bind("mb-opt-panic",panicKillAll);
})();













(()=>{
  const mb=$("sp202-menubar"),lbl=$("arr-bank-lbl"),bar=$("hybrid-mode-bar");
  if(!mb||!bar)return;
  const r=mb.querySelector(".mb-right");
  const titleEl=lbl&&lbl.parentElement!==bar.parentNode?lbl.parentElement:bar.previousElementSibling;
  mb.style.cssText="position:relative;top:auto;z-index:20;height:24px;padding:0;background:transparent;border:none;flex:1;";
  if(r&&lbl){r.textContent="BANK ";r.appendChild(lbl);}
  if(titleEl&&!titleEl.querySelector("#btn-arr-fill")){
    titleEl.replaceWith(mb);
  }else if(bar.previousElementSibling){
    const h=bar.previousElementSibling;
    [...h.childNodes].forEach(n=>{if(n.nodeType===3||(!n.querySelector?.("#btn-arr-fill")&&n.id!=="btn-arr-fill"&&n.id!=="btn-arr-clear"))n.remove();});
    h.prepend(mb);
  }else{
    bar.parentNode.insertBefore(mb,bar);
  }
})();




(()=>{
  if($("sp202-computo-font"))return;
  const st=document.createElement("style");
  st.id="sp202-computo-font";
  st.textContent=`
    @font-face{font-family:"Computo";src:url("video.ttf") format("truetype");font-display:swap;}
    *,*::before,*::after,html,body,button,input,select,textarea{font-family:"Computo",monospace!important;}
  `;
  document.head.appendChild(st);
})();







(()=>{
  const bar=$("hybrid-mode-bar"),lanes=$("ht-lanes"),shell=$("hybrid-song-shell");
  if(!bar||!lanes||$("ht-fx-lane"))return;

  const TOTAL_STEPS=64*NUM_STEPS,HDR_W=94,ROW_H=16,CV_H=ROW_H*6;
  const FX_LIST=[
    {id:"pitch",lbl:"PITCH",col:"#00d2ff"},
    {id:"time",lbl:"TIME",col:"#ff9d47"},
    {id:"delay",lbl:"DELAY",col:"#4dff91"},
    {id:"filter1",lbl:"FLT 1",col:"#ff4e3a"},
    {id:"filter2",lbl:"FLT 2",col:"#ff66cc"},
    {id:"ringmod",lbl:"RING",col:"#ffe047"}
  ];
  let fxSteps=Array.from({length:TOTAL_STEPS},()=>({p:false,m:null,v:null}));
  let fxOpen=false,fxRec=false,fxOn=true,fxTab="gate",lastStep=0;

  if(!$("sp202-fx-auto-css")){
    const st=document.createElement("style");st.id="sp202-fx-auto-css";
    st.textContent=`
      #ht-fx-lane{display:none;border-top:2px solid #e05a47;border-bottom:1px solid #232730;background:#0e1014}
      #ht-fx-lane.open{display:flex}
      .ht-fx-hdr{width:${HDR_W}px;flex-shrink:0;position:sticky;left:0;z-index:6;background:#16181e;border-right:1px solid #3c4250;display:flex;flex-direction:column}
      .ht-fx-top{padding:3px 4px;border-bottom:1px solid #2b3038;display:flex;gap:2px;justify-content:center}
      .ht-fx-tabs{display:flex;border-bottom:1px solid #2b3038}
      .ht-fx-tab{flex:1;background:#1a1d24;color:#7e8796;border:none;font:700 8px "Courier New",monospace;padding:3px 0;cursor:pointer}
      .ht-fx-tab.active{background:#e05a47;color:#111}
      .ht-fx-b{background:#232730;color:#8e96a4;border:1px solid #353b47;border-radius:2px;font:700 8px "Courier New",monospace;padding:1px 4px;cursor:pointer}
      .ht-fx-b.rec{background:#ff2638;color:#fff;border-color:#ff7882}
      .ht-fx-b.on{background:#4dff91;color:#08120c;border-color:#8affb8}
      .ht-fx-rlbl{height:${ROW_H}px;display:flex;align-items:center;padding:0 6px;font:700 8px "Courier New",monospace;border-bottom:1px solid #1d2028;box-sizing:border-box}
      .ht-fx-ctrl-info{flex:1;display:flex;flex-direction:column;justify-content:space-between;padding:5px 6px;font:700 8px "Courier New",monospace;color:#8e96a4}
      .ht-fx-body{display:flex;flex-direction:column;flex-shrink:0}
      .ht-fx-spacer{height:38px;background:#111318;border-bottom:1px solid #2b3038;font:700 8px "Courier New",monospace;color:#6d7482;display:flex;align-items:center;padding-left:6px;box-sizing:border-box}
      #ht-fx-cv{display:block;height:${CV_H}px;flex-shrink:0;cursor:crosshair}
    `;
    document.head.appendChild(st);
  }

  const tBtn=document.createElement("button");
  tBtn.className="h-btn amber";tBtn.id="ht-fx-toggle";tBtn.textContent="FX AUTO";
  bar.appendChild(tBtn);

  const row=document.createElement("div");row.id="ht-fx-lane";
  row.innerHTML=`
    <div class="ht-fx-hdr">
      <div class="ht-fx-top">
        <button class="ht-fx-b" id="ht-fx-rec" title="Record live FX + Knob">REC</button>
        <button class="ht-fx-b on" id="ht-fx-on" title="Enable playback">ON</button>
        <button class="ht-fx-b" id="ht-fx-clr" title="Clear all">CLR</button>
      </div>
      <div class="ht-fx-tabs">
        <button class="ht-fx-tab active" id="ht-fx-tgate">GATE</button>
        <button class="ht-fx-tab" id="ht-fx-tctrl">CTRL</button>
      </div>
      <div id="ht-fx-lbls">${FX_LIST.map(f=>`<div class="ht-fx-rlbl" style="color:${f.col}">${f.lbl}</div>`).join("")}</div>
      <div class="ht-fx-ctrl-info" id="ht-fx-cinfo" style="display:none"><span>100%</span><span>CTRL</span><span>0%</span></div>
    </div>
    <div class="ht-fx-body">
      <div class="ht-fx-spacer" id="ht-fx-hint">GATE: LEFT-DRAG ON · RIGHT-DRAG OFF</div>
      <canvas id="ht-fx-cv"></canvas>
    </div>`;
  lanes.after(row);

  const cv=$("ht-fx-cv"),ctx=cv.getContext("2d");
  const getStepPx=()=>{const b=$("ht-ruler")?.firstElementChild;return b?parseFloat(b.style.width)/NUM_STEPS:14;};

  function drawFxLane(){
    if(!fxOpen)return;
    const spx=getStepPx(),w=Math.max(1,Math.round(TOTAL_STEPS*spx)),h=CV_H;
    cv.style.width=`${w}px`;cv.width=w;cv.height=h;
    ctx.fillStyle="#0e1014";ctx.fillRect(0,0,w,h);
    ctx.strokeStyle="rgba(255,255,255,.06)";ctx.lineWidth=1;ctx.beginPath();
    if(fxTab==="gate"){
      for(let r=1;r<6;r++){const y=r*ROW_H+.5;ctx.moveTo(0,y);ctx.lineTo(w,y);}
    }else{
      const y=h/2+.5;ctx.moveTo(0,y);ctx.lineTo(w,y);
    }
    for(let s=0;s<TOTAL_STEPS;s+=NUM_STEPS){const x=s*spx+.5;ctx.moveTo(x,0);ctx.lineTo(x,h);}
    ctx.stroke();

    for(let s=0;s<TOTAL_STEPS;s++){
      const d=fxSteps[s];if(!d)continue;
      const x=s*spx,cw=Math.max(1,spx-1);
      if(fxTab==="gate"){
        if(d.p){ctx.fillStyle=FX_LIST[0].col;ctx.fillRect(x,2,cw,ROW_H-4);}
        if(d.m){const rIdx=FX_LIST.findIndex(f=>f.id===d.m);if(rIdx>0){ctx.fillStyle=FX_LIST[rIdx].col;ctx.fillRect(x,rIdx*ROW_H+2,cw,ROW_H-4);}}
      }else{
        const key=d.m||(d.p?"pitch":null);
        if(!key||!d.v)continue;
        const val=typeof d.v[key]==="number"?d.v[key]:.5;
        const col=FX_LIST.find(f=>f.id===key)?.col||"#ff9d47";
        const bh=Math.max(3,Math.round(val*(h-4)));
        ctx.fillStyle=col;ctx.globalAlpha=.35;ctx.fillRect(x,h-bh,cw,bh);
        ctx.globalAlpha=1;ctx.fillRect(x,h-bh,cw,2);
      }
    }
  }

  const setFxTab=t=>{
    fxTab=t;
    $("ht-fx-tgate").classList.toggle("active",t==="gate");
    $("ht-fx-tctrl").classList.toggle("active",t==="ctrl");
    $("ht-fx-lbls").style.display=t==="gate"?"":"none";
    $("ht-fx-cinfo").style.display=t==="ctrl"?"flex":"none";
    $("ht-fx-hint").textContent=t==="gate"?"GATE: LEFT-DRAG ON · RIGHT-DRAG OFF":"CTRL: LEFT-DRAG DRAW KNOB BAR · RIGHT-DRAG RESET 50%";
    drawFxLane();
  };
  $("ht-fx-tgate").onclick=()=>setFxTab("gate");
  $("ht-fx-tctrl").onclick=()=>setFxTab("ctrl");
  tBtn.onclick=()=>{fxOpen=!fxOpen;row.classList.toggle("open",fxOpen);tBtn.classList.toggle("active",fxOpen);if(fxOpen)drawFxLane();};
  $("ht-fx-rec").onclick=e=>{fxRec=!fxRec;e.target.classList.toggle("rec",fxRec);hud.innerHTML=`FX AUTO REC: <b>${fxRec?"ARMED (PUNCH FX + TWIST CTRL)":"OFF"}</b>`;};
  $("ht-fx-on").onclick=e=>{fxOn=!fxOn;e.target.classList.toggle("on",fxOn);};
  $("ht-fx-clr").onclick=()=>{fxSteps=Array.from({length:TOTAL_STEPS},()=>({p:false,m:null,v:null}));drawFxLane();hud.innerHTML="<b>FX AUTOMATION CLEARED</b>";};

  cv.oncontextmenu=e=>e.preventDefault();
  cv.onmousedown=e=>{
    const r=cv.getBoundingClientRect(),spx=getStepPx(),erase=e.button===2;
    const paint=ev=>{
      const st=Math.max(0,Math.min(TOTAL_STEPS-1,Math.floor((ev.clientX-r.left)/spx)));
      const d=fxSteps[st];
      if(fxTab==="gate"){
        const rIdx=Math.max(0,Math.min(5,Math.floor((ev.clientY-r.top)/ROW_H))),fx=FX_LIST[rIdx].id;
        if(erase){if(fx==="pitch")d.p=false;else if(d.m===fx)d.m=null;}
        else{
          if(fx==="pitch"){d.p=true;if(d.m&&!BOTTOM_FX.includes(d.m))d.m=null;}
          else if(BOTTOM_FX.includes(fx))d.m=fx;
          else{d.p=false;d.m=fx;}
          if(!d.v)d.v={...fxVals};
        }
      }else{
        const key=d.m||(d.p?"pitch":ctrlTarget);
        if(!key)return;
        if(!d.v)d.v={...fxVals};
        d.v[key]=erase?.5:Math.max(0,Math.min(1,1-(ev.clientY-r.top)/CV_H));
      }
      drawFxLane();
    };
    paint(e);
    const up=()=>{window.removeEventListener("mousemove",paint);window.removeEventListener("mouseup",up);};
    window.addEventListener("mousemove",paint);window.addEventListener("mouseup",up);
  };

  new MutationObserver(()=>{if(fxOpen)drawFxLane();}).observe(lanes,{childList:true});

  const recStep=s=>{fxSteps[s]={p:pitchOn,m:mainFx,v:{...fxVals}};drawFxLane();};
  const recNow=()=>{if(fxRec&&isPlaying&&playMode==="song"&&shell.classList.contains("open"))recStep(lastStep);};
  document.querySelectorAll(".fx-btn").forEach(b=>b.addEventListener("click",()=>setTimeout(recNow,0)));
  if($("knob-ctrl")){
    $("knob-ctrl").addEventListener("wheel",()=>setTimeout(recNow,0));
    window.addEventListener("mousemove",e=>{if(e.buttons===1)recNow();});
  }

  const _origUI=updatePlayheadUI;
  updatePlayheadUI=function(step,barIdx){
    _origUI(step,barIdx);
    if(playMode!=="song"||!shell.classList.contains("open"))return;
    const gStep=barIdx*NUM_STEPS+step;
    if(gStep<0||gStep>=TOTAL_STEPS)return;
    lastStep=gStep;
    if(fxRec){recStep(gStep);return;}
    if(!fxOn)return;
    const d=fxSteps[gStep],nextP=!!d.p,nextM=d.m||null;
    const changed=pitchOn!==nextP||mainFx!==nextM;
    pitchOn=nextP;mainFx=nextM;
    ctrlTarget=mainFx||(pitchOn?"pitch":null);
    if(d.v&&ctrlTarget&&typeof d.v[ctrlTarget]==="number")fxVals[ctrlTarget]=d.v[ctrlTarget];
    if(changed||d.v){syncFxBtns();applyFxRealtime();}
  };

  if(htApi.getState&&htApi.setState){
    const _gs=htApi.getState,_ss=htApi.setState;
    htApi.getState=()=>({..._gs(),fxSteps});
    htApi.setState=st=>{_ss(st);if(Array.isArray(st?.fxSteps))fxSteps=st.fxSteps.slice(0,TOTAL_STEPS);drawFxLane();};
  }
})();



















    
    
})();
