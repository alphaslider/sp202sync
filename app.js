(()=>{
const $=id=>document.getElementById(id);
const NUM_BANKS=4,BANK_NAMES=["A","B","C","D"],BEAT_CYCLE=[1,2,4,8,16,32],NUM_PADS=8,NUM_STEPS=16,NUM_PATS=8,NUM_BARS=16;
const GRADE_SPECS=[{name:"HI-FI",rate:31250,bits:12},{name:"STANDARD",rate:15625,bits:10},{name:"LO-FI 1",rate:7812,bits:8},{name:"LO-FI 2",rate:3906,bits:6}];
const JP_NAMES=["大太鼓 TAIKO-808","スネア SNARE-909","閉ハイハット CH-606","開ハイハット OH-606","手拍子 CLAP-202","重低音 SUB-303","エレピ RHODES-JP","木魚 MOKUGYO"];
const SOV_NAMES=["БОЧКА LEL-KICK","РАБОЧИЙ RITM-SNR","ХЭТ-ЗАК FORM-CH","ХЭТ-ОТК FORM-OH","ТОМ-АЛЬТ ELSITA","БАС-ГУД POLIVOKS","ЗВОН KREMEN-BELL","ШУМ-УДАР SOV-ZAP"];

let ac=null,masterGain,fxInput,lpfNode,hpfNode,lpfWet,hpfWet,thruGain,postFilterBus,ringGain,ringOsc,ringDepth,delayNode,delayLpf,delayFb,delayWet,dryGain;
const banks=Array.from({length:NUM_BANKS},(_,b)=>Array.from({length:NUM_PADS},(_,p)=>({
  bank:b,pad:p,name:b===0?JP_NAMES[p]:(b===1?SOV_NAMES[p]:`空き EMPTY ${BANK_NAMES[b]}${p+1}`),
  buffer:null,cache:{},startNorm:0,endNorm:1,loopBeats:null,waveZoom:1,waveScroll:0,
  grade:0,stereo:false,gate:false,loop:false,reverse:false,vol:0.85,pan:0,pitch:1.0,
  mute:false,solo:false,fxSend:(b===0||b===1)&&p<4,activeVoice:null,gainNode:null,panNode:null,analyser:null,dryOut:null,fxOut:null
})));
const patterns=Array.from({length:NUM_PATS},()=>Array.from({length:NUM_BANKS},()=>Array.from({length:NUM_PADS},()=>new Array(NUM_STEPS).fill(0))));
const trackVel=Array.from({length:NUM_BANKS},()=>new Array(NUM_PADS).fill(0.85));
const songBars=Array.from({length:NUM_BARS},()=>({pat:0,tracks:Array.from({length:NUM_BANKS},()=>new Array(NUM_PADS).fill(true))}));

let currentBank=0,selectedPad=0,currentPat=0,activeFx=null,holdOn=false,remainMode=false,deleteMode=false,truncateMode=false,deleteTargetPad=null;
let resampleState=null,resampleTarget=null,resampleNode=null,resampleChunksL=[],resampleChunksR=[],resampleFrames=0,resampleIdx=1;
let bpm=90,displayedLedValue=90,swingPct=10,volVal=0.85,ctrlVal=0.50,lastTap=0;
let isPlaying=false,playMode="pat",currentStep=0,currentBar=0,nextStepTime=0,schedTimer=null;
let auditionSource=null,auditionEl=null,draggingSampleId=null,sampleIdCounter=1;
const sampleRegistry=new Map(),folderTree={name:"ROOT",folders:{},files:[]},meterSegsUI=Array.from({length:NUM_PADS},()=>[]);
const hud=$("hud"),stepLed=$("step-led"),drawer=$("explorer-drawer"),spExplorerBtn=$("btn-sp-explorer"),rackBpmInp=$("rack-bpm-inp"),waveBpmInp=$("wave-bpm-inp"),btnWaveBeats=$("btn-wave-beats");

const curPadObj=()=>banks[currentBank][selectedPad];
const rateToSemi=r=>12*Math.log2(Math.max(0.25,r));
const semiToRate=s=>Math.pow(2,s/12);
const fmtBpm=v=>Number.isFinite(v)?Number(v.toFixed(2)).toString():"";
const getMinNormGap=p=>(!p||!p.buffer||!p.buffer.duration)?0.0001:Math.min(0.05,0.015/p.buffer.duration);
const getMaxZoomForPad=p=>(!p||!p.buffer||!p.buffer.duration)?64:Math.max(64,Math.min(2048,Math.ceil(p.buffer.duration/0.04)));

// 7-SEG LED
const bpmCanvas=$("bpm-canvas"),bpmCtx=bpmCanvas.getContext("2d");
const SEG_MAP={"0":[1,1,1,1,1,1,0],"1":[0,1,1,0,0,0,0],"2":[1,1,0,1,1,0,1],"3":[1,1,1,1,0,0,1],"4":[0,1,1,0,0,1,1],"5":[1,0,1,1,0,1,1],"6":[1,0,1,1,1,1,1],"7":[1,1,1,0,0,0,0],"8":[1,1,1,1,1,1,1],"9":[1,1,1,1,0,1,1],"-":[0,0,0,0,0,0,1]," ":[0,0,0,0,0,0,0]};
function drawSeg(ctx,x,y,l,t,v){
  const h=t/2;ctx.beginPath();
  if(!v){ctx.moveTo(x+h,y);ctx.lineTo(x+l-h,y);ctx.lineTo(x+l,y+h);ctx.lineTo(x+l-h,y+t);ctx.lineTo(x+h,y+t);ctx.lineTo(x,y+h);}
  else{ctx.moveTo(x+h,y);ctx.lineTo(x+t,y+h);ctx.lineTo(x+t,y+l-h);ctx.lineTo(x+h,y+l);ctx.lineTo(x,y+l-h);ctx.lineTo(x,y+h);}
  ctx.closePath();ctx.fill();
}
function drawSevenSegDisplay(val){
  displayedLedValue=val;const r=bpmCanvas.getBoundingClientRect();if(!r.width||!r.height)return;
  const dpr=window.devicePixelRatio||1,w=r.width,h=r.height;
  if(bpmCanvas.width!==Math.floor(w*dpr)||bpmCanvas.height!==Math.floor(h*dpr)){bpmCanvas.width=Math.floor(w*dpr);bpmCanvas.height=Math.floor(h*dpr);}
  bpmCtx.setTransform(dpr,0,0,dpr,0,0);bpmCtx.clearRect(0,0,w,h);
  const str=String(val==null?"---":Math.round(val)).padStart(3," ").slice(-3);
  const padX=w*0.06,padY=h*0.12,digH=h-padY*2,digSlot=(w-padX*2)/3,digW=digSlot*0.72,thick=Math.max(2.2,digH*0.125),gap=thick*0.28;
  for(let i=0;i<3;i++){
    const segs=SEG_MAP[str[i]||" "]||SEG_MAP[" "],ox=padX+i*digSlot+(digSlot-digW)*0.5;
    bpmCtx.save();bpmCtx.translate(ox+digW*0.08,padY);bpmCtx.transform(1,0,-0.11,1,0,0);
    const hL=digW-thick*0.9,vL=(digH-thick*1.1)/2;
    const coords=[()=>drawSeg(bpmCtx,thick*0.45,0,hL,thick,0),()=>drawSeg(bpmCtx,digW-thick,thick*0.5+gap,vL-gap,thick,1),()=>drawSeg(bpmCtx,digW-thick,digH/2+gap,vL-gap,thick,1),()=>drawSeg(bpmCtx,thick*0.45,digH-thick,hL,thick,0),()=>drawSeg(bpmCtx,0,digH/2+gap,vL-gap,thick,1),()=>drawSeg(bpmCtx,0,thick*0.5+gap,vL-gap,thick,1),()=>drawSeg(bpmCtx,thick*0.45,(digH-thick)/2,hL,thick,0)];
    bpmCtx.shadowBlur=0;bpmCtx.fillStyle="rgba(65,14,18,0.34)";coords.forEach(fn=>fn());
    bpmCtx.fillStyle="#ff2638";bpmCtx.shadowColor="rgba(255,30,50,0.95)";bpmCtx.shadowBlur=Math.max(6,digH*0.22);
    segs.forEach((on,idx)=>{if(on)coords[idx]();});bpmCtx.restore();
  }
}

// BPM & PITCH
function getEffectivePadRate(pad){let rate=pad.pitch;if(pad.fxSend){if(activeFx==="pitch")rate*=(0.5+ctrlVal*1.5);else if(activeFx==="time")rate*=(0.65+ctrlVal*0.7);}return Math.max(0.25,rate);}
function resolveLoopBeats(pad,rawDur){if(pad.loopBeats!==null)return pad.loopBeats;const ch=[4,8,2,16,1,32];for(const b of ch){const c=(b*60)/rawDur;if(c>=70&&c<=155)return b;}let best=4,minD=Infinity;for(const b of ch){const d=Math.abs((b*60)/rawDur-105);if(d<minD){minD=d;best=b;}}return best;}
function detectLoopBpm(pad){if(!pad||!pad.buffer)return null;const rawDur=(pad.endNorm-pad.startNorm)*pad.buffer.duration;if(rawDur<0.05)return null;const beats=resolveLoopBeats(pad,rawDur),baseBpm=(beats*60)/rawDur,effRate=getEffectivePadRate(pad);return{bpm:baseBpm*effRate,padBpm:baseBpm*pad.pitch,baseBpm,beats,dur:rawDur/effRate};}
function showPadBpmOnDisplay(pad){
  const info=detectLoopBpm(pad);
  if(info){drawSevenSegDisplay(Math.round(info.bpm));if(document.activeElement!==waveBpmInp)waveBpmInp.value=fmtBpm(info.padBpm);waveBpmInp.disabled=false;btnWaveBeats.textContent=`${info.beats}B`;}
  else{drawSevenSegDisplay(bpm);waveBpmInp.value="";waveBpmInp.disabled=true;btnWaveBeats.textContent="--";}
}
function setPadPitchRate(bIdx,pIdx,newRate){
  const pad=banks[bIdx][pIdx];pad.pitch=Math.max(0.5,Math.min(2.0,newRate));
  if(ac&&pad.activeVoice){const eff=getEffectivePadRate(pad);pad.activeVoice.rate=eff;pad.activeVoice.src.playbackRate.setTargetAtTime(eff,ac.currentTime,0.012);}
  if(bIdx===currentBank){const mt=$(`mix-tune-${pIdx}`);if(mt)mt.value=pad.pitch;if(pIdx===selectedPad){syncWaveEditorUI();showPadBpmOnDisplay(pad);}}
}
function setPadTargetBpm(bIdx,pIdx,targetBpm){
  const pad=banks[bIdx][pIdx],info=detectLoopBpm(pad);if(!info||!Number.isFinite(targetBpm)||targetBpm<=0)return;
  if(pad.loopBeats===null)pad.loopBeats=info.beats;
  const desired=targetBpm/info.baseBpm,clamped=Math.max(0.5,Math.min(2.0,desired));setPadPitchRate(bIdx,pIdx,clamped);
  const up=detectLoopBpm(pad);
  if(up){const semi=rateToSemi(pad.pitch);hud.innerHTML=`BANK ${BANK_NAMES[bIdx]} PAD ${pIdx+1} BPM: <b>${up.padBpm.toFixed(2)} BPM</b> (${semi>=0?"+":""}${semi.toFixed(2)} st)${desired!==clamped?" (OCTAVE LIMIT)":""}`;}
}
function stepPadBpm(delta){const info=detectLoopBpm(curPadObj());if(info)setPadTargetBpm(currentBank,selectedPad,info.padBpm+delta);}

// TRUNCATE
function truncatePadSample(bIdx,pIdx){
  initAudio();const pad=banks[bIdx][pIdx];
  if(!pad||!pad.buffer){hud.innerHTML=`<b>TRUNCATE:</b> BANK ${BANK_NAMES[bIdx]} PAD ${pIdx+1} IS EMPTY`;return false;}
  const srcBuf=pad.buffer,totalLen=srcBuf.length,sF=Math.max(0,Math.min(totalLen-1,Math.floor(pad.startNorm*totalLen))),eF=Math.max(sF+1,Math.min(totalLen,Math.ceil(pad.endNorm*totalLen)));
  if(sF===0&&eF===totalLen){hud.innerHTML="<b>TRUNCATE:</b> MARK POINTS ALREADY AT FULL LENGTH";return false;}
  stopPadVoice(bIdx,pIdx);
  const newBuf=ac.createBuffer(srcBuf.numberOfChannels,eF-sF,srcBuf.sampleRate);
  for(let c=0;c<srcBuf.numberOfChannels;c++)newBuf.getChannelData(c).set(srcBuf.getChannelData(c).subarray(sF,eF));
  pad.buffer=newBuf;pad.cache={};pad.startNorm=0;pad.endNorm=1;
  resetPadZoom(pad);syncPadVisuals();syncWaveEditorUI();showPadBpmOnDisplay(pad);renderAllWaveCanvases();
  hud.innerHTML=`<b>TRUNCATED</b> BANK ${BANK_NAMES[bIdx]} PAD ${pIdx+1} (${pad.name}) → <b>${newBuf.duration.toFixed(3)} s</b>`;return true;
}

// DECIMATION & WAV EXPORT
function renderDecimatedBuffer(ctx,srcBuf,grade,reverse){
  if(!srcBuf)return null;
  const sr=srcBuf.sampleRate,len=srcBuf.length,nCh=srcBuf.numberOfChannels,spec=GRADE_SPECS[grade];
  const stepRatio=Math.max(1,sr/spec.rate),qL=Math.pow(2,spec.bits-1),outBuf=ctx.createBuffer(nCh,len,sr);
  for(let c=0;c<nCh;c++){
    const src=srcBuf.getChannelData(c),dst=outBuf.getChannelData(c);let phase=stepRatio,hold=0;
    for(let i=0;i<len;i++){const si=reverse?(len-1-i):i;phase+=1;if(phase>=stepRatio){phase-=stepRatio;let s=src[si];if(grade>=2)s=Math.tanh(s*(grade===3?1.55:1.25));hold=Math.round(s*qL)/qL;}dst[i]=hold;}
  }
  return outBuf;
}
function getProcessedBuffer(pad){if(!pad.buffer)return null;const k=`${pad.grade}_${pad.reverse?1:0}`;return pad.cache[k]||(pad.cache[k]=renderDecimatedBuffer(ac,pad.buffer,pad.grade,pad.reverse));}
function encodeWav16(ab){
  const nCh=ab.numberOfChannels,sr=ab.sampleRate,len=ab.length,ba=nCh*2,ds=len*ba,buf=new ArrayBuffer(44+ds),v=new DataView(buf);
  const ws=(o,s)=>{for(let i=0;i<s.length;i++)v.setUint8(o+i,s.charCodeAt(i));};
  ws(0,"RIFF");v.setUint32(4,36+ds,true);ws(8,"WAVE");ws(12,"fmt ");v.setUint32(16,16,true);v.setUint16(20,1,true);
  v.setUint16(22,nCh,true);v.setUint32(24,sr,true);v.setUint32(28,sr*ba,true);v.setUint16(32,ba,true);v.setUint16(34,16,true);ws(36,"data");v.setUint32(40,ds,true);
  const chs=Array.from({length:nCh},(_,c)=>ab.getChannelData(c));let o=44;
  for(let i=0;i<len;i++)for(let c=0;c<nCh;c++){const s=Math.max(-1,Math.min(1,chs[c][i]));v.setInt16(o,s<0?s*0x8000:s*0x7FFF,true);o+=2;}
  return new Blob([buf],{type:"audio/wav"});
}
function triggerDownload(blob,fn){const u=URL.createObjectURL(blob),a=document.createElement("a");a.href=u;a.download=fn;document.body.appendChild(a);a.click();a.remove();setTimeout(()=>URL.revokeObjectURL(u),4000);}
async function exportPadWav(withFx=true){
  initAudio();const pad=curPadObj();if(!pad||!pad.buffer){hud.innerHTML="<b>EXPORT:</b> SELECTED PAD IS EMPTY";return;}
  const srcBuf=pad.buffer,sr=srcBuf.sampleRate,nCh=srcBuf.numberOfChannels;
  const safeBase=(pad.name.replace(/[^\x20-\x7E]/g,"").trim()||`PAD_${BANK_NAMES[currentBank]}${selectedPad+1}`).replace(/[^A-Z0-9_-]/gi,"_");
  if(!withFx){
    const sF=Math.max(0,Math.min(srcBuf.length-1,Math.floor(pad.startNorm*srcBuf.length))),eF=Math.max(sF+1,Math.min(srcBuf.length,Math.ceil(pad.endNorm*srcBuf.length)));
    const raw=ac.createBuffer(nCh,eF-sF,sr);for(let c=0;c<nCh;c++)raw.getChannelData(c).set(srcBuf.getChannelData(c).subarray(sF,eF));
    const fn=`${safeBase}_RAW.wav`;triggerDownload(encodeWav16(raw),fn);hud.innerHTML=`EXPORTED RAW WAV: <b>${fn}</b> (${raw.duration.toFixed(3)}s)`;return;
  }
  const rate=getEffectivePadRate(pad),totalDur=srcBuf.duration,fwdS=pad.startNorm*totalDur;let fwdE=pad.endNorm*totalDur;if(fwdE-fwdS<0.01)fwdE=Math.min(totalDur,fwdS+0.01);
  const sSec=pad.reverse?Math.max(0,totalDur-fwdE):fwdS,eSec=pad.reverse?Math.min(totalDur,totalDur-fwdS):fwdE,segDur=Math.max(0.01,eSec-sSec),playDur=segDur/rate;
  const useFx=pad.fxSend&&activeFx!==null,tail=(useFx&&activeFx==="delay")?Math.min(2.2,(0.06+ctrlVal*0.64)*3.5):0.02;
  const off=new OfflineAudioContext(2,Math.max(1,Math.ceil((playDur+tail)*sr)),sr),proc=renderDecimatedBuffer(off,srcBuf,pad.grade,pad.reverse);
  const src=off.createBufferSource();src.buffer=proc;src.playbackRate.value=rate;
  const mg=off.createGain();mg.gain.value=1;mg.channelCount=pad.stereo?2:1;mg.channelCountMode=pad.stereo?"max":"explicit";
  const cg=off.createGain();cg.gain.value=pad.vol;const pan=off.createStereoPanner();pan.pan.value=pad.pan;
  src.connect(mg);mg.connect(cg);cg.connect(pan);
  if(!useFx){pan.connect(off.destination);}else{
    const isL=activeFx==="filter1",isH=activeFx==="filter2",isR=activeFx==="ringmod",isD=activeFx==="delay",pb=off.createGain();
    if(isL){const f=off.createBiquadFilter();f.type="lowpass";f.Q.value=4.2;f.frequency.value=Math.min(sr*0.42,95*Math.pow(145,ctrlVal));pan.connect(f);f.connect(pb);}
    else if(isH){const f=off.createBiquadFilter();f.type="highpass";f.Q.value=3.5;f.frequency.value=Math.min(sr*0.42,65*Math.pow(110,ctrlVal));pan.connect(f);f.connect(pb);}
    else pan.connect(pb);
    const rg=off.createGain();rg.gain.value=isR?0.5:1;
    if(isR){const ro=off.createOscillator(),rd=off.createGain();ro.frequency.value=40+ctrlVal*900;rd.gain.value=0.5;ro.connect(rd);rd.connect(rg.gain);ro.start(0);}
    pb.connect(rg);rg.connect(off.destination);
    if(isD){const dn=off.createDelay(1.2),dl=off.createBiquadFilter(),df=off.createGain(),dw=off.createGain();dn.delayTime.value=0.06+ctrlVal*0.64;dl.type="lowpass";dl.frequency.value=3800;df.gain.value=0.32+ctrlVal*0.46;dw.gain.value=0.68;rg.connect(dn);dn.connect(dl);dl.connect(df);df.connect(dn);dl.connect(dw);dw.connect(off.destination);}
  }
  src.start(0,sSec,segDur);const ren=await off.startRendering();
  const info=detectLoopBpm(pad),spec=GRADE_SPECS[pad.grade],fn=`${safeBase}_${spec.name.replace(/\s+/g,"")}${info?`_${Math.round(info.bpm)}BPM`:""}${useFx?`_${activeFx.toUpperCase()}`:""}.wav`;
  triggerDownload(encodeWav16(ren),fn);hud.innerHTML=`EXPORTED WAV: <b>${fn}</b> (${spec.name} · ${ren.duration.toFixed(3)}s)`;
}

// AUDIO ENGINE + RESAMPLE TAP
function initAudio(){
  if(ac)return;
  ac=new (window.AudioContext||window.webkitAudioContext)();
  masterGain=ac.createGain();masterGain.gain.value=volVal;masterGain.connect(ac.destination);
  resampleNode=ac.createScriptProcessor(2048,2,2);const sink=ac.createGain();sink.gain.value=0;
  masterGain.connect(resampleNode);resampleNode.connect(sink);sink.connect(ac.destination);
  resampleNode.onaudioprocess=e=>{
    if(resampleState!=="armed"&&resampleState!=="recording")return;
    const inL=e.inputBuffer.getChannelData(0),inR=e.inputBuffer.getChannelData(1);
    if(resampleState==="armed"){
      let ti=-1;for(let i=0;i<inL.length;i++){if(Math.abs(inL[i])>0.0025||Math.abs(inR[i])>0.0025){ti=i;break;}}
      if(ti===-1)return;
      resampleState="recording";resampleChunksL=[];resampleChunksR=[];resampleFrames=0;syncPadVisuals();
      hud.innerHTML=`<b style="color:#ff3850">● RESAMPLING</b> TO BANK ${BANK_NAMES[resampleTarget.bank]} PAD ${resampleTarget.pad+1} — PRESS <b>REC</b> TO FINISH`;
      const sL=new Float32Array(inL.subarray(ti)),sR=new Float32Array(inR.subarray(ti));
      resampleChunksL.push(sL);resampleChunksR.push(sR);resampleFrames+=sL.length;return;
    }
    const cL=new Float32Array(inL),cR=new Float32Array(inR);
    resampleChunksL.push(cL);resampleChunksR.push(cR);resampleFrames+=cL.length;
    if(resampleFrames>=ac.sampleRate*30)finishResampleCapture();
  };
  fxInput=ac.createGain();
  lpfNode=ac.createBiquadFilter();lpfNode.type="lowpass";lpfNode.frequency.value=1800;lpfNode.Q.value=4.2;
  hpfNode=ac.createBiquadFilter();hpfNode.type="highpass";hpfNode.frequency.value=600;hpfNode.Q.value=3.5;
  lpfWet=ac.createGain();lpfWet.gain.value=0;hpfWet=ac.createGain();hpfWet.gain.value=0;thruGain=ac.createGain();thruGain.gain.value=1;
  postFilterBus=ac.createGain();fxInput.connect(thruGain);thruGain.connect(postFilterBus);
  fxInput.connect(lpfNode);lpfNode.connect(lpfWet);lpfWet.connect(postFilterBus);
  fxInput.connect(hpfNode);hpfNode.connect(hpfWet);hpfWet.connect(postFilterBus);
  ringGain=ac.createGain();ringGain.gain.value=1;ringOsc=ac.createOscillator();ringOsc.frequency.value=180;
  ringDepth=ac.createGain();ringDepth.gain.value=0;ringOsc.connect(ringDepth);ringDepth.connect(ringGain.gain);ringOsc.start();
  delayNode=ac.createDelay(1.2);delayNode.delayTime.value=0.28;delayLpf=ac.createBiquadFilter();delayLpf.type="lowpass";delayLpf.frequency.value=3800;
  delayFb=ac.createGain();delayFb.gain.value=0;delayWet=ac.createGain();delayWet.gain.value=0;dryGain=ac.createGain();dryGain.gain.value=1;
  postFilterBus.connect(ringGain);ringGain.connect(dryGain);dryGain.connect(masterGain);
  ringGain.connect(delayNode);delayNode.connect(delayLpf);delayLpf.connect(delayFb);delayFb.connect(delayNode);delayLpf.connect(delayWet);delayWet.connect(masterGain);
  for(let b=0;b<NUM_BANKS;b++)for(let p=0;p<NUM_PADS;p++){
    const ch=banks[b][p];ch.gainNode=ac.createGain();ch.panNode=ac.createStereoPanner();ch.analyser=ac.createAnalyser();ch.analyser.fftSize=256;
    ch.fxOut=ac.createGain();ch.dryOut=ac.createGain();
    ch.gainNode.connect(ch.panNode);ch.panNode.connect(ch.analyser);ch.panNode.connect(ch.fxOut);ch.panNode.connect(ch.dryOut);
    ch.fxOut.connect(fxInput);ch.dryOut.connect(masterGain);
  }
  updateAllMixerNodes();applyFxRealtime();buildFactoryKitBuffers();
}
function finishResampleCapture(){
  const tgt=resampleTarget,frames=resampleFrames,chL=resampleChunksL,chR=resampleChunksR;
  resampleState=null;resampleTarget=null;resampleChunksL=[];resampleChunksR=[];resampleFrames=0;syncPadVisuals();
  if(!tgt||frames<64){hud.innerHTML="<b>RESAMPLE CANCELLED:</b> NO AUDIO CAPTURED";return;}
  const fL=new Float32Array(frames),fR=new Float32Array(frames);let off=0;
  for(let i=0;i<chL.length;i++){fL.set(chL[i],off);fR.set(chR[i],off);off+=chL[i].length;}
  let eIdx=frames-1;while(eIdx>64&&Math.abs(fL[eIdx])<0.0008&&Math.abs(fR[eIdx])<0.0008)eIdx--;
  const fLen=Math.min(frames,eIdx+64),nb=ac.createBuffer(2,fLen,ac.sampleRate);
  nb.getChannelData(0).set(fL.subarray(0,fLen));nb.getChannelData(1).set(fR.subarray(0,fLen));
  const rName=`録音 RESAMP_${String(resampleIdx++).padStart(2,"0")}`;
  if(!folderTree.folders["RESAMPLED"])folderTree.folders["RESAMPLED"]={name:"RESAMPLED",folders:{},files:[]};
  const sid="smp_"+(sampleIdCounter++),en={id:sid,name:`${rName}.wav`,buffer:nb};
  sampleRegistry.set(sid,en);folderTree.folders["RESAMPLED"].files.push(en);renderSampleTree();
  assignBufferToPad(tgt.bank,tgt.pad,nb,rName);
  hud.innerHTML=`<b>RESAMPLED</b> → BANK ${BANK_NAMES[tgt.bank]} PAD ${tgt.pad+1} [<b>${rName}</b> · ${nb.duration.toFixed(3)}s]`;
}
function updateAllMixerNodes(){
  if(!ac)return;const now=ac.currentTime;
  for(let b=0;b<NUM_BANKS;b++){
    const anySolo=banks[b].some(c=>c.solo);
    for(let p=0;p<NUM_PADS;p++){
      const ch=banks[b][p];if(!ch.gainNode)continue;
      ch.gainNode.gain.setTargetAtTime((anySolo?ch.solo:!ch.mute)?ch.vol:0,now,0.012);
      ch.panNode.pan.setTargetAtTime(ch.pan,now,0.012);
      ch.fxOut.gain.setTargetAtTime(ch.fxSend?1:0,now,0.012);ch.dryOut.gain.setTargetAtTime(ch.fxSend?0:1,now,0.012);
    }
  }
}
function applyFxRealtime(){
  if(!ac)return;const now=ac.currentTime,tau=0.02,isL=activeFx==="filter1",isH=activeFx==="filter2",isR=activeFx==="ringmod",isD=activeFx==="delay";
  thruGain.gain.setTargetAtTime((!isL&&!isH)?1:0,now,tau);lpfWet.gain.setTargetAtTime(isL?1:0,now,tau);hpfWet.gain.setTargetAtTime(isH?1:0,now,tau);
  if(isL)lpfNode.frequency.setTargetAtTime(Math.min(ac.sampleRate*0.42,95*Math.pow(145,ctrlVal)),now,0.025);
  if(isH)hpfNode.frequency.setTargetAtTime(Math.min(ac.sampleRate*0.42,65*Math.pow(110,ctrlVal)),now,0.025);
  ringGain.gain.setTargetAtTime(isR?0.5:1,now,tau);ringDepth.gain.setTargetAtTime(isR?0.5:0,now,tau);
  if(isR)ringOsc.frequency.setTargetAtTime(40+ctrlVal*900,now,0.02);
  delayWet.gain.setTargetAtTime(isD?0.68:0,now,0.03);delayFb.gain.setTargetAtTime(isD?(0.32+ctrlVal*0.46):0,now,0.03);
  if(isD)delayNode.delayTime.setTargetAtTime(0.06+ctrlVal*0.64,now,0.14);
  for(let b=0;b<NUM_BANKS;b++)for(let p=0;p<NUM_PADS;p++){const ch=banks[b][p];if(ch.activeVoice){const r=getEffectivePadRate(ch);if(Math.abs(ch.activeVoice.rate-r)>0.0001){ch.activeVoice.rate=r;ch.activeVoice.src.playbackRate.setTargetAtTime(r,now,0.015);}}}
  if(curPadObj().fxSend)showPadBpmOnDisplay(curPadObj());
}

// DSP SYNTHESIS: JP FACTORY KIT + SOVIET PROCEDURAL DRUMS
function synthSampleBuffer(type){
  const sr=ac.sampleRate,durs={kick:.48,snare:.36,ch:.11,oh:.44,clap:.31,bass:.62,chord:1.15,perc:.22,sov_kick:.46,sov_snare:.34,sov_ch:.10,sov_oh:.42,sov_tom:.38,sov_bass:.58,sov_bell:.52,sov_zap:.26};
  const len=Math.floor(sr*(durs[type]||.3)),buf=ac.createBuffer(2,len,sr),L=buf.getChannelData(0),R=buf.getChannelData(1);
  let seed=1337,lp1=0,lp2=0,hp1=0;
  const rnd=()=>{seed=(seed*16807)%2147483647;return(seed-1)/1073741823.5-1;},mr=[205.3,304.4,369.6,522.7,540,800];
  for(let i=0;i<len;i++){
    const t=i/sr;let vL=0,vR=0;
    if(type==="kick"){const f=175*Math.exp(-t*34)+48*Math.exp(-t*2.4)+36,ck=Math.sin(2*Math.PI*1450*t)*Math.exp(-t*220)*0.45;vL=vR=Math.tanh((Math.sin(2*Math.PI*f*t)*Math.exp(-t*6.2)*2.3+ck)*1.35);}
    else if(type==="snare"){const s1=Math.sin(2*Math.PI*(228*Math.exp(-t*26)+168)*t)*Math.exp(-t*18)*0.68,s2=Math.sin(2*Math.PI*(342*Math.exp(-t*22)+245)*t)*Math.exp(-t*24)*0.34,n=rnd();hp1=0.82*(hp1+n-lp1);lp1=n;const w=hp1*Math.exp(-t*13.5)*0.92,sn=Math.tanh((s1+s2+w)*1.55);vL=sn;vR=sn*0.97+w*0.06;}
    else if(type==="ch"){let m=0;for(let k=0;k<6;k++)m+=Math.sign(Math.sin(2*Math.PI*mr[k]*1.04*t));m/=6;hp1=0.88*(hp1+m-lp1);lp1=m;vL=vR=Math.tanh(hp1*1.8)*Math.exp(-t*54)*0.72;}
    else if(type==="oh"){let m=0;for(let k=0;k<6;k++)m+=Math.sin(2*Math.PI*mr[k]*1.02*t+0.6*Math.sin(2*Math.PI*mr[(k+2)%6]*t));m/=6;hp1=0.86*(hp1+m-lp1);lp1=m;const e=(1-Math.exp(-t*180))*Math.exp(-t*7.8);vL=hp1*e*0.72;vR=(hp1*0.92+m*0.14)*e*0.72;}
    else if(type==="clap"){const n=rnd();lp1+=0.34*(n-lp1);const bp=n-lp1,bu=t<0.011?1:(t>0.019&&t<0.031?0.92:(t>0.039&&t<0.052?0.85:(t>0.058?Math.exp(-(t-0.058)*15.5)*0.78:0.12)));vL=Math.tanh(bp*bu*2.3)*0.85;vR=Math.tanh((bp*0.9+n*0.15)*bu*2.3)*0.85;}
    else if(type==="bass"){const f=55*(1+0.12*Math.exp(-t*35));vL=vR=Math.tanh((Math.sin(2*Math.PI*f*t)+Math.sin(4*Math.PI*f*t)*0.28*Math.exp(-t*4))*2.6)*Math.exp(-t*3.1)*(1-Math.exp(-t*240));}
    else if(type==="chord"){const fs=[174.61,207.65,261.63,311.13,392];let sL=0,sR=0;fs.forEach((f,idx)=>{const d=idx%2===0?1.0025:0.9975,b=Math.sin(2*Math.PI*f*4*t)*Math.exp(-t*16)*0.22;sL+=Math.sin(2*Math.PI*f*t)+b;sR+=Math.sin(2*Math.PI*f*d*t)+b;});const e=(1-Math.exp(-t*110))*Math.exp(-t*1.85);vL=Math.tanh((sL/3.4)*1.35)*e;vR=Math.tanh((sR/3.4)*1.35)*e;}
    else if(type==="perc"){const f1=540*Math.exp(-t*28)+390,f2=895*Math.exp(-t*35)+640;vL=vR=Math.tanh((Math.sin(2*Math.PI*f1*t)*0.7+Math.sin(2*Math.PI*f2*t)*0.45)*Math.exp(-t*26)*1.7)*0.85;}
    else if(type==="sov_kick"){const f=210*Math.exp(-t*38)+52*Math.exp(-t*3.2)+38;vL=vR=Math.tanh((Math.sin(2*Math.PI*f*t)+0.25*Math.sin(4*Math.PI*f*t)*Math.exp(-t*18))*3.1)*Math.exp(-t*6.8);}
    else if(type==="sov_snare"){const o1=Math.sin(2*Math.PI*(265*Math.exp(-t*30)+172)*t)*Math.exp(-t*19)*0.65,o2=Math.sin(2*Math.PI*(412*Math.exp(-t*26)+268)*t)*Math.exp(-t*25)*0.45,n=rnd();lp1+=0.42*(n-lp1);const g=Math.tanh((n-lp1)*2.4)*Math.exp(-t*12.5)*0.88;vL=Math.tanh((o1+o2+g)*1.65);vR=Math.tanh((o1*0.95+o2*1.05+g*0.92)*1.65);}
    else if(type==="sov_ch"){const bt=((Math.floor(t*14800)*1103515245)&1)?1:-1,rg=Math.sign(Math.sin(2*Math.PI*3120*t)*Math.sin(2*Math.PI*4790*t)),x=bt*0.6+rg*0.4;hp1=0.85*(hp1+x-lp1);lp1=x;vL=vR=Math.tanh(hp1*1.9)*Math.exp(-t*62)*0.74;}
    else if(type==="sov_oh"){const bt=((Math.floor(t*13200)*1664525)&1)?1:-1,rg=Math.sin(2*Math.PI*2890*t)*Math.sin(2*Math.PI*4410*t),x=bt*0.5+rg*0.5;hp1=0.83*(hp1+x-lp1);lp1=x;const e=(1-Math.exp(-t*140))*Math.exp(-t*7.2);vL=hp1*e*0.72;vR=rg*e*0.65;}
    else if(type==="sov_tom"){const f=195*Math.exp(-t*11.5)+74;vL=vR=Math.tanh((Math.sin(2*Math.PI*f*t)+0.18*Math.sin(6*Math.PI*f*t)*Math.exp(-t*14))*2.1)*Math.exp(-t*7.5);}
    else if(type==="sov_bass"){const f=49,raw=(2*((t*f)%1)-1+2*((t*f*1.006)%1)-1)*0.5,co=0.06+0.32*Math.exp(-t*8.5);lp1+=co*(raw-lp1);lp2+=co*(lp1-lp2);vL=vR=Math.tanh(lp2*3.4)*Math.exp(-t*3.2)*(1-Math.exp(-t*180));}
    else if(type==="sov_bell"){const m=Math.sin(2*Math.PI*845*t)*1.8*Math.exp(-t*9),e=Math.exp(-t*5.6);vL=Math.tanh(Math.sin(2*Math.PI*562*t+m)*e*1.8)*0.78;vR=Math.tanh(Math.sin(2*Math.PI*565*t+m)*e*1.8)*0.78;}
    else if(type==="sov_zap"){const f=1680*Math.exp(-t*29)+95;vL=vR=Math.tanh((Math.sign(Math.sin(2*Math.PI*f*t))*0.45+Math.sin(2*Math.PI*f*t)*0.55)*1.7)*Math.exp(-t*16)*0.82;}
    L[i]=vL;R[i]=vR;
  }
  return buf;
}
function buildFactoryKitBuffers(){
  [["kick","snare","ch","oh","clap","bass","chord","perc"],["sov_kick","sov_snare","sov_ch","sov_oh","sov_tom","sov_bass","sov_bell","sov_zap"]].forEach((arr,b)=>{
    arr.forEach((t,i)=>{const buf=synthSampleBuffer(t),pad=banks[b][i];if(!pad.buffer){pad.buffer=buf;pad.cache={};}sampleRegistry.forEach(e=>{if(e.synthType===t&&!e.buffer)e.buffer=buf;});});
  });
  syncPadVisuals();syncWaveEditorUI();renderAllWaveCanvases();
}

// DISPLAY & BLACK BUTTONS
function updateDynamicDisplay(){
  for(let b=0;b<NUM_BANKS;b++)$(`led-bank-${b}`).classList.toggle("lit",b===currentBank);
  const pad=curPadObj();for(let g=0;g<4;g++)$(`led-grade-${g}`).classList.toggle("lit",pad.grade===g);
  $("led-mono-0").classList.toggle("lit",!pad.stereo);$("led-mono-1").classList.toggle("lit",pad.stereo);
  $("led-trig-0").classList.toggle("lit",!pad.gate);$("led-trig-1").classList.toggle("lit",pad.gate);
  $("led-loop-1").classList.toggle("lit",pad.loop);$("led-loop-0").classList.toggle("lit",!pad.loop);
  $("led-rev-0").classList.toggle("lit",!pad.reverse);$("led-rev-1").classList.toggle("lit",pad.reverse);
  const sp=GRADE_SPECS[pad.grade],sum=$("wave-mode-summary");
  if(sum)sum.textContent=`GRADE: ${sp.name} (${(sp.rate/1000).toFixed(2)}kHz / ${sp.bits}-BIT) | ${pad.stereo?"STEREO":"MONO"} | ${pad.gate?"GATE":"TRIGGER"} | ${pad.loop?"LOOP":"ONE SHOT"} | ${pad.reverse?"REVERSE":"NORMAL"}`;
}
function hotSwapVoice(bIdx,pIdx){const p=banks[bIdx][pIdx];if(!p||!p.activeVoice||!ac)return;const ph=getPlayheadNorm(p);if(ph!==null)triggerPad(bIdx,pIdx,0,false,ph,p.activeVoice.vel||1);}
$("blk-0").onclick=()=>{const p=curPadObj();p.grade=(p.grade+1)%4;updateDynamicDisplay();hotSwapVoice(currentBank,selectedPad);const s=GRADE_SPECS[p.grade];hud.innerHTML=`GRADE: <b>${s.name} (${(s.rate/1000).toFixed(2)}kHz · ${s.bits}-BIT)</b>`;};
$("blk-1").onclick=()=>{const p=curPadObj();p.stereo=!p.stereo;updateDynamicDisplay();if(p.activeVoice&&p.activeVoice.monoGain){p.activeVoice.monoGain.channelCount=p.stereo?2:1;p.activeVoice.monoGain.channelCountMode=p.stereo?"max":"explicit";}};
$("blk-2").onclick=()=>{const p=curPadObj();p.gate=!p.gate;updateDynamicDisplay();};
$("blk-3").onclick=()=>{const p=curPadObj();p.loop=!p.loop;updateDynamicDisplay();hotSwapVoice(currentBank,selectedPad);};
$("blk-4").onclick=()=>{const p=curPadObj();p.reverse=!p.reverse;updateDynamicDisplay();hotSwapVoice(currentBank,selectedPad);renderAllWaveCanvases();};

// PAD VISUALS & PLAYBACK
function syncPadVisuals(){
  const activeWaveTab=$("view-wave").classList.contains("active"),isRecSel=resampleState==="select",isRecArmed=resampleState==="armed"||resampleState==="recording";
  for(let p=0;p<NUM_PADS;p++){
    const pad=banks[currentBank][p],el=$(`pad-${p}`),playing=!!pad.activeVoice,isTgt=resampleTarget&&resampleTarget.bank===currentBank&&resampleTarget.pad===p;
    el.classList.toggle("has-sample",!!pad.buffer);el.classList.toggle("selected-pad",p===selectedPad);
    el.classList.toggle("lit",!remainMode&&!deleteMode&&!isRecSel&&playing);
    el.classList.toggle("fx-blink-blue",remainMode&&pad.fxSend);
    el.classList.toggle("del-blink",deleteMode&&deleteTargetPad!==p);el.classList.toggle("del-selected",deleteMode&&deleteTargetPad===p);
    el.classList.toggle("rec-blink",isRecSel&&!isTgt);el.classList.toggle("rec-selected",isRecSel&&isTgt);el.classList.toggle("rec-armed",isRecArmed&&isTgt);
    const sn=$(`seq-pnum-${p}`);if(sn)sn.classList.toggle("lit",playing);
  }
  $("btn-remain").classList.toggle("lit-blue",remainMode);$("btn-del").classList.toggle("lit",deleteMode);
  $("btn-rec").classList.toggle("lit",isRecSel);$("btn-rec").classList.toggle("rec-pulse",isRecArmed);
  $("btn-mark").classList.toggle("lit",truncateMode||activeWaveTab);
  $("btn-ab").classList.toggle("lit",currentBank===1);$("btn-cd").classList.toggle("lit",currentBank===3);
}
function stopPadVoice(bIdx,pIdx,when=0){const p=banks[bIdx][pIdx];if(p.activeVoice){try{p.activeVoice.src.stop(when||0);}catch{}p.activeVoice=null;if(bIdx===currentBank){syncPadVisuals();if(pIdx===selectedPad)renderAllWaveCanvases();}}}
function triggerPad(bIdx,pIdx,when=0,fromSeq=false,resumeNorm=null,vel=1.0){
  initAudio();if(ac.state==="suspended")ac.resume();
  const pad=banks[bIdx][pIdx],now=ac.currentTime,startTime=when>now?when:now,vDelay=Math.max(0,(startTime-now)*1000);
  if(pad.activeVoice){const oldV=pad.activeVoice;pad.activeVoice=null;if(resumeNorm!==null&&oldV.monoGain){oldV.monoGain.gain.setTargetAtTime(0,startTime,0.004);try{oldV.src.stop(startTime+0.015);}catch{}}else{try{oldV.src.stop(startTime);}catch{}}}
  const buf=getProcessedBuffer(pad);
  if(!buf){if(bIdx===currentBank&&!remainMode&&!deleteMode&&resampleState!=="select"){const el=$(`pad-${pIdx}`);el.classList.add("lit");setTimeout(()=>{if(!pad.activeVoice)syncPadVisuals();},140);}return;}
  const src=ac.createBufferSource();src.buffer=buf;
  const totalDur=buf.duration,fwdS=pad.startNorm*totalDur;let fwdE=pad.endNorm*totalDur;if(fwdE-fwdS<0.01)fwdE=Math.min(totalDur,fwdS+0.01);
  const sSec=pad.reverse?Math.max(0,totalDur-fwdE):fwdS,eSec=pad.reverse?Math.min(totalDur,totalDur-fwdS):fwdE,segDur=Math.max(0.01,eSec-sSec),rate=getEffectivePadRate(pad);
  src.playbackRate.setValueAtTime(rate,startTime);
  const doLoop=pad.loop||holdOn;src.loop=doLoop;if(doLoop){src.loopStart=sSec;src.loopEnd=eSec;}
  const mg=ac.createGain();mg.channelCount=pad.stereo?2:1;mg.channelCountMode=pad.stereo?"max":"explicit";
  const vGain=Math.max(0.05,Math.min(1.0,vel));
  if(resumeNorm!==null){mg.gain.setValueAtTime(0,startTime);mg.gain.setTargetAtTime(vGain,startTime,0.004);}else mg.gain.setValueAtTime(vGain,startTime);
  src.connect(mg);mg.connect(pad.gainNode);
  let offsetSec=sSec,playDur=segDur;
  if(resumeNorm!==null){const cl=Math.max(pad.startNorm,Math.min(pad.endNorm,resumeNorm));offsetSec=pad.reverse?Math.max(sSec,Math.min(eSec-0.005,totalDur-cl*totalDur)):Math.max(sSec,Math.min(eSec-0.005,cl*totalDur));playDur=Math.max(0.01,eSec-offsetSec);}
  const vo={src,monoGain:mg,vel:vGain,startTime:startTime-((offsetSec-sSec)/rate),fwdStartSec:fwdS,fwdEndSec:fwdE,segDur,totalDur,rate,doLoop,reverse:pad.reverse};
  pad.activeVoice=vo;
  if(doLoop)src.start(startTime,offsetSec);
  else if(fromSeq&&pad.gate)src.start(startTime,offsetSec,Math.min(playDur/rate,getStepDuration(currentStep))*rate);
  else src.start(startTime,offsetSec,playDur);
  if(bIdx===currentBank){if(vDelay<4)syncPadVisuals();else setTimeout(()=>{if(pad.activeVoice===vo)syncPadVisuals();},vDelay);}
  src.onended=()=>{if(pad.activeVoice===vo){pad.activeVoice=null;if(bIdx===currentBank){syncPadVisuals();if(pIdx===selectedPad)renderAllWaveCanvases();}}};
}
function getPlayheadNorm(pad){const v=pad&&pad.activeVoice;if(!v||!ac)return null;const el=(ac.currentTime-v.startTime)*v.rate;if(el<0||(!v.doLoop&&el>v.segDur))return null;const pos=v.doLoop?(el%v.segDur):el;return Math.max(0,Math.min(1,(v.reverse?(v.fwdEndSec-pos):(v.fwdStartSec+pos))/v.totalDur));}

// PANIC, BANKS, MODES
function stopAudition(){if(auditionSource){try{auditionSource.stop();}catch{}auditionSource=null;}if(auditionEl){auditionEl.classList.remove("auditioning");auditionEl=null;}}
function panicKillAll(){
  stopTransport();stopAudition();
  if(deleteMode||truncateMode){deleteMode=false;truncateMode=false;deleteTargetPad=null;}
  if(resampleState){resampleState=null;resampleTarget=null;resampleChunksL=[];resampleChunksR=[];resampleFrames=0;}
  for(let b=0;b<NUM_BANKS;b++)for(let p=0;p<NUM_PADS;p++)if(banks[b][p].activeVoice){try{banks[b][p].activeVoice.src.stop();}catch{}banks[b][p].activeVoice=null;}
  if(ac&&delayFb&&delayWet){const n=ac.currentTime;delayFb.gain.cancelScheduledValues(n);delayWet.gain.cancelScheduledValues(n);delayFb.gain.setValueAtTime(0,n);delayWet.gain.setValueAtTime(0,n);if(activeFx==="delay")setTimeout(()=>{if(activeFx==="delay")applyFxRealtime();},130);}
  syncPadVisuals();drawSevenSegDisplay(bpm);renderAllWaveCanvases();
  const c=$("btn-cancel");c.classList.add("lit");setTimeout(()=>c.classList.remove("lit"),180);
  hud.innerHTML="<b>CANCEL // PANIC KILL</b> — ALL AUDIO STOPPED";
}
function switchBank(nb){
  currentBank=nb;deleteMode=false;truncateMode=false;deleteTargetPad=null;
  document.querySelectorAll("#bank-selector [data-bank]").forEach(b=>b.classList.toggle("active",+b.dataset.bank===currentBank));
  ["seq-bank-lbl","mix-bank-lbl","arr-bank-lbl","drawer-bank-lbl"].forEach(id=>$(id).textContent=BANK_NAMES[currentBank]);
  updateDynamicDisplay();refreshAllBankUI();syncPadVisuals();syncWaveEditorUI();renderAllWaveCanvases();
}
$("btn-ab").onclick=()=>switchBank(currentBank===0?1:0);
$("btn-cd").onclick=()=>switchBank(currentBank===2?3:2);
document.querySelectorAll("#bank-selector [data-bank]").forEach(b=>b.onclick=()=>switchBank(+b.dataset.bank));

$("btn-rec").onclick=()=>{
  initAudio();if(ac.state==="suspended")ac.resume();
  if(remainMode)remainMode=false;if(deleteMode||truncateMode){deleteMode=false;truncateMode=false;deleteTargetPad=null;}
  if(resampleState===null){resampleState="select";resampleTarget={bank:currentBank,pad:selectedPad};syncPadVisuals();hud.innerHTML=`<b>RESAMPLE TARGET:</b> BANK ${BANK_NAMES[currentBank]} PAD ${selectedPad+1} — CLICK PAD OR PRESS <b>REC</b> TO ARM`;return;}
  if(resampleState==="select"){if(!resampleTarget)resampleTarget={bank:currentBank,pad:selectedPad};resampleState="armed";resampleChunksL=[];resampleChunksR=[];resampleFrames=0;syncPadVisuals();hud.innerHTML=`<b>RESAMPLE ARMED</b> → BANK ${BANK_NAMES[resampleTarget.bank]} PAD ${resampleTarget.pad+1} — WAITING FOR PAD OR SEQ...`;return;}
  if(resampleState==="armed"){resampleState=null;resampleTarget=null;syncPadVisuals();hud.innerHTML="<b>RESAMPLE DISARMED</b>";return;}
  if(resampleState==="recording")finishResampleCapture();
};
$("btn-del").onclick=()=>{
  if(remainMode)remainMode=false;if(resampleState){resampleState=null;resampleTarget=null;resampleChunksL=[];resampleChunksR=[];resampleFrames=0;}
  if(!deleteMode){deleteMode=true;truncateMode=false;deleteTargetPad=null;syncPadVisuals();hud.innerHTML="<b>DELETE ARMED:</b> CLICK PAD + <b>DEL</b> TO ERASE · OR PRESS <b>MARK</b> TO TRUNCATE";return;}
  if(truncateMode){const t=deleteTargetPad!==null?deleteTargetPad:selectedPad;deleteMode=false;truncateMode=false;deleteTargetPad=null;truncatePadSample(currentBank,t);syncPadVisuals();return;}
  if(deleteTargetPad!==null){const p=banks[currentBank][deleteTargetPad];stopPadVoice(currentBank,deleteTargetPad);Object.assign(p,{buffer:null,cache:{},startNorm:0,endNorm:1,loopBeats:null,waveZoom:1,waveScroll:0,pitch:1.0,name:`空き EMPTY ${BANK_NAMES[currentBank]}${deleteTargetPad+1}`});deleteMode=false;truncateMode=false;deleteTargetPad=null;refreshAllBankUI();syncPadVisuals();syncWaveEditorUI();renderAllWaveCanvases();}
  else{deleteMode=false;truncateMode=false;syncPadVisuals();}
};
$("btn-remain").onclick=()=>{if(deleteMode||truncateMode){deleteMode=false;truncateMode=false;deleteTargetPad=null;}if(resampleState){resampleState=null;resampleTarget=null;}remainMode=!remainMode;syncPadVisuals();};
function switchTab(t){
  document.querySelectorAll("[data-tab]").forEach(b=>b.classList.toggle("active",b.dataset.tab===t));
  document.querySelectorAll(".view-panel").forEach(v=>v.classList.toggle("active",v.id===`view-${t}`));
  syncPadVisuals();if(t==="wave"){syncWaveEditorUI();showPadBpmOnDisplay(curPadObj());requestAnimationFrame(renderAllWaveCanvases);}
}
$("btn-mark").onclick=()=>{
  if(deleteMode){truncateMode=!truncateMode;deleteTargetPad=truncateMode?(deleteTargetPad!==null?deleteTargetPad:selectedPad):null;syncPadVisuals();
    hud.innerHTML=truncateMode?`<b>TRUNCATE ARMED:</b> BANK ${BANK_NAMES[currentBank]} PAD ${deleteTargetPad+1} (${banks[currentBank][deleteTargetPad].name}) — PRESS <b>DEL</b> TO TRUNCATE`:"<b>DELETE ARMED:</b> CLICK PAD + <b>DEL</b> TO ERASE · OR PRESS <b>MARK</b> TO TRUNCATE";return;}
  switchTab("wave");
};
document.querySelectorAll("[data-tab]").forEach(b=>b.onclick=()=>switchTab(b.dataset.tab));

function assignBufferToPad(bIdx,pIdx,buf,name){
  const pad=banks[bIdx][pIdx];
  Object.assign(pad,{buffer:buf,cache:{},startNorm:0,endNorm:1,loopBeats:null,waveZoom:1,waveScroll:0,pitch:1.0,name:name.replace(/\.[^.]+$/,"").slice(0,16).toUpperCase()});
  selectedPad=pIdx;refreshAllBankUI();syncPadVisuals();syncWaveEditorUI();showPadBpmOnDisplay(pad);renderAllWaveCanvases();triggerPad(bIdx,pIdx);
  const info=detectLoopBpm(pad);hud.innerHTML=`LOADED <b>${name}</b> → ${BANK_NAMES[bIdx]}${pIdx+1}${info?` // <b>${info.padBpm.toFixed(2)} BPM (${info.beats}B)</b>`:""}`;
}
document.querySelectorAll(".pad").forEach(el=>{
  const idx=+el.dataset.pad;
  el.addEventListener("mousedown",()=>{
    selectedPad=idx;const pad=banks[currentBank][idx];updateDynamicDisplay();syncWaveEditorUI();
    if(resampleState==="select"){resampleTarget={bank:currentBank,pad:idx};syncPadVisuals();hud.innerHTML=`<b>RESAMPLE TARGET:</b> BANK ${BANK_NAMES[currentBank]} PAD ${idx+1} (${pad.name}) — PRESS <b>REC</b> AGAIN TO ARM`;return;}
    if(deleteMode){deleteTargetPad=idx;syncPadVisuals();hud.innerHTML=truncateMode?`<b>TRUNCATE ARMED:</b> BANK ${BANK_NAMES[currentBank]} PAD ${idx+1} (${pad.name}) — PRESS <b>DEL</b> TO TRUNCATE`:`<b>DELETE TARGET:</b> BANK ${BANK_NAMES[currentBank]} PAD ${idx+1} — PRESS <b>DEL</b> TO ERASE OR <b>MARK</b> TO TRUNCATE`;return;}
    if(remainMode){pad.fxSend=!pad.fxSend;updateAllMixerNodes();applyFxRealtime();syncPadVisuals();refreshMixerUI();return;}
    triggerPad(currentBank,idx);showPadBpmOnDisplay(pad);renderAllWaveCanvases();
  });
  const rel=()=>{if(!remainMode&&!deleteMode&&resampleState!=="select"&&banks[currentBank][idx].gate&&!holdOn)stopPadVoice(currentBank,idx);};
  el.addEventListener("mouseup",rel);el.addEventListener("mouseleave",rel);
  el.addEventListener("dragenter",e=>{e.preventDefault();el.classList.add("drag-over");});
  el.addEventListener("dragover",e=>{e.preventDefault();e.dataTransfer.dropEffect="copy";el.classList.add("drag-over");});
  el.addEventListener("dragleave",()=>el.classList.remove("drag-over"));
  el.addEventListener("drop",async e=>{
    e.preventDefault();e.stopPropagation();el.classList.remove("drag-over");initAudio();
    const sid=draggingSampleId||e.dataTransfer.getData("text/plain");
    if(sid&&sampleRegistry.has(sid)){const en=sampleRegistry.get(sid);draggingSampleId=null;const b=await resolveSampleBuffer(en);if(b)assignBufferToPad(currentBank,idx,b,en.name);return;}
    const f=e.dataTransfer.files&&e.dataTransfer.files[0];if(f)assignBufferToPad(currentBank,idx,await ac.decodeAudioData(await f.arrayBuffer()),f.name);
  });
});

// WAVE EDITOR & FILE MENU
const miniCanvas=$("mini-wave-canvas"),miniCtx=miniCanvas.getContext("2d"),waveCanvas=$("wave-canvas"),waveCtx=waveCanvas.getContext("2d"),rngStart=$("rng-start"),rngEnd=$("rng-end"),rngPitch=$("rng-pitch");
const fmtZoom=z=>z>=10?`${Math.round(z)}x`:`${Math.round(z*10)/10}x`;
function setWaveZoom(nz,anchor=0.5){const p=curPadObj(),mz=getMaxZoomForPad(p),oS=1/p.waveZoom,cz=Math.max(1,Math.min(mz,nz)),nS=1/cz;p.waveZoom=cz;p.waveScroll=Math.max(0,Math.min(1-nS,p.waveScroll+anchor*oS-anchor*nS));$("lbl-zoom").textContent=fmtZoom(p.waveZoom);renderAllWaveCanvases();}
function resetPadZoom(p=curPadObj()){if(!p)return;p.waveZoom=1;p.waveScroll=0;if(p===curPadObj()&&$("lbl-zoom"))$("lbl-zoom").textContent="1x";}
function syncWaveEditorUI(){
  const p=curPadObj(),dur=p.buffer?p.buffer.duration:0,semi=rateToSemi(p.pitch),mz=getMaxZoomForPad(p);
  p.waveZoom=Math.max(1,Math.min(mz,p.waveZoom||1));p.waveScroll=Math.max(0,Math.min(1-1/p.waveZoom,p.waveScroll||0));
  $("lbl-zoom").textContent=fmtZoom(p.waveZoom);$("wave-pad-lbl").textContent=`BANK ${BANK_NAMES[currentBank]} · PAD ${selectedPad+1} [${p.name}]`;
  rngStart.value=p.startNorm;rngEnd.value=p.endNorm;rngPitch.value=semi.toFixed(2);
  $("lbl-pad-pitch").textContent=`${semi>=0?"+":""}${semi.toFixed(2)} st`;$("lbl-start-ms").textContent=(p.startNorm*dur).toFixed(3)+" s";$("lbl-end-ms").textContent=(p.endNorm*dur).toFixed(3)+" s";
  const info=detectLoopBpm(p);
  if(info){if(document.activeElement!==waveBpmInp)waveBpmInp.value=fmtBpm(info.padBpm);waveBpmInp.disabled=false;btnWaveBeats.textContent=`${info.beats}B`;}
  else{waveBpmInp.value="";waveBpmInp.disabled=true;btnWaveBeats.textContent="--";}
  updateDynamicDisplay();
}
function drawMiniWave(){
  const wrap=$("mini-wave-wrap");if(!wrap||!wrap.clientWidth)return;
  const dpr=window.devicePixelRatio||1,w=wrap.clientWidth,h=wrap.clientHeight;
  if(miniCanvas.width!==Math.floor(w*dpr)||miniCanvas.height!==Math.floor(h*dpr)){miniCanvas.width=Math.floor(w*dpr);miniCanvas.height=Math.floor(h*dpr);}
  miniCtx.setTransform(dpr,0,0,dpr,0,0);miniCtx.fillStyle="#090b0e";miniCtx.fillRect(0,0,w,h);
  const p=curPadObj();if(!p.buffer)return;
  const data=p.buffer.getChannelData(0),step=Math.max(1,Math.floor(data.length/w));
  miniCtx.strokeStyle="rgba(224,90,71,0.72)";miniCtx.lineWidth=1;miniCtx.beginPath();
  for(let x=0;x<w;x++){const idx=Math.floor((x/w)*data.length);let mn=1,mx=-1;for(let k=0;k<step&&idx+k<data.length;k++){const v=data[idx+k];if(v<mn)mn=v;if(v>mx)mx=v;}miniCtx.moveTo(x,(1-mx)*0.5*h);miniCtx.lineTo(x,(1-mn)*0.5*h);}
  miniCtx.stroke();
  const sx=p.startNorm*w,ex=p.endNorm*w;miniCtx.fillStyle="rgba(0,0,0,0.55)";miniCtx.fillRect(0,0,sx,h);miniCtx.fillRect(ex,0,w-ex,h);
  miniCtx.fillStyle="#4dff91";miniCtx.fillRect(sx,0,1.5,h);miniCtx.fillStyle="#ff3850";miniCtx.fillRect(ex-1.5,0,1.5,h);
  const vx=p.waveScroll*w,vw=Math.max(6,(1/p.waveZoom)*w);miniCtx.fillStyle="rgba(255,255,255,0.14)";miniCtx.fillRect(vx,0,vw,h);
  miniCtx.strokeStyle="rgba(255,195,140,0.9)";miniCtx.lineWidth=1.5;miniCtx.strokeRect(vx+0.75,0.75,vw-1.5,h-1.5);
  const ph=getPlayheadNorm(p);if(ph!==null){miniCtx.strokeStyle="#fff";miniCtx.beginPath();miniCtx.moveTo(ph*w,0);miniCtx.lineTo(ph*w,h);miniCtx.stroke();}
}
function drawWaveform(){
  const wrap=$("wave-wrap");if(!wrap||!wrap.clientWidth)return;
  const dpr=window.devicePixelRatio||1,w=wrap.clientWidth,h=wrap.clientHeight;
  if(waveCanvas.width!==Math.floor(w*dpr)||waveCanvas.height!==Math.floor(h*dpr)){waveCanvas.width=Math.floor(w*dpr);waveCanvas.height=Math.floor(h*dpr);}
  waveCtx.setTransform(dpr,0,0,dpr,0,0);waveCtx.fillStyle="#0b0d11";waveCtx.fillRect(0,0,w,h);
  waveCtx.strokeStyle="rgba(255,255,255,0.05)";waveCtx.lineWidth=1;waveCtx.beginPath();waveCtx.moveTo(0,h/2);waveCtx.lineTo(w,h/2);
  for(let i=1;i<8;i++){waveCtx.moveTo((w/8)*i,0);waveCtx.lineTo((w/8)*i,h);}waveCtx.stroke();
  const p=curPadObj();
  if(!p.buffer){waveCtx.fillStyle="#6d727b";waveCtx.font="bold 12px Courier New";waveCtx.textAlign="center";waveCtx.fillText("NO SAMPLE LOADED — DRAG AUDIO ONTO PAD",w/2,h/2+4);return;}
  const vS=p.waveScroll,vSpan=1/p.waveZoom,vE=Math.min(1,vS+vSpan),n2x=n=>((n-vS)/vSpan)*w;
  const data=p.buffer.getChannelData(0),sS=Math.floor(vS*data.length),eS=Math.floor(vE*data.length),vis=Math.max(1,eS-sS),step=Math.max(1,Math.floor(vis/w));
  const sx=n2x(p.startNorm),ex=n2x(p.endNorm);
  waveCtx.fillStyle="rgba(0,0,0,0.55)";if(sx>0)waveCtx.fillRect(0,0,Math.min(w,sx),h);if(ex<w)waveCtx.fillRect(Math.max(0,ex),0,w-Math.max(0,ex),h);
  const aL=Math.max(0,sx),aR=Math.min(w,ex);if(aR>aL){waveCtx.fillStyle="rgba(224,90,71,0.08)";waveCtx.fillRect(aL,0,aR-aL,h);}
  waveCtx.strokeStyle="#e05a47";waveCtx.lineWidth=1.25;waveCtx.beginPath();
  for(let x=0;x<w;x++){const idx=sS+Math.floor((x/w)*vis);let mn=1,mx=-1;for(let k=0;k<step&&idx+k<data.length;k++){const v=data[idx+k];if(v<mn)mn=v;if(v>mx)mx=v;}waveCtx.moveTo(x,(1-mx)*0.5*h);waveCtx.lineTo(x,(1-mn)*0.5*h);}
  waveCtx.stroke();
  if(sx>=-4&&sx<=w+4){waveCtx.strokeStyle="#4dff91";waveCtx.lineWidth=2;waveCtx.beginPath();waveCtx.moveTo(sx,0);waveCtx.lineTo(sx,h);waveCtx.stroke();waveCtx.fillStyle="#4dff91";waveCtx.fillRect(sx,0,36,15);waveCtx.fillStyle="#08120c";waveCtx.font="bold 9px Courier New";waveCtx.textAlign="left";waveCtx.fillText("START",sx+4,10);}
  if(ex>=-4&&ex<=w+4){waveCtx.strokeStyle="#ff3850";waveCtx.lineWidth=2;waveCtx.beginPath();waveCtx.moveTo(ex,0);waveCtx.lineTo(ex,h);waveCtx.stroke();waveCtx.fillStyle="#ff3850";waveCtx.fillRect(Math.max(0,ex-28),h-15,28,15);waveCtx.fillStyle="#fff";waveCtx.font="bold 9px Courier New";waveCtx.textAlign="left";waveCtx.fillText("END",Math.max(4,ex-23),h-5);}
  const ph=getPlayheadNorm(p);if(ph!==null){const px=n2x(ph);if(px>=-2&&px<=w+2){waveCtx.save();waveCtx.strokeStyle="#fff";waveCtx.shadowColor="rgba(255,220,150,.95)";waveCtx.shadowBlur=8;waveCtx.lineWidth=2;waveCtx.beginPath();waveCtx.moveTo(px,0);waveCtx.lineTo(px,h);waveCtx.stroke();waveCtx.restore();}}
}
function renderAllWaveCanvases(){if(!$("view-wave").classList.contains("active"))return;drawMiniWave();drawWaveform();}

const waveFileMenu=$("wave-file-menu"),btnWaveFileMenu=$("btn-wave-file-menu"),closeWaveMenu=()=>{waveFileMenu.classList.remove("open");btnWaveFileMenu.classList.remove("active");};
btnWaveFileMenu.onclick=e=>{e.stopPropagation();const o=waveFileMenu.classList.toggle("open");btnWaveFileMenu.classList.toggle("active",o);};
window.addEventListener("mousedown",e=>{if(!e.target.closest("#wave-file-menu-wrap"))closeWaveMenu();});
$("menu-export-fx").onclick=()=>{closeWaveMenu();exportPadWav(true);};
$("menu-export-raw").onclick=()=>{closeWaveMenu();exportPadWav(false);};
$("menu-truncate-pad").onclick=()=>{closeWaveMenu();truncatePadSample(currentBank,selectedPad);};
$("menu-reset-marks").onclick=()=>{closeWaveMenu();$("btn-wave-reset").click();};

$("btn-pad-bpm-dn").onclick=()=>stepPadBpm(-1);$("btn-pad-bpm-up").onclick=()=>stepPadBpm(1);
function commitWaveBpm(){const v=parseFloat(waveBpmInp.value);if(Number.isFinite(v)&&v>0)setPadTargetBpm(currentBank,selectedPad,v);else syncWaveEditorUI();}
waveBpmInp.addEventListener("change",commitWaveBpm);waveBpmInp.addEventListener("keydown",e=>{if(e.key==="Enter"){commitWaveBpm();waveBpmInp.blur();}});
btnWaveBeats.onclick=()=>{const p=curPadObj(),info=detectLoopBpm(p);if(!info)return;p.loopBeats=BEAT_CYCLE[(BEAT_CYCLE.indexOf(info.beats)+1)%BEAT_CYCLE.length];syncWaveEditorUI();showPadBpmOnDisplay(p);};
$("btn-match-master").onclick=()=>setPadTargetBpm(currentBank,selectedPad,bpm);
$("btn-sync-bpm").onclick=()=>{const info=detectLoopBpm(curPadObj());if(info){updateBpm(info.padBpm);hud.innerHTML=`MASTER BPM LOCKED: <b>${bpm} BPM</b>`;}};
$("btn-zoom-in").onclick=()=>setWaveZoom(curPadObj().waveZoom*2,0.5);$("btn-zoom-out").onclick=()=>setWaveZoom(curPadObj().waveZoom/2,0.5);
$("btn-zoom-fit").onclick=()=>{resetPadZoom();renderAllWaveCanvases();};
waveCanvas.addEventListener("wheel",e=>{e.preventDefault();const r=waveCanvas.getBoundingClientRect();setWaveZoom(curPadObj().waveZoom*(e.deltaY<0?1.45:1/1.45),Math.max(0,Math.min(1,(e.clientX-r.left)/r.width)));},{passive:false});
let dragMini=false,dragMark=null;
function panMini(e){const p=curPadObj(),r=miniCanvas.getBoundingClientRect(),n=Math.max(0,Math.min(1,(e.clientX-r.left)/r.width)),s=1/p.waveZoom;p.waveScroll=Math.max(0,Math.min(1-s,n-s/2));renderAllWaveCanvases();}
miniCanvas.onmousedown=e=>{dragMini=true;panMini(e);};
rngStart.oninput=()=>{const p=curPadObj();p.startNorm=Math.min(+rngStart.value,p.endNorm-getMinNormGap(p));syncWaveEditorUI();showPadBpmOnDisplay(p);renderAllWaveCanvases();};
rngEnd.oninput=()=>{const p=curPadObj();p.endNorm=Math.max(+rngEnd.value,p.startNorm+getMinNormGap(p));syncWaveEditorUI();showPadBpmOnDisplay(p);renderAllWaveCanvases();};
rngPitch.oninput=()=>setPadPitchRate(currentBank,selectedPad,semiToRate(+rngPitch.value));rngPitch.ondblclick=()=>setPadPitchRate(currentBank,selectedPad,1.0);
const cx2n=x=>{const p=curPadObj(),r=waveCanvas.getBoundingClientRect();return Math.max(0,Math.min(1,p.waveScroll+Math.max(0,Math.min(1,(x-r.left)/r.width))*(1/p.waveZoom)));};
waveCanvas.oncontextmenu=e=>e.preventDefault();
waveCanvas.onmousedown=e=>{const n=cx2n(e.clientX),p=curPadObj(),tol=0.06/p.waveZoom;dragMark=e.button===2?"end":(Math.abs(n-p.endNorm)<Math.abs(n-p.startNorm)&&Math.abs(n-p.endNorm)<tol?"end":"start");applyMark(n);};
function applyMark(n){const p=curPadObj(),mg=getMinNormGap(p);if(dragMark==="start")p.startNorm=Math.min(n,p.endNorm-mg);else p.endNorm=Math.max(n,p.startNorm+mg);syncWaveEditorUI();showPadBpmOnDisplay(p);renderAllWaveCanvases();}
window.addEventListener("mousemove",e=>{if(dragMini)panMini(e);if(dragMark)applyMark(cx2n(e.clientX));});
window.addEventListener("mouseup",()=>{dragMini=false;dragMark=null;});
$("btn-wave-audition").onclick=()=>triggerPad(currentBank,selectedPad);
$("btn-wave-reset").onclick=()=>{const p=curPadObj();p.startNorm=0;p.endNorm=1;p.loopBeats=null;setPadPitchRate(currentBank,selectedPad,1.0);resetPadZoom(p);syncWaveEditorUI();showPadBpmOnDisplay(p);renderAllWaveCanvases();};

// EXPLORER
function registerFactoryTree(){
  const addGrp=(title,items)=>{const f={name:title,folders:{},files:[]};items.forEach(([name,synthType])=>{const id="smp_"+(sampleIdCounter++),en={id,name,synthType,buffer:null};sampleRegistry.set(id,en);f.files.push(en);});folderTree.folders[title]=f;};
  addGrp("JP FACTORY KIT (和製)",[["大太鼓_Taiko_808.wav","kick"],["スネア_Snare_909.wav","snare"],["閉ハイハット_CH_606.wav","ch"],["開ハイハット_OH_606.wav","oh"],["手拍子_Clap_202.wav","clap"],["重低音_Sub_303.wav","bass"],["エレピ_Rhodes_JP.wav","chord"],["木魚_Mokugyo_Perc.wav","perc"]]);
  addGrp("SOVIET DRUM LAB (СССР)",[["БОЧКА_Lel_Kick.wav","sov_kick"],["РАБОЧИЙ_Ritm2_Snare.wav","sov_snare"],["ХЭТ-ЗАК_Formanta_CH.wav","sov_ch"],["ХЭТ-ОТК_Formanta_OH.wav","sov_oh"],["ТОМ-АЛЬТ_Elsita_Tom.wav","sov_tom"],["БАС-ГУД_Polivoks_Bass.wav","sov_bass"],["ЗВОН_Kremenchug_Bell.wav","sov_bell"],["ШУМ-УДАР_UDS_Zap.wav","sov_zap"]]);
}
function addFilesToTree(fl){
  const af=Array.from(fl).filter(f=>f.type.startsWith("audio/")||/\.(wav|mp3|ogg|flac|m4a|aif|aiff)$/i.test(f.name));
  af.forEach(file=>{const parts=(file.webkitRelativePath||("LOADED FILES/"+file.name)).split("/").filter(Boolean),name=parts.pop();let n=folderTree;parts.forEach(d=>{if(!n.folders[d])n.folders[d]={name:d,folders:{},files:[]};n=n.folders[d];});const id="smp_"+(sampleIdCounter++),en={id,name,file,buffer:null};sampleRegistry.set(id,en);n.files.push(en);});
  if(af.length){renderSampleTree();hud.innerHTML=`EXPLORER: ADDED <b>${af.length}</b> SAMPLE(S)`;}
}
async function resolveSampleBuffer(en){initAudio();if(en.buffer)return en.buffer;if(en.synthType)return en.buffer=synthSampleBuffer(en.synthType);if(en.file)return en.buffer=await ac.decodeAudioData(await en.file.arrayBuffer());return null;}
async function auditionSample(en,el){initAudio();if(ac.state==="suspended")ac.resume();stopAudition();const b=await resolveSampleBuffer(en);if(!b)return;const s=ac.createBufferSource();s.buffer=b;s.connect(masterGain);s.start();auditionSource=s;auditionEl=el;el.classList.add("auditioning");s.onended=()=>{if(auditionSource===s)stopAudition();};}
function renderTreeNode(node,cont){
  Object.values(node.folders).forEach(sub=>{const h=document.createElement("div");h.className="tree-folder-hdr";h.textContent=`▾ ${sub.name}`;const c=document.createElement("div");c.className="tree-children";h.onclick=()=>{const col=c.classList.toggle("collapsed");h.textContent=`${col?"▸":"▾"} ${sub.name}`;};cont.append(h,c);renderTreeNode(sub,c);});
  node.files.forEach(en=>{const r=document.createElement("div");r.className="tree-file";r.draggable=true;r.innerHTML=`<span class="tree-file-name">${en.name}</span><span class="tree-file-tag">DRAG</span>`;r.onclick=()=>auditionSample(en,r);r.ondragstart=e=>{draggingSampleId=en.id;e.dataTransfer.setData("text/plain",en.id);e.dataTransfer.effectAllowed="copy";};r.ondragend=()=>{draggingSampleId=null;};cont.appendChild(r);});
}
function renderSampleTree(){const w=$("sample-tree");w.innerHTML="";renderTreeNode(folderTree,w);}
(()=>{const h=$("explorer-drag-handle");let dx=0,dy=0,dr=false;h.onmousedown=e=>{if(e.target.closest(".drawer-close"))return;dr=true;const r=drawer.getBoundingClientRect();dx=e.clientX-r.left;dy=e.clientY-r.top;};window.addEventListener("mousemove",e=>{if(!dr)return;drawer.style.left=Math.max(0,Math.min(innerWidth-100,e.clientX-dx))+"px";drawer.style.top=Math.max(0,Math.min(innerHeight-60,e.clientY-dy))+"px";});window.addEventListener("mouseup",()=>{dr=false;});})();
const toggleDrawer=f=>{const o=f!==undefined?f:!drawer.classList.contains("open");drawer.classList.toggle("open",o);spExplorerBtn.classList.toggle("active",o);$("btn-open-explorer").classList.toggle("active",o);};
spExplorerBtn.onclick=()=>toggleDrawer();$("btn-open-explorer").onclick=()=>toggleDrawer();$("btn-close-drawer").onclick=()=>toggleDrawer(false);
$("btn-load-folder").onclick=()=>$("inp-folder").click();$("btn-load-files").onclick=()=>$("inp-files").click();
$("inp-folder").onchange=e=>{addFilesToTree(e.target.files);e.target.value="";};$("inp-files").onchange=e=>{addFilesToTree(e.target.files);e.target.value="";};

// SEQUENCER, MIXER, ARRANGER
const getStepDuration=s=>{const b=60/bpm/4,sw=(swingPct/100)*b*0.5;return s%2===0?b+sw:b-sw;};
function scheduleStep(step,bar,time){const pat=patterns[playMode==="song"?songBars[bar].pat:currentPat];for(let b=0;b<NUM_BANKS;b++)for(let p=0;p<NUM_PADS;p++){const v=pat[b][p][step];if(v>0&&(playMode!=="song"||songBars[bar].tracks[b][p]))triggerPad(b,p,time,true,null,v);}setTimeout(()=>{if(isPlaying)updatePlayheadUI(step,bar);},Math.max(0,(time-ac.currentTime)*1000));}
function schedulerTick(){while(nextStepTime<ac.currentTime+0.1){scheduleStep(currentStep,currentBar,nextStepTime);nextStepTime+=getStepDuration(currentStep);if(++currentStep>=NUM_STEPS){currentStep=0;if(playMode==="song")currentBar=(currentBar+1)%NUM_BARS;}}}
function startTransport(){initAudio();if(ac.state==="suspended")ac.resume();if(isPlaying)return;isPlaying=true;currentStep=0;currentBar=0;nextStepTime=ac.currentTime+0.03;schedTimer=setInterval(schedulerTick,25);$("btn-play").classList.add("lit");drawSevenSegDisplay(bpm);}
function stopTransport(){isPlaying=false;if(schedTimer){clearInterval(schedTimer);schedTimer=null;}$("btn-play").classList.remove("lit");document.querySelectorAll(".step-num.now,.step-cell.playhead,.arr-bar-pat.now,.arr-cell.now").forEach(e=>e.classList.remove("now","playhead"));stepLed.textContent="01:01";}
function updatePlayheadUI(step,bar){stepLed.textContent=`${String(bar+1).padStart(2,"0")}:${String(step+1).padStart(2,"0")}`;document.querySelectorAll(".step-num.now,.step-cell.playhead,.arr-bar-pat.now,.arr-cell.now").forEach(e=>e.classList.remove("now","playhead"));if($(`snum-${step}`))$(`snum-${step}`).classList.add("now");document.querySelectorAll(`.step-cell[data-step="${step}"]`).forEach(e=>e.classList.add("playhead"));if(playMode==="song"){if($(`arr-bp-${bar}`))$(`arr-bp-${bar}`).classList.add("now");document.querySelectorAll(`.arr-cell[data-bar="${bar}"]`).forEach(e=>e.classList.add("now"));}}
function updateVelSquareUI(p,v){const sq=$(`seq-vel-${p}`);if(!sq)return;sq.style.setProperty("--v",v);sq.querySelector("span").textContent=Math.round(v*99);}
function applyStepCellUI(c,v){c.classList.toggle("on",v>0);if(v>0)c.style.setProperty("--v",v);else c.style.removeProperty("--v");}
function buildPatternButtons(){const w=$("pat-selector");for(let i=0;i<NUM_PATS;i++){const b=document.createElement("button");b.className="hw-btn mini-btn"+(i===0?" active":"");b.textContent=`P${i+1}`;b.onclick=()=>{currentPat=i;w.querySelectorAll(".mini-btn").forEach((btn,idx)=>btn.classList.toggle("active",idx===i));$("seq-pat-label").textContent=`P${i+1}`;refreshSequencerUI();};w.appendChild(b);}}
function buildSequencerGrid(){
  const w=$("seq-grid");w.innerHTML="";const hdr=document.createElement("div");hdr.className="seq-step-nums";hdr.innerHTML="<div></div>";
  for(let s=0;s<NUM_STEPS;s++){const d=document.createElement("div");d.id=`snum-${s}`;d.className="step-num"+(s%4===0?" beat":"");d.textContent=s+1;hdr.appendChild(d);}w.appendChild(hdr);
  for(let p=0;p<NUM_PADS;p++){
    const row=document.createElement("div");row.className="seq-row";const info=document.createElement("div");info.className="seq-pad-info";
    info.innerHTML=`<span class="seq-pad-num" id="seq-pnum-${p}">A${p+1}</span><span class="seq-pad-name" id="seq-pname-${p}"></span><button class="seq-mute-mini" id="seq-mute-${p}" title="Mute">M</button><div class="seq-vel-sq" id="seq-vel-${p}" title="Drag Up/Down: Track Velocity"><span>84</span></div>`;
    info.onmousedown=e=>{if(e.target.closest(".seq-mute-mini")||e.target.closest(".seq-vel-sq"))return;selectedPad=p;updateDynamicDisplay();syncWaveEditorUI();showPadBpmOnDisplay(banks[currentBank][p]);triggerPad(currentBank,p,0,false,null,trackVel[currentBank][p]);};
    info.querySelector(".seq-mute-mini").onclick=()=>{banks[currentBank][p].mute=!banks[currentBank][p].mute;updateAllMixerNodes();refreshMixerUI();refreshSequencerUI();};
    info.querySelector(".seq-vel-sq").onmousedown=e=>{e.preventDefault();e.stopPropagation();const sy=e.clientY,sv=trackVel[currentBank][p],mv=ev=>{const nv=Math.max(0.15,Math.min(1.0,sv+(sy-ev.clientY)/95));trackVel[currentBank][p]=nv;updateVelSquareUI(p,nv);hud.innerHTML=`TRACK ${BANK_NAMES[currentBank]}${p+1} PAINT VELOCITY: <b>${Math.round(nv*100)}%</b>`;},up=()=>{window.removeEventListener("mousemove",mv);window.removeEventListener("mouseup",up);};window.addEventListener("mousemove",mv);window.addEventListener("mouseup",up);};
    row.appendChild(info);
    for(let s=0;s<NUM_STEPS;s++){
      const c=document.createElement("button");c.className="step-cell"+(s%4===0?" beat-start":"");c.dataset.pad=p;c.dataset.step=s;
      c.onmousedown=e=>{e.preventDefault();const sy=e.clientY,iV=patterns[currentPat][currentBank][p][s];let moved=false,bV=iV>0?iV:trackVel[currentBank][p];const mv=ev=>{if(!moved&&Math.abs(ev.clientY-sy)<4)return;moved=true;const nv=Math.max(0.15,Math.min(1.0,bV+(sy-ev.clientY)/90));patterns[currentPat][currentBank][p][s]=nv;trackVel[currentBank][p]=nv;applyStepCellUI(c,nv);updateVelSquareUI(p,nv);hud.innerHTML=`STEP ${s+1} (${BANK_NAMES[currentBank]}${p+1}) VELOCITY: <b>${Math.round(nv*100)}%</b>`;},up=()=>{window.removeEventListener("mousemove",mv);window.removeEventListener("mouseup",up);if(!moved){const nv=iV>0?0:trackVel[currentBank][p];patterns[currentPat][currentBank][p][s]=nv;applyStepCellUI(c,nv);if(nv>0)updateVelSquareUI(p,nv);}};window.addEventListener("mousemove",mv);window.addEventListener("mouseup",up);};
      row.appendChild(c);
    }
    w.appendChild(row);
  }
}
function refreshSequencerUI(){const bn=BANK_NAMES[currentBank],pat=patterns[currentPat][currentBank];for(let p=0;p<NUM_PADS;p++){$(`seq-pnum-${p}`).textContent=`${bn}${p+1}`;$(`seq-pname-${p}`).textContent=banks[currentBank][p].name;$(`seq-mute-${p}`).classList.toggle("muted",banks[currentBank][p].mute);updateVelSquareUI(p,trackVel[currentBank][p]);}document.querySelectorAll(".step-cell").forEach(c=>applyStepCellUI(c,pat[+c.dataset.pad][+c.dataset.step]));}
function buildMixerUI(){
  const g=$("mixer-grid");g.innerHTML="";
  for(let i=0;i<NUM_PADS;i++){
    const s=document.createElement("div");s.className="mix-strip";
    s.innerHTML=`<div class="mix-ch-id" id="mix-chid-${i}">A${i+1}</div><div class="mix-ch-name" id="mix-pname-${i}"></div><div class="mix-param"><span class="mix-param-lbl">PAN</span><input type="range" class="mix-mini-slider" id="mix-pan-${i}" min="-1" max="1" step="0.05" value="0"></div><div class="mix-param"><span class="mix-param-lbl">TUNE</span><input type="range" class="mix-mini-slider" id="mix-tune-${i}" min="0.5" max="2.0" step="0.005" value="1"></div><div class="mix-fader-area"><div class="fader-track-wrap"><input type="range" class="v-fader" id="mix-vol-${i}" min="0" max="1.2" step="0.01" value="0.85" orient="vertical"></div><div class="led-meter" id="meter-${i}"></div></div><div class="mix-btns"><button class="mix-btn" id="mix-fx-${i}">FX</button></div><div class="mix-btns"><button class="mix-btn" id="mix-m-${i}">M</button><button class="mix-btn" id="mix-s-${i}">S</button></div>`;
    g.appendChild(s);const mEl=s.querySelector(`#meter-${i}`);meterSegsUI[i]=[];for(let k=0;k<12;k++){const d=document.createElement("div");d.className="meter-seg";mEl.appendChild(d);meterSegsUI[i].push(d);}
    s.querySelector(`#mix-vol-${i}`).oninput=e=>{banks[currentBank][i].vol=+e.target.value;updateAllMixerNodes();};
    s.querySelector(`#mix-pan-${i}`).oninput=e=>{banks[currentBank][i].pan=+e.target.value;updateAllMixerNodes();};
    s.querySelector(`#mix-tune-${i}`).oninput=e=>setPadPitchRate(currentBank,i,+e.target.value);s.querySelector(`#mix-tune-${i}`).ondblclick=()=>setPadPitchRate(currentBank,i,1.0);
    s.querySelector(`#mix-fx-${i}`).onclick=()=>{banks[currentBank][i].fxSend=!banks[currentBank][i].fxSend;updateAllMixerNodes();applyFxRealtime();refreshMixerUI();syncPadVisuals();};
    s.querySelector(`#mix-m-${i}`).onclick=()=>{banks[currentBank][i].mute=!banks[currentBank][i].mute;updateAllMixerNodes();refreshMixerUI();refreshSequencerUI();};
    s.querySelector(`#mix-s-${i}`).onclick=()=>{banks[currentBank][i].solo=!banks[currentBank][i].solo;updateAllMixerNodes();refreshMixerUI();};
  }
}
function refreshMixerUI(){const bn=BANK_NAMES[currentBank];for(let i=0;i<NUM_PADS;i++){const ch=banks[currentBank][i];$(`mix-chid-${i}`).textContent=`${bn}${i+1}`;$(`mix-pname-${i}`).textContent=ch.name;$(`mix-vol-${i}`).value=ch.vol;$(`mix-pan-${i}`).value=ch.pan;$(`mix-tune-${i}`).value=ch.pitch;$(`mix-fx-${i}`).classList.toggle("fx-on",ch.fxSend);$(`mix-m-${i}`).classList.toggle("m-on",ch.mute);$(`mix-s-${i}`).classList.toggle("s-on",ch.solo);}}
function buildArrangerUI(){
  const w=$("arr-grid");w.innerHTML="";const hdr=document.createElement("div");hdr.className="arr-header-row";hdr.innerHTML=`<div style="font-size:9px;color:var(--silk-dim);padding-left:4px">BAR / PAT</div>`;
  for(let b=0;b<NUM_BARS;b++){const btn=document.createElement("button");btn.className="arr-bar-pat";btn.id=`arr-bp-${b}`;btn.textContent=`P${songBars[b].pat+1}`;btn.onclick=()=>{songBars[b].pat=(songBars[b].pat+1)%NUM_PATS;btn.textContent=`P${songBars[b].pat+1}`;};hdr.appendChild(btn);}w.appendChild(hdr);
  for(let t=0;t<NUM_PADS;t++){const row=document.createElement("div");row.className="arr-row";row.innerHTML=`<div class="arr-trk-lbl"><span id="arr-tid-${t}">A${t+1}</span><b id="arr-pname-${t}" style="font-weight:400;overflow:hidden;text-overflow:ellipsis"></b></div>`;for(let b=0;b<NUM_BARS;b++){const c=document.createElement("button");c.className="arr-cell";c.dataset.bar=b;c.dataset.track=t;c.onmousedown=()=>{const cur=songBars[b].tracks[currentBank][t];songBars[b].tracks[currentBank][t]=!cur;c.classList.toggle("on",!cur);};row.appendChild(c);}w.appendChild(row);}
}
function refreshArrangerUI(){const bn=BANK_NAMES[currentBank];for(let t=0;t<NUM_PADS;t++){$(`arr-tid-${t}`).textContent=`${bn}${t+1}`;$(`arr-pname-${t}`).textContent=banks[currentBank][t].name;}document.querySelectorAll(".arr-cell").forEach(c=>c.classList.toggle("on",songBars[+c.dataset.bar].tracks[currentBank][+c.dataset.track]));}
function refreshAllBankUI(){refreshSequencerUI();refreshMixerUI();refreshArrangerUI();}
function loadBoomBapPattern(){const pat=patterns[currentPat][currentBank];for(let p=0;p<NUM_PADS;p++)pat[p].fill(0);[[0,1],[7,.72],[10,.95]].forEach(([s,v])=>pat[0][s]=v);[[4,.95],[12,1]].forEach(([s,v])=>pat[1][s]=v);[0,2,4,6,8,10,12,14].forEach((s,i)=>pat[2][s]=i%2===0?.88:.48);pat[3][14]=.75;[[0,.92],[10,.82]].forEach(([s,v])=>pat[5][s]=v);[[0,.85],[6,.65]].forEach(([s,v])=>pat[6][s]=v);refreshSequencerUI();}

const meterBuf=new Uint8Array(128);
function uiAnimLoop(){
  if(ac){
    if($("view-mix").classList.contains("active"))for(let i=0;i<NUM_PADS;i++){const ch=banks[currentBank][i];if(!ch.analyser)continue;ch.analyser.getByteTimeDomainData(meterBuf);let pk=0;for(let k=0;k<meterBuf.length;k++){const v=Math.abs(meterBuf[k]-128)/128;if(v>pk)pk=v;}const lit=Math.min(12,Math.round(pk*16));for(let s=0;s<12;s++)meterSegsUI[i][s].className=s<lit?(s>=9?"meter-seg on-high":"meter-seg on-low"):"meter-seg";}
    if($("view-wave").classList.contains("active")&&curPadObj().activeVoice){drawMiniWave();drawWaveform();}
  }
  requestAnimationFrame(uiAnimLoop);
}

const updateBpm=v=>{const p=parseFloat(v);if(!Number.isFinite(p))return;bpm=Math.max(40,Math.min(240,Math.round(p*100)/100));rackBpmInp.value=fmtBpm(bpm);drawSevenSegDisplay(Math.round(bpm));};
$("btn-bpm-dn").onclick=()=>updateBpm(bpm-1);$("btn-bpm-up").onclick=()=>updateBpm(bpm+1);
$("rack-bpm-dn").onclick=()=>updateBpm(bpm-1);$("rack-bpm-up").onclick=()=>updateBpm(bpm+1);
rackBpmInp.onchange=()=>updateBpm(rackBpmInp.value);rackBpmInp.onkeydown=e=>{if(e.key==="Enter"){updateBpm(rackBpmInp.value);rackBpmInp.blur();}};
$("btn-tap").onclick=()=>{const n=performance.now();if(lastTap&&n-lastTap<2000)updateBpm(60000/(n-lastTap));lastTap=n;};
$("btn-play").onclick=startTransport;$("btn-stop").onclick=stopTransport;
$("btn-mode-pat").onclick=()=>{playMode="pat";$("btn-mode-pat").classList.add("active");$("btn-mode-song").classList.remove("active");};
$("btn-mode-song").onclick=()=>{playMode="song";$("btn-mode-song").classList.add("active");$("btn-mode-pat").classList.remove("active");};
$("rng-swing").oninput=e=>{swingPct=+e.target.value;$("lbl-swing").textContent=`${swingPct}%`;};
$("btn-seq-demo").onclick=loadBoomBapPattern;$("btn-seq-clear").onclick=()=>{patterns[currentPat][currentBank].forEach(r=>r.fill(0));refreshSequencerUI();};
$("btn-mix-reset").onclick=()=>{for(let i=0;i<NUM_PADS;i++)Object.assign(banks[currentBank][i],{vol:.85,pan:0,pitch:1,mute:false,solo:false});updateAllMixerNodes();applyFxRealtime();refreshMixerUI();refreshSequencerUI();syncWaveEditorUI();};
$("btn-arr-fill").onclick=()=>{songBars.forEach(b=>b.tracks[currentBank].fill(true));refreshArrangerUI();};
$("btn-arr-clear").onclick=()=>{songBars.forEach(b=>b.tracks[currentBank].fill(false));refreshArrangerUI();};
document.querySelectorAll(".fx-btn").forEach(el=>el.onclick=()=>{initAudio();activeFx=activeFx===el.dataset.fx?null:el.dataset.fx;document.querySelectorAll(".fx-btn").forEach(b=>b.classList.toggle("lit",b.dataset.fx===activeFx));applyFxRealtime();});
$("btn-hold").onclick=e=>{holdOn=!holdOn;e.currentTarget.classList.toggle("lit",holdOn);for(let b=0;b<NUM_BANKS;b++)for(let p=0;p<NUM_PADS;p++)if(banks[b][p].activeVoice)hotSwapVoice(b,p);};
$("btn-cancel").onclick=panicKillAll;

function setupKnob(id,init,label,onChange){
  const w=$(id),cap=w.querySelector(".knob-cap");let val=init;
  const ren=sh=>{cap.style.transform=`rotate(${(val-0.5)*270}deg)`;if(sh)hud.innerHTML=`<b>${label}:</b> ${Math.round(val*100)}%`;};
  ren(false);
  w.onmousedown=e=>{e.preventDefault();initAudio();const sy=e.clientY,sv=val,mv=ev=>{val=Math.max(0,Math.min(1,sv+(sy-ev.clientY)/140));ren(true);onChange(val);},up=()=>{window.removeEventListener("mousemove",mv);window.removeEventListener("mouseup",up);};window.addEventListener("mousemove",mv);window.addEventListener("mouseup",up);};
  w.addEventListener("wheel",e=>{e.preventDefault();initAudio();val=Math.max(0,Math.min(1,val+(e.deltaY<0?0.03:-0.03)));ren(true);onChange(val);},{passive:false});
  w.ondblclick=()=>{initAudio();val=init;ren(true);onChange(val);};
}
setupKnob("knob-vol",volVal,"MASTER VOLUME",v=>{volVal=v;if(masterGain)masterGain.gain.setTargetAtTime(v,ac.currentTime,0.015);});
setupKnob("knob-ctrl",ctrlVal,"FX CONTROL",v=>{ctrlVal=v;applyFxRealtime();});

window.addEventListener("keydown",e=>{
  if((document.activeElement&&document.activeElement.tagName==="INPUT")||e.repeat)return;
  if(e.key>="1"&&e.key<="8"){const i=+e.key-1;selectedPad=i;updateDynamicDisplay();syncWaveEditorUI();showPadBpmOnDisplay(banks[currentBank][i]);if(resampleState==="select"){resampleTarget={bank:currentBank,pad:i};syncPadVisuals();hud.innerHTML=`<b>RESAMPLE TARGET:</b> BANK ${BANK_NAMES[currentBank]} PAD ${i+1} (${banks[currentBank][i].name}) — PRESS <b>REC</b> AGAIN TO ARM`;return;}if(!remainMode&&!deleteMode)triggerPad(currentBank,i);renderAllWaveCanvases();}
  if(e.code==="Escape")panicKillAll();
  if(e.code==="Space"){e.preventDefault();isPlaying?stopTransport():startTransport();}
});
window.addEventListener("keyup",e=>{if(document.activeElement&&document.activeElement.tagName==="INPUT")return;if(e.key>="1"&&e.key<="8"){const i=+e.key-1;if(banks[currentBank][i].gate&&!holdOn)stopPadVoice(currentBank,i);}});
window.addEventListener("resize",()=>requestAnimationFrame(()=>{drawSevenSegDisplay(displayedLedValue);renderAllWaveCanvases();}));

registerFactoryTree();renderSampleTree();buildPatternButtons();buildSequencerGrid();buildMixerUI();buildArrangerUI();
loadBoomBapPattern();refreshAllBankUI();updateDynamicDisplay();syncPadVisuals();
requestAnimationFrame(()=>{drawSevenSegDisplay(bpm);renderAllWaveCanvases();});
requestAnimationFrame(uiAnimLoop);
})();