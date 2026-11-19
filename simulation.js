/* Deterministic, renderer-independent flight/combat simulation. Units: metres/seconds. */
(function(root){
 'use strict';
 const clamp=(n,a,b)=>Math.max(a,Math.min(b,n));
 const length=v=>Math.hypot(v.x,v.y,v.z);
 const norm=v=>{const n=length(v)||1;return{x:v.x/n,y:v.y/n,z:v.z/n};};
 const distance=(a,b)=>Math.hypot(a.x-b.x,a.y-b.y,a.z-b.z);
 const copy=v=>({x:v.x,y:v.y,z:v.z});
 function segmentDistance(a,b,p){const x=b.x-a.x,y=b.y-a.y,z=b.z-a.z,t=clamp(((p.x-a.x)*x+(p.y-a.y)*y+(p.z-a.z)*z)/(x*x+y*y+z*z||1),0,1);return Math.hypot(a.x+t*x-p.x,a.y+t*y-p.y,a.z+t*z-p.z);}
 const phases={
  ambush:{name:'01 / ИМПЕРСКАЯ ЗАСАДА',objective:'Пробейся через эскорт',tip:'Держи цель по центру. ЛКМ / пробел — огонь.',duration:32},
  field:{name:'02 / АСТЕРОИДНЫЙ КОРИДОР',objective:'Не потеряй ситха среди скал',tip:'WASD — манёвры. SHIFT — форсаж. T — турель.',duration:43},
  scan:{name:'03 / ПО СЛЕДУ СИТХА',objective:'Вычисли маршрут прыжка',tip:'Удерживай корабль ситха в прицеле сканера.',duration:38},
  hyper:{name:'04 / МЕЖДУ ЗВЁЗДАМИ',objective:'Не отпускай штурвал',tip:'Гиперпространственный переход.',duration:7},
  duel:{name:'05 / ПОСЛЕДНИЙ ПЕРЕХВАТ',objective:'Останови корабль ситха',tip:'Щит цели отключён. Захвати цель и запускай ракеты.',duration:80}
 };
 const difficulties={
  cadet:{key:'cadet',label:'КАДЕТ',damage:.62,enemyHp:.82,score:.85,density:.8},
  knight:{key:'knight',label:'РЫЦАРЬ',damage:1,enemyHp:1,score:1,density:1},
  master:{key:'master',label:'МАСТЕР',damage:1.38,enemyHp:1.18,score:1.3,density:1.18}
 };
 const enemyTypes={
  interceptor:{hp:39,radius:8,speed:32,sway:23,lift:13,shoot:[2.7,4.5],damage:8,score:250,scale:1},
  bomber:{hp:92,radius:11,speed:20,sway:10,lift:7,shoot:[3.9,5.8],damage:14,score:480,scale:1.42},
  ace:{hp:60,radius:9,speed:46,sway:34,lift:20,shoot:[2.1,3.3],damage:11,score:700,scale:1.18}
 };
 const multiplierFor=combo=>Math.min(5,1+Math.floor(Math.max(0,combo-1)/2));
 class Game{
  constructor(seed=123456,difficulty='knight'){this.initialSeed=seed>>>0;this.difficulty=difficulties[difficulty]?difficulty:'knight';this.reset();}
  reset(){
   const mod=this.mods=difficulties[this.difficulty];
   this.seed=this.initialSeed>>>0;this.nextId=1;this.status='ready';this.phase='ambush';this.phaseTime=0;this.time=0;
   this.player={x:0,y:0,z:0,vx:0,vy:0,hull:100,shield:100,heat:0,boost:100,boosting:false,rockets:6,speed:110};
   this.aim={x:0,y:0};this.yaw=0;this.pitch=0;this.turret=false;this.power='shields';
   this.enemies=[];this.asteroids=[];this.bullets=[];this.missiles=[];this.pickups=[];this.events=[];
    this.score=0;this.kills=0;this.shots=0;this.hits=0;this.combo=0;this.comboTimer=0;this.maxCombo=0;this.pickupsCollected=0;
    this.rift=100;this.echo=null;this.echoCount=0;this.echoKills=0;this.echoLog=[];this.echoShots=[];this.echoSample=0;this.echoInvulnerable=0;this.nearMisses=new Set();this.bossGap=330;
   this.lock=0;this.lockId=null;this.lockCandidate=null;this.scan=0;this.hyperReady=false;
   this.fireTimer=0;this.missileTimer=0;this.lastDamage=-10;this.overheated=false;
   this.spawnTimer=1;this.destroyerTimer=this.range(2.4,4.2);this.history=[];this.historyTimer=0;this.collisionTimer=0;this.noteTimer=0;
   const bossHp=Math.round(360*mod.enemyHp);
   this.boss={id:'boss',kind:'boss',variant:'sith',x:0,y:15,z:-340,hp:bossHp,maxHp:bossHp,radius:14,seed:0,shoot:3,attackTimer:1.6,enraged:false};
   this.radarThreat=0;this.won=false;this.rank=null;this.reason='';
   for(let i=0;i<Math.round(95*mod.density);i++)this.asteroids.push(this.rock(true));
  }
  random(){this.seed=(Math.imul(this.seed,1664525)+1013904223)>>>0;return this.seed/4294967296;}
  range(a,b){return a+(b-a)*this.random();}
  emit(type,data={}){this.events.push({type,...data});}
  start(){this.reset();this.status='playing';this.emit('chapter');this.emit('comms',{who:'К-7 / БОРТОВОЙ ДРОИД',text:'Ситх впереди. Я бы предложил отступить, но ты ведь всё равно не послушаешь.'});this.spawnEnemy('interceptor');this.spawnEnemy('interceptor');}
  rock(initial=false){const dense=this.phase==='field'||this.phase==='duel';let x=this.range(-700,700),y=this.range(-370,370);if(!dense&&Math.abs(x)<130&&Math.abs(y)<90)x+=(x<0?-1:1)*180;return{id:this.nextId++,x,y,z:this.player.z-this.range(initial?100:900,2100),radius:this.range(8,dense?34*this.mods.density:25),rot:this.range(0,6.28),spin:this.range(-.1,.1),hp:40};}
  spawnEnemy(variant){
   const p=this.player,mod=this.mods;
   if(!variant){
    const pool=this.phase==='duel'?[['interceptor',.43],['bomber',.27],['ace',.3]]:this.phase==='field'||this.phase==='scan'?[['interceptor',.52],['bomber',.21],['ace',.27]]:[['interceptor',.72],['bomber',.12],['ace',.16]];
    const roll=this.random();let edge=0;variant='interceptor';
    for(const [name,weight] of pool){edge+=weight;if(roll<=edge){variant=name;break;}}
   }
   const cfg=enemyTypes[variant]||enemyTypes.interceptor;
   const hp=Math.max(1,Math.round(cfg.hp*mod.enemyHp));
   const e={id:this.nextId++,kind:'fighter',variant,x:p.x+this.range(-220,220),y:p.y+this.range(-110,110),z:p.z-this.range(this.phase==='duel'?240:330,this.phase==='duel'?470:600),hp,maxHp:hp,radius:cfg.radius,seed:this.range(0,6.28),side:this.random()<.5?-1:1,age:0,shoot:this.range(cfg.shoot[0],cfg.shoot[1]),sway:cfg.sway,lift:cfg.lift,speed:cfg.speed,damage:cfg.damage,scale:cfg.scale};
   this.enemies.push(e);
  }
  setPhase(phase){
   this.phase=phase;this.phaseTime=0;this.emit('chapter');
   const lines={field:'Он ведёт нас в астероидное поле. Отлично. Я как раз закончил ремонт.',scan:'Зафиксирован разгон гипердрайва! Держи ситха в прицеле. Я вычислю маршрут.',hyper:'Координаты совпадают. Если это сработает — напомни мне удивиться.',duel:'Мы вышли прямо за ним! Его щит не восстановился. Это наш шанс.'};
   if(lines[phase])this.emit('comms',{who:'К-7 / БОРТОВОЙ ДРОИД',text:lines[phase]});
   if(phase==='field'){for(let i=0;i<Math.round(18*this.mods.density);i++)this.asteroids.push(this.rock());}
    if(phase==='hyper'){this.echo=null;this.echoLog=[];this.echoShots=[];this.bullets=[];this.missiles=[];this.enemies=[];this.pickups=[];this.player.shield=Math.min(100,this.player.shield+40);this.player.heat=0;this.player.boost=100;this.overheated=false;this.emit('jump');}
    if(phase==='duel'){this.player.rockets=Math.max(3,this.player.rockets);this.boss.hp=this.boss.maxHp;this.bossGap=310;this.boss.z=this.player.z-this.bossGap;this.boss.attackTimer=1.4;this.boss.enraged=false;this.player.shield=Math.min(100,this.player.shield+25);this.pickups=[];this.missiles=[];this.bullets=[];for(const r of this.asteroids){r.z=this.player.z-this.range(250,2000);}this.spawnEnemy('ace');this.spawnEnemy('interceptor');}
  }
  setPower(value){if(['engines','shields','weapons'].includes(value)){this.power=value;this.emit('power');}}
  toggleTurret(){if(this.status!=='playing'||this.phase==='hyper')return;this.turret=!this.turret;this.aim={x:0,y:0};this.lock=0;this.lockId=null;this.emit('seat');this.emit('comms',{who:'К-7 / БОРТОВОЙ ДРОИД',text:this.turret?'Корабль беру на себя. Турель твоя. Пожалуйста, не стреляй по нашей антенне.':'Возвращаю управление. Держи его в поле зрения.'});}
  forward(){return{x:-Math.sin(this.yaw)*Math.cos(this.pitch),y:Math.sin(this.pitch),z:-Math.cos(this.yaw)*Math.cos(this.pitch)};}
  alignedTarget(angle=.13){const d=this.forward(),p=this.player;let best=null,bestDot=Math.cos(angle);for(const t of [...this.enemies,this.boss]){if(t.hp<=0)continue;const dx=t.x-p.x,dy=t.y-p.y,dz=t.z-p.z,dist=Math.hypot(dx,dy,dz);if(dist>850||dist<8)continue;const dot=(dx*d.x+dy*d.y+dz*d.z)/dist;if(dot>bestDot){bestDot=dot;best=t;}}return best;}
  multiplier(){return multiplierFor(this.combo);}
   fire(){const p=this.player;if(this.fireTimer>0||this.overheated||this.phase==='hyper')return;const rate=(this.turret?.105:.16)*(this.power==='weapons'?.75:1);this.fireTimer=rate;p.heat=Math.min(100,p.heat+(this.turret?5.5:7));this.shots++;let dir=this.forward();const target=this.alignedTarget(this.turret?.12:.1);if(target)dir=norm({x:target.x-p.x,y:target.y-p.y,z:target.z-p.z});const bullet={id:this.nextId++,x:p.x,y:p.y,z:p.z-5,vx:dir.x*1050,vy:dir.y*1050,vz:dir.z*1050-p.speed,life:1.5,enemy:false,damage:this.power==='weapons'?19:15,turret:this.turret};this.bullets.push(bullet);this.echoShots.push({time:this.time,phase:this.phase,x:bullet.x,y:bullet.y,z:bullet.z,vx:bullet.vx,vy:bullet.vy,vz:bullet.vz,damage:bullet.damage});this.emit('fire',{turret:this.turret});if(p.heat>=99){this.overheated=true;this.emit('toast',{text:'СТВОЛЫ ПЕРЕГРЕТЫ · дай им остыть'});}}
   activateRift(){
    if(this.status!=='playing'||this.phase==='hyper'||this.echo||this.rift<100)return false;
    const frames=this.echoLog.filter(f=>f.phase===this.phase&&this.time-f.time<=3.1);
    if(frames.length<12||this.time-frames[0].time<1)return false;
    const first=frames[0],last=frames[frames.length-1];
    const shots=this.echoShots.filter(s=>s.phase===this.phase&&s.time>=first.time&&s.time<=last.time);
    this.echo={frames:frames.map(f=>({...f})),shots:shots.map(s=>({...s})),elapsed:0,duration:last.time-first.time,shotIndex:0,x:first.x,y:first.y,z:first.z,yaw:first.yaw,pitch:first.pitch};
    this.player.x=first.x;this.player.y=first.y;this.player.z=first.z;this.player.vx=first.vx;this.player.vy=first.vy;this.bossGap=clamp(this.player.z-this.boss.z,180,650);
    this.echoInvulnerable=.8;this.rift=0;this.echoCount++;this.echoLog=[];this.echoShots=[];this.emit('rift',{position:copy(first),duration:this.echo.duration});return true;
   }
   advanceEcho(dt){
    if(!this.echo)return;const e=this.echo;e.elapsed=Math.min(e.duration,e.elapsed+dt);const time=e.frames[0].time+e.elapsed;
    let i=0;while(i<e.frames.length-2&&e.frames[i+1].time<time)i++;
    const a=e.frames[i],b=e.frames[Math.min(i+1,e.frames.length-1)],t=clamp((time-a.time)/(b.time-a.time||1),0,1);
    for(const key of ['x','y','z','yaw','pitch'])e[key]=a[key]+(b[key]-a[key])*t;
    while(e.shotIndex<e.shots.length&&e.shots[e.shotIndex].time<=time){const s=e.shots[e.shotIndex++];this.bullets.push({id:this.nextId++,x:s.x,y:s.y,z:s.z,vx:s.vx,vy:s.vy,vz:s.vz,damage:s.damage*.8,life:1.5,enemy:false,echo:true});this.emit('echoFire',{position:copy(s)});}
    if(e.elapsed>=e.duration){this.emit('echoEnd',{position:{x:e.x,y:e.y,z:e.z}});this.echo=null;}
   }
  launchMissile(){if(this.status!=='playing'||this.phase==='hyper')return false;const p=this.player;if(p.rockets<=0){this.emit('toast',{text:'РАКЕТЫ ЗАКОНЧИЛИСЬ'});return false;}if(this.missileTimer>0)return false;const target=[...this.enemies,this.boss].find(e=>e.id===this.lockId&&e.hp>0);if(this.lock<1||!target){this.emit('toast',{text:'УДЕРЖИВАЙ ЦЕЛЬ В ПРИЦЕЛЕ ДО ЗАХВАТА'});return false;}p.rockets--;this.missileTimer=1.3;this.missiles.push({id:this.nextId++,x:p.x-4,y:p.y-3,z:p.z-6,target:target.id,life:6,enemy:false});this.emit('missile');return true;}
  jump(){if(this.status!=='playing')return false;if(this.phase!=='scan'||!this.hyperReady){this.emit('toast',{text:'ГИПЕРДРАЙВ · маршрут ещё не вычислен'});return false;}this.setPhase('hyper');return true;}
   damagePlayer(amount,source){if(this.status!=='playing'||this.phase==='hyper'||this.echoInvulnerable>0||this.time-this.lastDamage<.28)return;this.lastDamage=this.time;amount*=this.mods.damage;const absorbed=Math.min(this.player.shield,amount);this.player.shield-=absorbed;const hullDamage=Math.max(0,amount-absorbed)*.75;this.player.hull=Math.max(0,this.player.hull-hullDamage);if(hullDamage>0){this.combo=0;this.comboTimer=0;}this.emit('damage',{amount,source});if(this.player.hull<=0)this.end(false,'Корабль получил критические повреждения.');}
  awardKill(t){
   this.combo++;this.comboTimer=4.6;this.maxCombo=Math.max(this.maxCombo,this.combo);
   const mult=this.multiplier();
   const base=t.kind==='boss'?5000:(t.variant==='ace'?700:t.variant==='bomber'?480:250)+(this.turret?50:0);
   const gain=Math.round(base*mult*this.mods.score);
    this.score+=gain;this.rift=clamp(this.rift+(t.kind==='boss'?35:18),0,100);if(t.lastEchoHit)this.echoKills++;
   this.emit('kill',{position:copy(t),kind:t.kind,variant:t.variant,score:gain,combo:this.combo,multiplier:mult});
  }
   damageTarget(t,amount,missile=false,echo=false){
   if(t.hp<=0)return;
   if(t.kind==='boss'&&this.phase!=='duel'){if(this.noteTimer<=0){this.emit('toast',{text:'ЩИТ СИТХА ДЕРЖИТСЯ · уничтожай эскорт'});this.noteTimer=5;}this.emit('shield',{position:copy(t)});return;}
    t.hp=Math.max(0,t.hp-amount);t.lastEchoHit=echo;this.hits+=missile||echo?0:1;this.emit('hit',{position:copy(t),boss:t.kind==='boss',echo});
   if(t.hp===0){
    this.kills++;this.awardKill(t);this.emit('explosion',{position:copy(t),size:t.kind==='boss'?40:(t.variant==='bomber'?22:t.variant==='ace'?17:15)});
    if(t.kind==='boss'){this.end(true,'Корабль ситха уничтожен. Его маршрут заканчивается здесь.');}
    else{this.player.shield=Math.min(100,this.player.shield+3);this.dropPickup(t);}
   }
  }
  dropPickup(t){
   if(t.kind==='boss')return;
   const chance=t.variant==='ace'?.78:t.variant==='bomber'?.58:.32;
   if(this.random()>chance)return;
   const roll=this.random();let type;
   if(this.player.shield<55)type=roll<.62?'shield':'hull';
   else if(this.player.rockets<4)type=roll<.5?'rocket':roll<.85?'shield':'hull';
   else type=roll<.4?'hull':roll<.82?'shield':'rocket';
   this.pickups.push({id:this.nextId++,type,x:t.x,y:t.y,z:t.z,age:0,life:14});
  }
  collectPickup(k){
   const p=this.player;
   if(k.type==='shield')p.shield=Math.min(100,p.shield+26);
   else if(k.type==='hull')p.hull=Math.min(100,p.hull+12);
   else p.rockets=Math.min(9,p.rockets+2);
   this.pickupsCollected++;
   this.score+=50;
    this.emit('pickup',{pickupType:k.type,position:copy(k)});
  }
  destroyerVolley(){
   const p=this.player,origin={x:-390,y:125,z:p.z-560};
   for(let i=0;i<3;i++){
    const aim={x:p.x+this.range(-55,55),y:p.y+this.range(-35,35),z:p.z};
    const dir=norm({x:aim.x-origin.x,y:aim.y-origin.y,z:aim.z-origin.z});
    this.bullets.push({id:this.nextId++,x:origin.x,y:origin.y,z:origin.z,vx:dir.x*540,vy:dir.y*540,vz:dir.z*540,life:2.4,enemy:true,damage:13,heavy:true});
   }
   this.emit('turbolaser');
  }
  bossMissile(){
   const b=this.boss;
   this.missiles.push({id:this.nextId++,x:b.x,y:b.y-2,z:b.z,life:5,enemy:true,damage:16});
   this.emit('bossMissile');
  }
  end(win,reason){if(this.status!=='playing')return;this.status='ended';this.won=win;this.reason=reason;if(win)this.score+=Math.round((this.player.hull*15+this.player.shield*5)*this.mods.score);this.rank=this.calculateRank();this.emit('end',{win,rank:this.rank});}
  calculateRank(){
   const acc=this.hits/(this.shots||1);
   if(this.won){
    if(this.player.hull>=72&&acc>=.34&&this.maxCombo>=6)return 'S';
    if(this.player.hull>=38||acc>=.3)return 'A';
    return 'B';
   }
   if(this.boss.hp/this.boss.maxHp<.35||this.score>=5000)return 'C';
   if(this.score>=2000)return 'D';
   return 'E';
  }
  step(dt,input={}){
   if(this.status!=='playing')return;dt=clamp(dt,0,.05);this.time+=dt;this.phaseTime+=dt;const p=this.player,mod=this.mods;
    this.fireTimer=Math.max(0,this.fireTimer-dt);this.missileTimer=Math.max(0,this.missileTimer-dt);this.noteTimer=Math.max(0,this.noteTimer-dt);this.collisionTimer=Math.max(0,this.collisionTimer-dt);this.echoInvulnerable=Math.max(0,this.echoInvulnerable-dt);
   if(this.comboTimer>0){this.comboTimer-=dt;if(this.comboTimer<=0){this.combo=0;this.comboTimer=0;}}
   if(input.aimX!==undefined)this.aim.x=clamp(input.aimX,-1,1);if(input.aimY!==undefined)this.aim.y=clamp(input.aimY,-1,1);
   const yawTarget=-this.aim.x*(this.turret?Math.PI:.65),pitchTarget=-this.aim.y*(this.turret?1.1:.48);this.yaw+=(yawTarget-this.yaw)*(1-Math.exp(-dt*8));this.pitch+=(pitchTarget-this.pitch)*(1-Math.exp(-dt*8));
   const wantBoost=!!input.boost&&!this.turret&&this.phase!=='hyper'&&(p.boosting?p.boost>0.5:p.boost>=18);
   if(wantBoost!==p.boosting){p.boosting=wantBoost;this.emit('boost',{on:wantBoost});}
   if(p.boosting)p.boost=Math.max(0,p.boost-dt*32);else p.boost=Math.min(100,p.boost+dt*18);
   p.speed=(this.phase==='hyper'?1500:110)*(this.power==='engines'?1.3:1)*(p.boosting?1.62:1);p.z-=p.speed*dt;
   const dx=this.turret?-p.x*.35:(input.right?1:0)-(input.left?1:0),dy=this.turret?-p.y*.35:(input.up?1:0)-(input.down?1:0);
   p.vx+=(clamp(dx,-1,1)*75-p.vx)*(1-Math.exp(-dt*3));p.vy+=(clamp(dy,-1,1)*60-p.vy)*(1-Math.exp(-dt*3));p.x=clamp(p.x+p.vx*dt,-260,260);p.y=clamp(p.y+p.vy*dt,-160,160);
   const avoid=this.turret&&this.phase!=='hyper';if(avoid){for(const r of this.asteroids){const dz=p.z-r.z;if(dz>0&&dz<235&&Math.abs(r.x-p.x)<r.radius+24&&Math.abs(r.y-p.y)<r.radius+24){p.vx+=(r.x>p.x?-1:1)*145*dt;p.vy+=(r.y>p.y?-1:1)*95*dt;}}}
   p.heat=Math.max(0,p.heat-dt*(this.power==='weapons'?24:22));if(this.overheated&&p.heat<25){this.overheated=false;this.emit('toast',{text:'ПУШКИ СНОВА ГОТОВЫ'});}if(this.time-this.lastDamage>3.5)p.shield=Math.min(100,p.shield+dt*(this.power==='shields'?5.5:1.6));
    if(input.fire)this.fire();this.advanceEcho(dt);
   const boss=this.boss,final=this.phase==='duel';
    boss.x=Math.sin(this.time*(final?.43:.23))*105+Math.sin(this.time*.79)*22;boss.y=20+Math.cos(this.time*(final?.37:.3))*55;
    if(this.phase!=='hyper')this.bossGap=clamp(this.bossGap+((final?107:114)-p.speed)*dt,final?160:200,650);
    boss.z=p.z-this.bossGap;
   if(final){
    if(!boss.enraged&&boss.hp<=boss.maxHp*.4){boss.enraged=true;this.emit('enrage',{position:copy(boss)});}
    boss.attackTimer-=dt;
    if(boss.attackTimer<=0){
     boss.attackTimer=boss.enraged?1.12:1.72;
     const roll=this.random();
     if(roll<.48)this.enemyFire(boss,boss.enraged?16:14);
     else if(roll<.8)this.enemyFire(boss,11,.045);
     else this.bossMissile();
     if(boss.enraged&&roll<.42)this.enemyFire(boss,9,.07);
    }
   }
   const candidate=this.alignedTarget(.14);this.lockCandidate=candidate;if(candidate&&candidate.id===this.lockId){this.lock=clamp(this.lock+dt/1.15,0,1);}else if(candidate){this.lockId=candidate.id;this.lock=0;}else{this.lock=Math.max(0,this.lock-dt*2);if(this.lock===0)this.lockId=null;}
   if(this.phase==='scan'){const aligned=candidate&&candidate.id==='boss';const rate=aligned?(this.lock>=1?1/7.5:1/9):1/35;this.scan=clamp(this.scan+dt*rate,0,1);if(this.scan>=1&&!this.hyperReady){this.hyperReady=true;this.emit('ready');this.emit('comms',{who:'К-7 / БОРТОВОЙ ДРОИД',text:'Маршрут готов. Рычаг справа. Только не перепутай с подогревом сиденья.'});}if(this.phaseTime>55){this.end(false,'Ситх ушёл. Маршрут был готов, но ты не включил гипердрайв.');}}
   if(this.phase==='ambush'&&this.phaseTime>=32)this.setPhase('field');else if(this.phase==='field'&&this.phaseTime>=43)this.setPhase('scan');else if(this.phase==='hyper'&&this.phaseTime>=7)this.setPhase('duel');else if(this.phase==='duel'&&this.phaseTime>=80)this.end(false,'Ситх восстановил гипердрайв и ушёл от перехвата.');
   if(this.status!=='playing')return;
   if(this.phase==='ambush'){this.destroyerTimer-=dt;if(this.destroyerTimer<=0){this.destroyerTimer=this.range(2.6,4.4);this.destroyerVolley();}}
   if(this.phase!=='hyper'){
    this.spawnTimer-=dt;const max=this.phase==='duel'?3:5;if(this.spawnTimer<=0&&this.enemies.filter(e=>e.hp>0).length<max){this.spawnEnemy();this.spawnTimer=this.phase==='scan'?5.2:3.8;}
    for(const e of this.enemies){if(e.hp<=0)continue;e.age+=dt;e.z-=(p.speed-(e.speed||32))*dt;e.x+=Math.sin(e.age*1.2+e.seed)*dt*(e.sway||23);e.y+=Math.cos(e.age*.8+e.seed)*dt*(e.lift||13);e.shoot-=dt;if(e.shoot<=0&&distance(e,p)<720){e.shoot=this.range(e.variant==='bomber'?3.9:e.variant==='ace'?2.1:2.7,e.variant==='bomber'?5.8:e.variant==='ace'?3.3:4.5);this.enemyFire(e,e.damage||8,e.variant==='ace'?.05:0);}if(e.z>p.z+180||e.age>28)e.hp=0;}
    this.enemies=this.enemies.filter(e=>e.hp>0);
     for(let i=0;i<this.asteroids.length;i++){const r=this.asteroids[i];r.rot+=r.spin*dt;const d=distance(r,p);if(r.z>p.z+100||r.hp<=0){this.nearMisses.delete(r.id);this.asteroids[i]=this.rock();}else if(this.collisionTimer<=0&&d<r.radius+5){this.damagePlayer(28,'asteroid');this.collisionTimer=1;r.hp=0;this.emit('explosion',{position:copy(r),size:r.radius});}else if(!this.nearMisses.has(r.id)&&Math.abs(r.z-p.z)<r.radius+10&&d<r.radius+37){this.nearMisses.add(r.id);this.rift=clamp(this.rift+22,0,100);this.score+=Math.round(90*this.mods.score);this.emit('nearMiss',{position:copy(r)});}}
    for(const k of this.pickups){k.age+=dt;k.life-=dt;const d=distance(k,p);if(k.age>.22&&d<270){const dir=norm({x:p.x-k.x,y:p.y-k.y,z:p.z-k.z});const sp=145+Math.min(100,k.age*35);k.x+=dir.x*sp*dt;k.y+=dir.y*sp*dt;k.z+=dir.z*sp*dt;}if(k.age>.15&&distance(k,p)<14){this.collectPickup(k);k.life=0;}if(k.z>p.z+70||k.life<=0)k.life=0;}
    this.pickups=this.pickups.filter(k=>k.life>0);
    this.updateProjectiles(dt);
   }
    this.echoSample-=dt;if(this.echoSample<=0){this.echoSample=.05;this.echoLog.push({time:this.time,phase:this.phase,x:p.x,y:p.y,z:p.z,vx:p.vx,vy:p.vy,yaw:this.yaw,pitch:this.pitch});}while(this.echoLog.length&&this.time-this.echoLog[0].time>3.1)this.echoLog.shift();while(this.echoShots.length&&this.time-this.echoShots[0].time>3.1)this.echoShots.shift();
    this.historyTimer-=dt;if(this.historyTimer<=0){this.historyTimer=.1;this.history.push({time:this.time,phase:this.phase,player:copy(p),echo:this.echo?{x:this.echo.x,y:this.echo.y,z:this.echo.z,yaw:this.echo.yaw,pitch:this.echo.pitch}:null,boost:p.boost,boosting:p.boosting,combo:this.combo,comboTimer:this.comboTimer,yaw:this.yaw,pitch:this.pitch,boss:{...copy(boss),hp:boss.hp,enraged:boss.enraged},enemies:this.enemies.map(e=>({...copy(e),id:e.id,seed:e.seed,variant:e.variant,scale:e.scale})),bullets:this.bullets.map(b=>({...copy(b),id:b.id,enemy:b.enemy,echo:!!b.echo,vx:b.vx,vy:b.vy,vz:b.vz,heavy:b.heavy})),missiles:this.missiles.map(m=>({...copy(m),id:m.id,enemy:!!m.enemy})),pickups:this.pickups.map(k=>({...copy(k),id:k.id,type:k.type})),asteroids:this.asteroids.map(a=>({...copy(a),id:a.id,radius:a.radius,rot:a.rot}))});if(this.history.length>120)this.history.shift();}
  }
  enemyFire(e,damage,spread=0){const p=this.player,base=norm({x:p.x+p.vx*.35-e.x,y:p.y+p.vy*.35-e.y,z:p.z-e.z});const perp=norm({x:-base.z,y:0,z:base.x});const count=spread?3:1;for(let i=0;i<count;i++){const off=spread?(i-1)*spread:0;const dir=norm({x:base.x+perp.x*off,y:base.y,z:base.z+perp.z*off});this.bullets.push({id:this.nextId++,x:e.x,y:e.y,z:e.z,vx:dir.x*330,vy:dir.y*330,vz:dir.z*330,life:3,enemy:true,damage});}this.emit('enemyFire');}
  updateProjectiles(dt){const p=this.player;
    for(const b of this.bullets){const before=copy(b);b.x+=b.vx*dt;b.y+=b.vy*dt;b.z+=b.vz*dt;b.life-=dt;if(b.enemy){if(segmentDistance(before,b,p)<6){b.life=0;this.damagePlayer(b.damage,'laser');}}else{let target=null,t=Infinity;for(const e of [...this.enemies,this.boss]){if(e.hp>0&&segmentDistance(before,b,e)<e.radius+2){const d=distance(before,e);if(d<t){target=e;t=d;}}}let rock=null;for(const r of this.asteroids){if(r.hp>0&&segmentDistance(before,b,r)<r.radius*.8&&distance(before,r)<t){rock=r;t=distance(before,r);target=null;}}let missile=null;for(const m of this.missiles){if(m.enemy&&segmentDistance(before,b,m)<5&&distance(before,m)<t){missile=m;t=distance(before,m);target=null;rock=null;}}if(target){b.life=0;this.damageTarget(target,b.damage,false,!!b.echo);}else if(missile){b.life=0;missile.life=0;this.score+=60;this.emit('explosion',{position:copy(missile),size:5});}else if(rock){b.life=0;rock.hp-=b.damage;if(rock.hp<=0){this.score+=20;this.emit('explosion',{position:copy(rock),size:rock.radius});}}}}
   this.bullets=this.bullets.filter(b=>b.life>0);
   for(const m of this.missiles){
    m.life-=dt;const before=copy(m);
    if(m.enemy){
     const dir=norm({x:p.x-m.x,y:p.y-m.y,z:p.z-m.z});const speed=285+Math.min(95,(5-m.life)*30);
     m.x+=dir.x*speed*dt;m.y+=dir.y*speed*dt;m.z+=dir.z*speed*dt;
     if(segmentDistance(before,m,p)<8){m.life=0;this.damagePlayer(m.damage,'missile');this.emit('explosion',{position:copy(p),size:6});}
    }else{
     const target=[...this.enemies,this.boss].find(e=>e.id===m.target&&e.hp>0);if(!target){m.life=0;continue;}const dir=norm({x:target.x-m.x,y:target.y-m.y,z:target.z-m.z});const speed=520+p.speed;m.x+=dir.x*speed*dt;m.y+=dir.y*speed*dt;m.z+=dir.z*speed*dt;if(segmentDistance(before,m,target)<target.radius+5){m.life=0;this.damageTarget(target,90,true);this.emit('explosion',{position:copy(target),size:12});}
    }
   }
   this.missiles=this.missiles.filter(m=>m.life>0);
  }
  progress(){if(this.phase==='scan')return this.scan;return clamp(this.phaseTime/phases[this.phase].duration,0,1);}
 }
 root.RiftSim={Game,phases,difficulties,enemyTypes,segmentDistance,distance,norm,multiplierFor};
})(typeof window!=='undefined'?window:globalThis);
