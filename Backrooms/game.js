(function () {
'use strict';

/* ═══════════════════════════════════════════════════════════
   BACKROOMS — рефактор + оптимизация + консоль команд
   ═══════════════════════════════════════════════════════════ */

const TEX    = 64;
const TMASK  = 63;
const TSHIFT = 6;
const B      = 8;
const OPEN   = 0.22;
const WIDE   = 0.30;
const PLANE  = 0.80;
const FOG_R  = 30, FOG_G = 27, FOG_B = 15;
const FOG_D  = 0.047;
const PR     = 0.28;

const STAM_MAX   = 100;
const STAM_DRAIN = 26;
const STAM_REGEN = 11;
const STAM_IDLE  = 15;
const STAM_RECOVER = 35;

const MON_SPEED      = 4.7;
const MON_SPRINT_MULT = 1.35;
const MON_CAUGHT_D   = 0.75;
const MON_LOS_RANGE  = 30;
const MON_ESCAPE_T   = 8.0;
const MON_ESCAPE_D   = 16;
const MON_SEARCH_T   = 20.0;
const MON_FIRST_MIN  = 8;
const MON_FIRST_MAX  = 16;
const MON_COOL_MIN   = 14;
const MON_COOL_MAX   = 26;

const L1_MON_SPEED      = 5.4;
const L1_MON_SPRINT_MULT = 1.45;
const L1_MON_LOS_RANGE  = 34;
const L1_MON_FIRST_MIN  = 5;
const L1_MON_FIRST_MAX  = 11;
const L1_MON_COOL_MIN   = 10;
const L1_MON_COOL_MAX   = 20;

const L2_MON_SPEED      = 3.8;
const L2_MON_SPRINT_MULT = 1.25;
const L2_MON_LOS_RANGE  = 22;
const L2_MON_FIRST_MIN  = 6;
const L2_MON_FIRST_MAX  = 12;
const L2_MON_COOL_MIN   = 12;
const L2_MON_COOL_MAX   = 22;
const L3_MON_SPEED=6.15,L3_MON_SPRINT_MULT=1.55,L3_MON_LOS_RANGE=38;
const L3_MON_FIRST_MIN=4,L3_MON_FIRST_MAX=8,L3_MON_COOL_MIN=8,L3_MON_COOL_MAX=15;

const ENERGY_SPAWN_CHANCE = 0.045;
const ECHO_SPAWN_CHANCE = 0.028;
const ECHO_GOAL = 3;
const ECHO_REWARD = 150;
const MOP_SPAWN_CHANCE    = 0.010;
const RADAR_SPAWN_CHANCE  = 0.010;
const BEER_SPAWN_CHANCE   = 0.005;

const ENERGY_HEAL = 55;
const BOOST_DURATION = 5.0;
const BOOST_MULT = 1.8;
const MON_STUN_DURATION = 5.0;
const RADAR_DURATION = 10.0;
const BEER_DURATION = 20.0;
const BEER_SLOW = 0.65;
const PUDDLE_LIFE = 120;
const PUDDLE_RADIUS = 1.35;
const STUN_SCORE = 25;

const LB_KEY = 'backrooms_lb_v1';
const PORTAL_SCORE_L1 = 150;
const PORTAL_SCORE_L2 = 300;
const PORTAL_SCORE_L3 = 520;
const SCORE_PER_SEC_L0 = 1;
const SCORE_PER_SEC_L1 = 2;
const SCORE_PER_SEC_L2 = 3;
const SCORE_PER_ENERGY = 10;
const SCORE_PER_ROOM = 5;

/* ─── утилиты ─── */
function hash(x, y, s) {
  let h = Math.imul(x | 0, 374761393) ^ Math.imul(y | 0, 668265263) ^ Math.imul(s | 0, 1442695041);
  h = Math.imul(h ^ (h >>> 13), 1274126177);
  h ^= h >>> 16;
  return (h >>> 0) * 2.3283064365386963e-10;
}
function vnoise(x, y, s) {
  const xi = Math.floor(x), yi = Math.floor(y);
  const xf = x - xi, yf = y - yi;
  const u = xf * xf * (3 - 2 * xf), v = yf * yf * (3 - 2 * yf);
  const a = hash(xi, yi, s),     b = hash(xi + 1, yi, s);
  const c = hash(xi, yi + 1, s), d = hash(xi + 1, yi + 1, s);
  const ab = a + (b - a) * u, cd = c + (d - c) * u;
  return ab + (cd - ab) * v;
}
function pack(r, g, b) {
  r = r < 0 ? 0 : r > 255 ? 255 : r | 0;
  g = g < 0 ? 0 : g > 255 ? 255 : g | 0;
  b = b < 0 ? 0 : b > 255 ? 255 : b | 0;
  return (255 << 24) | (b << 16) | (g << 8) | r;
}

/* ═══════════════════════════════════════════════════════════
   СОСТОЯНИЕ
   ═══════════════════════════════════════════════════════════ */
let currentLevel = 0;
let score = 0;
let energyCollected = 0;
let portalActive = false;
let portalX = 0, portalY = 0;
let portalMsgTimer = 0;

const player = { x: 1000.5, y: 1000.5, yaw: 0, bobT: 0, bob: 0 };
let targetYaw = 0;
const stamina = { cur: STAM_MAX, exhausted: false };
const boost = { t: 0 };
const radar = { t: 0 };
const beer = { t: 0, punchCd: 0 };
let shield = false;
const bucket = { x: 1000.5, y: 1000.5, active: false };
const kartRace = { active: false, finishX: 0, finishY: 0, playerWon: false, monsterWon: false };
let flicker = 1;

const visitedRooms = new Set();
const puddles = [];
const mopDrops = [];
const radarDrops = [];
const beerDrops = [];
const energyDrops = [];
const echoDrops = [];
let echoCount = 0;
let echoRewarded = false;
const itemsSeen = new Set();
const thrownCans = [];
const landedCans = [];

let blackoutActive = false;
let godMode = false;
let noclipMode = false;
let timeScale = 1.0;

const eventSys = { nextTimer: 40 + Math.random() * 20, active: null, timeLeft: 0 };
const noisePulse = { x: 0, y: 0, t: 0 };
const poolCurrent = { timer: 26, active: 0, angle: 0 };
const crimsonAlarm = { timer: 24, active: 0 };

/* ═══════════════════════════════════════════════════════════
   МИР
   ═══════════════════════════════════════════════════════════ */
function wallAt(x, y) {
  const bx = Math.floor(x / B);
  const by = Math.floor(y / B);
  const xm = x - bx * B;
  const ym = y - by * B;
  if (xm === 0 && ym === 0) return true;
  if (xm === 0) {
    if (hash(bx, by, 101) < OPEN) return false;
    const dw = hash(bx, by, 303) < WIDE ? 2 : 1;
    const span = B - dw;
    const d0 = by * B + 1 + ((hash(bx, by, 7) * span) | 0);
    return !(y >= d0 && y < d0 + dw);
  }
  if (ym === 0) {
    if (hash(bx, by, 202) < OPEN) return false;
    const dw = hash(bx, by, 404) < WIDE ? 2 : 1;
    const span = B - dw;
    const d0 = bx * B + 1 + ((hash(bx, by, 11) * span) | 0);
    return !(x >= d0 && x < d0 + dw);
  }
  if (currentLevel === 2) {
    if (hash(bx, by, 777) > 0.82) {
      if (xm >= 3 && xm <= 5 && ym >= 3 && ym <= 5) return true;
    }
  } else if (currentLevel === 1 || currentLevel === 3) {
    if (hash(bx, by, 666) > 0.75) {
      if (xm >= 3 && xm <= 5 && ym >= 3 && ym <= 5) return true;
    }
  } else {
    if (hash(bx, by, 555) > 0.88) {
      if (xm >= 3 && xm <= 5 && ym >= 3 && ym <= 5) return true;
    }
  }
  return false;
}
function solid(x, y) {
  if (noclipMode) return false;
  return wallAt(Math.floor(x), Math.floor(y));
}

/* ═══════════════════════════════════════════════════════════
   ТЕКСТУРЫ
   ═══════════════════════════════════════════════════════════ */
const wallTex  = new Uint32Array(TEX * TEX);
const floorTex = new Uint32Array(TEX * TEX);
const ceilTex  = new Uint32Array(TEX * TEX);
const wallTexL1  = new Uint32Array(TEX * TEX);
const floorTexL1 = new Uint32Array(TEX * TEX);
const ceilTexL1  = new Uint32Array(TEX * TEX);
const puddleTex  = new Uint32Array(TEX * TEX);
const portalTex  = new Uint32Array(TEX * TEX);
const mopPuddleTex = new Uint32Array(TEX * TEX);

/* Poolrooms — оптимизированные текстуры */
const wallTexL2  = new Uint32Array(TEX * TEX);
const floorTexL2 = new Uint32Array(TEX * TEX);   // плитка, БЕЗ воды
const ceilTexL2  = new Uint32Array(TEX * TEX);
const waterOverlayTexL2 = new Uint32Array(TEX * TEX); // вода — накладывается сверху
const WATER_CAUSTIC_FRAMES = 8;
const waterCausticLUT = new Uint8Array(WATER_CAUSTIC_FRAMES * TEX * TEX);
for (let frame = 0; frame < WATER_CAUSTIC_FRAMES; frame++) {
  for (let y = 0; y < TEX; y++) for (let x = 0; x < TEX; x++) {
    const wave = Math.sin(x * 0.19 + y * 0.13 + frame * Math.PI * 2 / WATER_CAUSTIC_FRAMES);
    waterCausticLUT[frame * TEX * TEX + y * TEX + x] = 224 + ((wave + 1) * 15.5);
  }
}

(function buildTextures() {
  for (let y = 0; y < TEX; y++) {
    for (let x = 0; x < TEX; x++) {
      /* Level 0 */
      let r, g, b;
      if (y >= 57) {
        const v = 0.85 + hash(x, y, 41) * 0.30;
        r = 104 * v; g = 84 * v; b = 58 * v;
        if (y === 57) { r *= 1.45; g *= 1.45; b *= 1.45; }
      } else {
        const stripe = 0.5 + 0.5 * Math.sin(x * 0.3927);
        let s = 1 + stripe * 0.055;
        s *= 0.90 + vnoise(x * 0.09, y * 0.09, 4) * 0.26;
        s *= 0.96 + hash(x, y, 21) * 0.09;
        if (y === 56) s *= 0.68;
        if (y === 55) s *= 0.86;
        if (y < 2) s *= 0.92;
        r = 202 * s; g = 186 * s; b = 120 * s;
      }
      wallTex[y * TEX + x] = pack(r, g, b);

      const fn1 = vnoise(x * 0.11, y * 0.11, 7);
      const fn2 = vnoise(x * 0.45, y * 0.45, 13);
      let fs = 0.72 + fn1 * 0.42 + fn2 * 0.14;
      fs *= 0.94 + hash(x, y, 55) * 0.12;
      if (fn1 < 0.28) fs *= 0.80;
      floorTex[y * TEX + x] = pack(128 * fs, 121 * fs, 86 * fs);

      let cs = 0.96 + hash(x, y, 5) * 0.07;
      cs *= 0.90 + vnoise(x * 0.13, y * 0.13, 3) * 0.16;
      let edge = 1;
      if ((x & 31) === 0 || (y & 31) === 0) edge = 0.66;
      else if ((x & 31) === 1 || (y & 31) === 1) edge = 0.86;
      ceilTex[y * TEX + x] = pack(172 * cs * edge, 166 * cs * edge, 128 * cs * edge);

      /* Level 1 */
      const cn1 = vnoise(x * 0.08, y * 0.08, 201);
      const cn2 = vnoise(x * 0.3, y * 0.3, 202);
      let cval = 0.55 + cn1 * 0.35 + cn2 * 0.15;
      cval *= 0.9 + hash(x, y, 203) * 0.15;
      if (cn1 < 0.35) cval *= 0.7;
      if ((x % 16 === 0) && hash(x, y, 204) > 0.7) cval *= 0.5;
      wallTexL1[y * TEX + x] = pack(120 * cval, 118 * cval, 112 * cval);

      const f1 = vnoise(x * 0.12, y * 0.12, 211);
      let f1s = 0.6 + f1 * 0.35;
      f1s *= 0.9 + hash(x, y, 212) * 0.15;
      floorTexL1[y * TEX + x] = pack(95 * f1s, 92 * f1s, 88 * f1s);

      const pn = vnoise(x * 0.2, y * 0.2, 221);
      let ps = 0.5 + pn * 0.3;
      const ripple = 0.5 + 0.5 * Math.sin(x * 0.8 + y * 0.5 + pn * 8);
      ps *= 0.8 + ripple * 0.3;
      puddleTex[y * TEX + x] = pack(40 * ps, 55 * ps, 70 * ps);

      let ds = 0.35 + hash(x, y, 231) * 0.25;
      ceilTexL1[y * TEX + x] = pack(55 * ds, 53 * ds, 50 * ds);

      /* Level 2 (Poolrooms) */
      const tileSize = 16;
      const tileX = x % tileSize, tileY = y % tileSize;
      const isGrout = (tileX === 0 || tileY === 0 || tileX === tileSize - 1 || tileY === tileSize - 1);
      let tileV = 0.92 + hash(x, y, 301) * 0.06;
      if (isGrout) tileV *= 0.65;
      tileV *= 0.96 + vnoise(x * 0.15, y * 0.15, 302) * 0.08;
      wallTexL2[y * TEX + x] = pack(235 * tileV, 238 * tileV, 240 * tileV);

      let floorV = 0.85 + hash(x, y, 303) * 0.08;
      if (isGrout) floorV *= 0.75;
      floorV *= 0.95 + vnoise(x * 0.2, y * 0.2, 304) * 0.1;
      floorTexL2[y * TEX + x] = pack(200 * floorV, 210 * floorV, 215 * floorV);

      let ceilV = 0.85 + hash(x, y, 305) * 0.08;
      if (isGrout) ceilV *= 0.8;
      ceilTexL2[y * TEX + x] = pack(220 * ceilV, 230 * ceilV, 235 * ceilV);

      /* Вода — полупрозрачный слой (tileable, оптимизированный: одна vnoise) */
      const wpn = vnoise(x * 0.18, y * 0.18, 306);
      const wRipple = 0.5 + 0.5 * Math.sin(x * 0.6 + y * 0.4 + wpn * 8);
      const wv = 0.5 + wpn * 0.25 + wRipple * 0.25;
      waterOverlayTexL2[y * TEX + x] = pack(
        Math.min(255, 70 * wv + 30),
        Math.min(255, 150 * wv + 50),
        Math.min(255, 190 * wv + 60)
      );

      /* портал */
      const pdx = x - 32, pdy = y - 32;
      const pd = Math.sqrt(pdx * pdx + pdy * pdy);
      if (pd < 28) {
        const glow = 1 - pd / 28;
        portalTex[y * TEX + x] = pack(120 + glow * 135, 20 + glow * 40, 180 + glow * 75);
      } else portalTex[y * TEX + x] = 0;

      const mpn = vnoise(x * 0.18, y * 0.18, 350);
      const mripple = 0.5 + 0.5 * Math.sin(x * 0.45 + y * 0.35 + mpn * 6);
      const mpv = 0.42 + mpn * 0.28 + mripple * 0.22;
      mopPuddleTex[y * TEX + x] = pack(
        Math.min(255, 40 * mpv + 18),
        Math.min(255, 65 * mpv + 22),
        Math.min(255, 100 * mpv + 28)
      );
    }
  }
})();

/* ═══════════════════════════════════════════════════════════
   СПРАЙТЫ
   ═══════════════════════════════════════════════════════════ */
const MSW = 40, MSH = 60;
const monsterTex = new Uint32Array(MSW * MSH);
(function buildMonster() {
  for (let y = 0; y < MSH; y++) {
    for (let x = 0; x < MSW; x++) {
      const cx = x - MSW / 2 + 0.5;
      let inside = false, isEye = false;
      const hx = cx / 6.5, hy = (y - 11) / 8.5;
      if (hx * hx + hy * hy < 1) inside = true;
      if (y >= 14 && y <= 20) {
        const jx = Math.abs(cx) / (5.5 - (y - 14) * 0.4);
        if (jx < 1) inside = true;
      }
      if (y >= 20 && y <= 48) {
        const t = (y - 20) / 28;
        if (Math.abs(cx) < 5.5 + t * 2.5) inside = true;
      }
      if (y >= 22 && y <= 50) {
        const t = (y - 22) / 28;
        if (Math.abs(Math.abs(cx) - (7.0 + t * 3.6)) < 1.5) inside = true;
      }
      if (y >= 48) { if (Math.abs(Math.abs(cx) - 3.2) < 2.2) inside = true; }
      if (y >= 7 && y <= 11) {
        const edx = Math.abs(Math.abs(cx) - 3.2);
        if (edx < 1.4 && Math.abs(y - 9) < 1.6) isEye = true;
      }
      let mouth = false;
      if (y >= 15 && y <= 17) {
        if (Math.abs(cx) < 4.5 - (y - 15) * 0.6) mouth = true;
      }
      let col;
      if (isEye) col = pack(230, 30, 25);
      else if (mouth) col = pack(20, 5, 5);
      else if (inside) {
        const n = vnoise(x * 0.4, y * 0.4, 93);
        const v = 8 + n * 22 + hash(x, y, 91) * 8;
        const rib = (Math.abs(cx) < 4 && Math.floor((y - 20) / 3) % 2 === 0) ? 0.55 : 1.0;
        col = pack(v * rib, v * rib * 0.85, v * rib * 0.95);
      } else col = 0;
      monsterTex[y * MSW + x] = col;
    }
  }
})();

const ENW = 20, ENH = 36;
const energyTex = new Uint32Array(ENW * ENH);
(function buildEnergy() {
  for (let y = 0; y < ENH; y++) {
    for (let x = 0; x < ENW; x++) {
      const cx = x - ENW / 2 + 0.5;
      let inside = false, rim = false, label = false;
      if (y >= 4 && y <= ENH - 2) {
        if (Math.abs(cx) < (y < 6 ? 5.5 : y > ENH - 4 ? 5.0 : 6.0)) inside = true;
      }
      if (y >= 2 && y <= 4 && Math.abs(cx) < 5) inside = true;
      if (inside && cx < -2 && cx > -4) rim = true;
      if (y >= 14 && y <= 24 && Math.abs(cx) < 4.5) label = true;
      let col;
      if (label) {
        const v = 0.6 + hash(x, y, 301) * 0.3;
        col = pack(230 * v, 200 * v, 40 * v);
        if ((Math.abs(cx) < 1.5 && y > 16 && y < 22) ||
            (cx > -2 && cx < 0 && y >= 15 && y <= 17)) col = pack(30, 20, 10);
      } else if (rim) col = pack(240, 240, 240);
      else if (inside) { const v = 0.45 + hash(x, y, 302) * 0.35; col = pack(180 * v, 30 * v, 25 * v); }
      energyTex[y * ENW + x] = col;
    }
  }
})();

const ECHOW = 20, ECHOH = 28;
const echoTex = new Uint32Array(ECHOW * ECHOH);
(function buildEchoTexture() {
  for (let y = 0; y < ECHOH; y++) {
    for (let x = 0; x < ECHOW; x++) {
      const fold = x >= 14 && y < 6 && x + y < 20;
      const paper = x >= 3 && x <= 16 && y >= 2 && y <= 25;
      let col = 0;
      if (paper) {
        const shade = 0.82 + hash(x, y, 1701) * 0.16;
        col = pack(205 * shade, 194 * shade, 151 * shade);
        if (x === 3 || x === 16 || y === 2 || y === 25) col = pack(95, 82, 61);
        if (fold) col = pack(120, 105, 80);
        if (y === 10 || y === 15 || y === 20) {
          if (x >= 6 && x <= 13) col = pack(90, 72, 115);
        }
        if ((x === 8 || x === 11) && y >= 7 && y <= 8) col = pack(130, 95, 165);
      }
      echoTex[y * ECHOW + x] = col;
    }
  }
})();

const CCW = 16, CCH = 8;
const crushedCanTex = new Uint32Array(CCW * CCH);
(function buildCrushedCan() {
  for (let y = 0; y < CCH; y++) {
    for (let x = 0; x < CCW; x++) {
      const cx = x - CCW / 2 + 0.5, cy = y - CCH / 2 + 0.5;
      let col = 0;
      if (Math.abs(cx) < 6.5 && Math.abs(cy) < 2.8) {
        const v = 0.4 + hash(x, y, 401) * 0.4;
        col = pack(150 * v, 30 * v, 22 * v);
        if ((x + y * 2) % 5 === 0) col = pack(70, 15, 10);
        if (cy < -1) col = pack(200 * v, 60 * v, 45 * v);
      }
      crushedCanTex[y * CCW + x] = col;
    }
  }
})();

const MOPW = 20, MOPH = 42;
const mopTex = new Uint32Array(MOPW * MOPH);
(function buildMop() {
  for (let y = 0; y < MOPH; y++) {
    for (let x = 0; x < MOPW; x++) {
      const cx = x - MOPW / 2 + 0.5;
      let col = 0;
      if (y >= 3 && y <= 26 && Math.abs(cx) < 1.4) {
        const v = 0.72 + hash(x, y, 601) * 0.2;
        col = pack(135 * v, 88 * v, 45 * v);
      }
      if (y >= 26 && y <= MOPH - 2) {
        const t = (y - 26) / (MOPH - 28);
        const halfW = 5 + t * 4;
        if (Math.abs(cx) < halfW) {
          const sp = (x + y * 0.3) % 2.5;
          const v = 0.55 + hash(x, y, 602) * 0.35;
          if (sp < 1.2) col = pack(200 * v, 195 * v, 165 * v);
          else col = pack(150 * v, 145 * v, 120 * v);
        }
      }
      mopTex[y * MOPW + x] = col;
    }
  }
})();

const HMW = 48, HMH = 80;
const handMopTex = new Uint32Array(HMW * HMH);
(function buildHandMop() {
  for (let y = 0; y < HMH; y++) {
    for (let x = 0; x < HMW; x++) {
      let col = 0;
      const t = (y - 6) / 56;
      if (t >= 0 && t <= 1) {
        const handleX = 40 - t * 28;
        if (Math.abs(x - handleX) < 2) {
          const v = 0.75 + hash(x, y, 621) * 0.2;
          col = pack(135 * v, 88 * v, 45 * v);
        }
      }
      const dmx = x - 12, dmy = y - 68;
      if (dmx * dmx / 56 + dmy * dmy / 32 < 1) {
        const sp = (x + y * 0.4) % 3;
        const v = 0.6 + hash(x, y, 622) * 0.3;
        col = sp < 1.2 ? pack(200 * v, 195 * v, 165 * v) : pack(150 * v, 145 * v, 120 * v);
      }
      handMopTex[y * HMW + x] = col;
    }
  }
})();

const BKW = 20, BKH = 26;
const bucketTex = new Uint32Array(BKW * BKH);
(function buildBucket() {
  for (let y = 0; y < BKH; y++) {
    for (let x = 0; x < BKW; x++) {
      const cx = x - BKW / 2 + 0.5;
      let col = 0;
      if (y >= 0 && y <= 4) {
        const d = Math.sqrt(cx * cx + (y - 4) * (y - 4));
        if (Math.abs(d - 7) < 0.8) col = pack(85, 90, 100);
      }
      const t = (y - 5) / (BKH - 7);
      if (t >= 0 && t <= 1) {
        const halfW = 6.5 + t * 1.5;
        if (Math.abs(cx) < halfW) {
          const v = 0.5 + hash(x, y, 631) * 0.25;
          const shading = 1 - Math.abs(cx) / halfW * 0.4;
          col = pack(115 * v * shading, 128 * v * shading, 148 * v * shading);
        }
      }
      if (y === 5 && Math.abs(cx) < 8) col = pack(190, 200, 220);
      if (y >= 7 && y <= 9 && Math.abs(cx) < 6.5) {
        const v = 0.7 + hash(x, y, 632) * 0.3;
        col = pack(60 * v, 95 * v, 130 * v);
      }
      bucketTex[y * BKW + x] = col;
    }
  }
})();

const HNW = 40, HNH = 72;
const handEnergyTex = new Uint32Array(HNW * HNH);
(function buildHandEnergy() {
  for (let y = 0; y < HNH; y++) {
    for (let x = 0; x < HNW; x++) {
      const cx = x - HNW / 2 + 0.5;
      let inside = false, rim = false, label = false, shine = false;
      const yy = y + cx * 0.15;
      if (yy >= 8 && yy <= HNH - 4) {
        const halfW = yy < 12 ? 11 : (yy > HNH - 8 ? 10 : 12);
        if (Math.abs(cx) < halfW) inside = true;
      }
      if (yy >= 4 && yy <= 8 && Math.abs(cx) < 10) inside = true;
      if (inside && cx < -5 && cx > -8) shine = true;
      if (inside && cx > 8) rim = true;
      if (yy >= 28 && yy <= 48 && Math.abs(cx) < 9) label = true;
      let col;
      if (label) {
        const v = 0.7 + hash(x, y, 311) * 0.3;
        col = pack(240 * v, 200 * v, 40 * v);
        const ly = yy - 38;
        if ((Math.abs(cx) < 3 && ly > -5 && ly < 5) ||
            (cx > -3 && cx < 2 && ly >= -8 && ly <= -3) ||
            (cx > -3 && cx < 4 && ly >= 3 && ly <= 7)) col = pack(30, 20, 10);
        if (yy === 28 || yy === 48) col = pack(30, 20, 10);
      } else if (shine) col = pack(255, 240, 200);
      else if (rim) col = pack(60, 20, 15);
      else if (inside) { const v = 0.5 + hash(x, y, 312) * 0.35; col = pack(200 * v, 40 * v, 30 * v); }
      handEnergyTex[y * HNW + x] = col;
    }
  }
})();

const HCNW = 34, HCNH = 24;
const handCanTex = new Uint32Array(HCNW * HCNH);
(function buildHandCan() {
  for (let y = 0; y < HCNH; y++) {
    for (let x = 0; x < HCNW; x++) {
      const cx = x - HCNW / 2 + 0.5, cy = y - HCNH / 2 + 0.5;
      const oval = (cx * cx) / 196 + (cy * cy) / 49;
      let col = 0;
      if (oval < 1) {
        const v = 0.4 + hash(x, y, 501) * 0.4;
        col = pack(160 * v, 32 * v, 24 * v);
        if (Math.abs(cx) < 11 && Math.abs(cy) < 2 && (x % 5 === 0)) col = pack(70, 15, 10);
        if (cy < -2 && oval < 0.6) col = pack(230 * v, 60 * v, 45 * v);
      }
      handCanTex[y * HCNW + x] = col;
    }
  }
})();

const HRW = 40, HRH = 40;
const handRadarTex = new Uint32Array(HRW * HRH);
(function buildHandRadar() {
  for (let y = 0; y < HRH; y++) {
    for (let x = 0; x < HRW; x++) {
      const cx = x - HRW / 2 + 0.5, cy = y - HRH / 2 + 0.5;
      const d = Math.sqrt(cx * cx + cy * cy);
      let col = 0;
      if (d < 19) { const v = 0.4 + hash(x, y, 641) * 0.3; col = pack(55 * v, 62 * v, 72 * v); }
      if (d < 13) col = pack(20, 40, 25);
      if (d < 13 && (Math.abs(cx) < 0.6 || Math.abs(cy) < 0.6)) col = pack(40, 110, 50);
      if (d < 13 && (Math.abs(d - 5) < 0.5 || Math.abs(d - 9.5) < 0.5)) col = pack(40, 110, 50);
      if (Math.abs(d - 13) < 1.2) col = pack(110, 120, 130);
      if (d < 2) col = pack(80, 220, 100);
      handRadarTex[y * HRW + x] = col;
    }
  }
})();

const HBW = 26, HBH = 64;
const handBeerTex = new Uint32Array(HBW * HBH);
(function buildHandBeer() {
  for (let y = 0; y < HBH; y++) {
    for (let x = 0; x < HBW; x++) {
      const cx = x - HBW / 2 + 0.5;
      let col = 0;
      if (y >= 2 && y <= 14 && Math.abs(cx) < 3.5) {
        const v = 0.5 + hash(x, y, 651) * 0.3; col = pack(30 * v, 80 * v, 40 * v);
      }
      if (y >= 14 && y <= 18) {
        if (Math.abs(cx) < 3.5 + (y - 14) * 1.5) {
          const v = 0.5 + hash(x, y, 652) * 0.3; col = pack(30 * v, 80 * v, 40 * v);
        }
      }
      if (y >= 18 && y <= HBH - 4 && Math.abs(cx) < 9) {
        const v = 0.5 + hash(x, y, 653) * 0.25;
        const shading = 1 - Math.abs(cx) / 9 * 0.4;
        col = pack(30 * v * shading, 90 * v * shading, 45 * v * shading);
      }
      if (y >= 30 && y <= 48 && Math.abs(cx) < 8) {
        const v = 0.8 + hash(x, y, 654) * 0.15;
        col = pack(230 * v, 200 * v, 60 * v);
        if (Math.abs(cx) < 4 && y > 35 && y < 44) col = pack(180, 30, 20);
      }
      if (Math.abs(cx + 5) < 1 && y > 20 && y < HBH - 10) col = pack(180, 230, 190);
      if (y >= 0 && y <= 2 && Math.abs(cx) < 4) col = pack(200, 200, 200);
      handBeerTex[y * HBW + x] = col;
    }
  }
})();

const RDW = 14, RDH = 14;
const radarTex = new Uint32Array(RDW * RDH);
(function buildRadar() {
  for (let y = 0; y < RDH; y++) {
    for (let x = 0; x < RDW; x++) {
      const cx = x - RDW / 2 + 0.5, cy = y - RDH / 2 + 0.5;
      const d = Math.sqrt(cx * cx + cy * cy);
      let col = 0;
      if (d < 6.5) col = pack(45, 50, 60);
      if (d < 5) col = pack(30, 60, 35);
      if (d < 2.5) col = pack(80, 220, 100);
      radarTex[y * RDW + x] = col;
    }
  }
})();

const BEWW = 10, BEWH = 24;
const beerTex = new Uint32Array(BEWW * BEWH);
(function buildBeerWorld() {
  for (let y = 0; y < BEWH; y++) {
    for (let x = 0; x < BEWW; x++) {
      const cx = x - BEWW / 2 + 0.5;
      let col = 0;
      if (y >= 1 && y <= 5 && Math.abs(cx) < 1.8) col = pack(30, 80, 40);
      if (y >= 5 && y <= BEWH - 2 && Math.abs(cx) < 3.5) {
        const v = 0.6 + hash(x, y, 661) * 0.3; col = pack(30 * v, 90 * v, 45 * v);
      }
      if (y >= 10 && y <= 18 && Math.abs(cx) < 3.2) col = pack(220, 190, 60);
      if (y === 0 && Math.abs(cx) < 2) col = pack(200, 200, 200);
      beerTex[y * BEWW + x] = col;
    }
  }
})();

const WF_W = 28, WF_H = 30;
const wetFloorSignTex = new Uint32Array(WF_W * WF_H);
(function buildWetFloorSign() {
  for (let y = 0; y < WF_H; y++) {
    for (let x = 0; x < WF_W; x++) {
      const cx = x - WF_W / 2 + 0.5;
      let col = 0;
      const t = (y - 2) / (WF_H - 4);
      if (t >= 0 && t <= 1) {
        const halfW = 2 + t * 11;
        if (Math.abs(cx) < halfW) {
          const v = 0.85 + hash(x, y, 701) * 0.15;
          col = pack(245 * v, 210 * v, 30 * v);
          if (Math.abs(cx) > halfW - 1.8 || y < 4) col = pack(25, 20, 8);
          if (y >= 9 && y <= WF_H - 8 && Math.abs(cx) < 1.6) col = pack(25, 20, 8);
        }
      }
      wetFloorSignTex[y * WF_W + x] = col;
    }
  }
})();

const FINW = 40, FINH = 10;
const finishTex = new Uint32Array(FINW * FINH);
(function buildFinish() {
  for (let y = 0; y < FINH; y++) {
    for (let x = 0; x < FINW; x++) {
      const check = ((x >> 2) + (y >> 1)) & 1;
      finishTex[y * FINW + x] = check ? pack(240, 240, 240) : pack(20, 20, 20);
    }
  }
})();

const KAW = 200, KAH = 90;
const handKartTex = new Uint32Array(KAW * KAH);
(function buildHandKart() {
  for (let y = 0; y < KAH; y++) {
    for (let x = 0; x < KAW; x++) {
      let col = 0;
      const cx = x - KAW / 2 + 0.5, cy = y - KAH + 40;
      const d = Math.sqrt(cx * cx + cy * cy);
      if (d > 30 && d < 38 && y > 20) col = pack(35, 35, 40);
      if (d > 26 && d < 30 && y > 20) col = pack(90, 90, 100);
      if (Math.abs(cx) < 3 && y > 40 && y < KAH - 2) col = pack(50, 50, 55);
      if (Math.abs(cx) < 10 && y > KAH - 10) col = pack(70, 70, 75);
      if (d > 5 && d < 12 && y > 55) col = pack(45, 45, 50);
      handKartTex[y * KAW + x] = col;
    }
  }
})();

const KMW = 60, KMH = 15;
const monsterKartTex = new Uint32Array(KMW * KMH);
(function buildMonsterKart() {
  for (let y = 0; y < KMH; y++) {
    for (let x = 0; x < KMW; x++) {
      const cx = x - KMW / 2 + 0.5, cy = y - KMH / 2 + 0.5;
      let col = 0;
      if (Math.abs(cx) < 24 && Math.abs(cy) < 4) {
        const v = 0.6 + hash(x, y, 821) * 0.3; col = pack(180 * v, 40 * v, 30 * v);
      }
      if (Math.abs(Math.abs(cx) - 20) < 3 && Math.abs(cy) < 4.5) col = pack(30, 30, 35);
      if (Math.abs(cx) < 22 && Math.abs(cy) < 1) col = pack(240, 220, 60);
      monsterKartTex[y * KMW + x] = col;
    }
  }
})();

/* ─── скример ─── */
const SCRW = 200, SCRH = 240;
let screamerURL = null;
(function buildScreamer() {
  const c = document.createElement('canvas');
  c.width = SCRW; c.height = SCRH;
  const cc = c.getContext('2d');
  const id = cc.createImageData(SCRW, SCRH);
  const d = id.data;
  for (let y = 0; y < SCRH; y++) {
    for (let x = 0; x < SCRW; x++) {
      const cx = x - SCRW / 2 + 0.5;
      const cy = y - SCRH / 2 + 0.5;
      const nx = cx / (SCRW * 0.42);
      const ny = cy / (SCRH * 0.55);
      let head = nx * nx + ny * ny < 1;
      if (!head && y > SCRH * 0.55 && y < SCRH * 0.95) {
        const jx = cx / (SCRW * 0.20 * (1 - (y - SCRH * 0.55) / (SCRH * 0.40) * 0.3));
        if (Math.abs(jx) < 1) head = true;
      }
      const i = (y * SCRW + x) * 4;
      if (!head) { d[i + 3] = 0; continue; }
      const n1 = vnoise(x * 0.06, y * 0.06, 11);
      const n2 = vnoise(x * 0.25, y * 0.25, 12);
      const base = 45 + n1 * 55 + n2 * 25;
      let r = base, g = base * 0.9, b = base * 0.95;
      const ex1 = x - SCRW * 0.36, ey1 = y - SCRH * 0.38;
      const ex2 = x - SCRW * 0.64, ey2 = y - SCRH * 0.38;
      const d1 = Math.sqrt(ex1 * ex1 + ey1 * ey1);
      const d2 = Math.sqrt(ex2 * ex2 + ey2 * ey2);
      let darken = 1;
      const eyeR = SCRW * 0.10;
      if (d1 < eyeR || d2 < eyeR) {
        darken = 0.05;
        const rd1 = Math.sqrt((x - SCRW * 0.36) ** 2 + (y - SCRH * 0.38) ** 2);
        const rd2 = Math.sqrt((x - SCRW * 0.64) ** 2 + (y - SCRH * 0.38) ** 2);
        const pupilR = eyeR * 0.42;
        if (rd1 < pupilR || rd2 < pupilR) {
          r = 255; g = 20; b = 15;
        }
      }
      if (Math.abs(cx) < SCRW * 0.04 && y > SCRH * 0.46 && y < SCRH * 0.58) darken = 0.2;
      const mouthY = SCRH * 0.74;
      const mouthH = SCRH * 0.15;
      const mouthW = SCRW * 0.22 * (1 - Math.abs(y - mouthY) / mouthH);
      if (y > mouthY - mouthH && y < mouthY + mouthH && Math.abs(cx) < mouthW) darken = 0.04;
      const vein = vnoise(x * 0.15, y * 0.15, 14);
      if (vein < 0.32) darken *= 0.65;
      r *= darken; g *= darken; b *= darken;
      const vx = Math.abs(cx) / (SCRW * 0.5);
      const vy = Math.abs(cy) / (SCRH * 0.5);
      const vig = Math.max(0, 1 - (vx * vx + vy * vy) * 0.7);
      r *= vig; g *= vig; b *= vig;
      d[i] = r; d[i + 1] = g; d[i + 2] = b; d[i + 3] = 255;
    }
  }
  cc.putImageData(id, 0, 0);
  screamerURL = c.toDataURL();
})();

/* ═══════════════════════════════════════════════════════════
   DOM
   ═══════════════════════════════════════════════════════════ */
const canvas = document.getElementById('view');
const ctx = canvas.getContext('2d', { alpha: false });
const eventMsgEl = document.getElementById('eventMsg');
const viewEl = document.getElementById('view');
const waterOverlay = document.getElementById('waterOverlay');
const levelNameEl = document.getElementById('levelName');
const scoreEl = document.getElementById('scoreVal');
const energyEl = document.getElementById('energyVal');
const echoEl = document.getElementById('echoVal');
const staminaFill = document.getElementById('staminaFill');
const dangerEl = document.getElementById('dangerVig');
const boostEl = document.getElementById('boostVig');
const fpsEl = document.getElementById('fps');

let cw = 480, ch = 240;
let img, buf, wallTop, wallBot, depth;

function resize() {
  const aspect = window.innerWidth / window.innerHeight;
  // Poolrooms рендерится в более низком внутреннем разрешении: CSS растягивает canvas,
  // а тяжёлый проход по пикселям обрабатывает примерно на 44% меньше точек.
  ch = currentLevel === 2 ? 160 : 240;
  cw = Math.round(ch * aspect);
  cw = cw < 180 ? 180 : cw > 780 ? 780 : cw;
  canvas.width = cw;
  canvas.height = ch;
  img = ctx.createImageData(cw, ch);
  buf = new Uint32Array(img.data.buffer);
  wallTop = new Int32Array(cw);
  wallBot = new Int32Array(cw);
  depth = new Float32Array(cw);
}
window.addEventListener('resize', resize);
resize();

/* ═══════════════════════════════════════════════════════════
   ИГРОК
   ═══════════════════════════════════════════════════════════ */
function canWalk(x, y) {
  if (noclipMode) return true;
  return !solid(x - PR, y - PR) && !solid(x + PR, y - PR) &&
         !solid(x - PR, y + PR) && !solid(x + PR, y + PR);
}
function findSpawn() {
  for (let a = 0; a < 400; a++) {
    const bx = 120 + ((hash(a, 3, 9) * 40) | 0);
    const by = 120 + ((hash(a, 5, 9) * 40) | 0);
    const px = bx * B + B * 0.5;
    const py = by * B + B * 0.5;
    let ok = true;
    for (let dy = -1; dy <= 1 && ok; dy++)
      for (let dx = -1; dx <= 1; dx++)
        if (wallAt((px | 0) + dx, (py | 0) + dy)) { ok = false; break; }
    if (ok) return { x: px, y: py };
  }
  return { x: 1000.5, y: 1000.5 };
}
(function spawn() {
  const s = findSpawn();
  player.x = s.x; player.y = s.y;
  bucket.x = s.x; bucket.y = s.y;
  player.yaw = hash(3, 9, 1) * Math.PI * 2;
  targetYaw = player.yaw;
})();

/* ═══════════════════════════════════════════════════════════
   ИНВЕНТАРЬ
   ═══════════════════════════════════════════════════════════ */
const inventory = [null, null, null, null, null];
let activeSlot = -1;
const inventoryEls = document.querySelectorAll('.slot');

function iconSVG(type) {
  if (type === 'energy') return '<svg width="24" height="30" viewBox="0 0 24 30"><rect x="6" y="3" width="12" height="24" fill="#b02018" stroke="#e8dd93" stroke-width="1"/><rect x="7" y="4" width="10" height="4" fill="#e8dd93"/><rect x="7" y="11" width="10" height="10" fill="#e8c840"/><polygon points="13,12 10,17 12,17 11,21 15,15 13,15" fill="#1a1000"/></svg>';
  if (type === 'can') return '<svg width="24" height="30" viewBox="0 0 24 30"><ellipse cx="12" cy="22" rx="10" ry="3" fill="#5a0a05"/><path d="M3 20 L5 15 L9 17 L13 14 L18 16 L21 20 Z" fill="#8b1810" stroke="#e8dd93" stroke-width="0.7"/></svg>';
  if (type === 'mop') return '<svg width="24" height="30" viewBox="0 0 24 30"><line x1="16" y1="4" x2="9" y2="19" stroke="#8a5a2a" stroke-width="2"/><ellipse cx="8" cy="23" rx="7" ry="4" fill="#d0c8a8"/><rect x="15" y="18" width="6" height="8" fill="#7a8a9a" stroke="#5a6a7a" stroke-width="0.5"/><rect x="15" y="18" width="6" height="2" fill="#9aaaba"/></svg>';
  if (type === 'radar') return '<svg width="24" height="24" viewBox="0 0 24 24"><circle cx="12" cy="12" r="10" fill="#2a3038" stroke="#8a8a8a" stroke-width="1"/><circle cx="12" cy="12" r="7" fill="#1a3a25"/><circle cx="12" cy="12" r="2" fill="#50c060"/></svg>';
  if (type === 'beer') return '<svg width="24" height="30" viewBox="0 0 24 30"><rect x="9" y="2" width="6" height="8" fill="#1e5028"/><rect x="6" y="10" width="12" height="18" fill="#287830" stroke="#e8dd93" stroke-width="0.7"/><rect x="7" y="15" width="10" height="8" fill="#e8c840"/><circle cx="12" cy="19" r="2" fill="#b02018"/></svg>';
  return '';
}
function updateInventoryUI() {
  for (let i = 0; i < 5; i++) {
    const el = inventoryEls[i];
    const item = inventory[i];
    const iconEl = el.querySelector('.icon');
    const cntEl = el.querySelector('.cnt');
    if (item) {
      el.classList.remove('empty');
      el.classList.toggle('active', i === activeSlot);
      iconEl.innerHTML = iconSVG(item.type);
      cntEl.textContent = item.count > 1 ? item.count : '';
    } else {
      el.classList.add('empty');
      el.classList.remove('active');
      iconEl.innerHTML = '';
      cntEl.textContent = '';
    }
  }
}
function addItem(type) {
  for (let i = 0; i < 5; i++) if (inventory[i] && inventory[i].type === type) { inventory[i].count++; updateInventoryUI(); return true; }
  for (let i = 0; i < 5; i++) if (!inventory[i]) { inventory[i] = { type, count: 1 }; updateInventoryUI(); return true; }
  return false;
}

function trySpawnItemsInRoom(bx, by) {
  const key = bx + ',' + by;
  if (itemsSeen.has(key)) return;
  itemsSeen.add(key);
  const echoRoll = hash(bx, by, 1700);
  if (echoRoll < ECHO_SPAWN_CHANCE && echoCount + echoDrops.length < ECHO_GOAL) {
    const ex = bx * B + 1 + hash(bx, by, 1702) * (B - 2);
    const ey = by * B + 1 + hash(bx, by, 1703) * (B - 2);
    if (!solid(ex, ey)) echoDrops.push({ x: ex, y: ey });
  }
  const roll = hash(bx, by, 999);
  let type = null;
  if (roll < ENERGY_SPAWN_CHANCE) type = 'energy';
  else if (roll < ENERGY_SPAWN_CHANCE + MOP_SPAWN_CHANCE) type = 'mop';
  else if (roll < ENERGY_SPAWN_CHANCE + MOP_SPAWN_CHANCE + RADAR_SPAWN_CHANCE) type = 'radar';
  else if (roll < ENERGY_SPAWN_CHANCE + MOP_SPAWN_CHANCE + RADAR_SPAWN_CHANCE + BEER_SPAWN_CHANCE) type = 'beer';
  if (!type) return;
  const ox = 1 + hash(bx, by, 998) * (B - 2);
  const oy = 1 + hash(bx, by, 997) * (B - 2);
  const ex = bx * B + ox, ey = by * B + oy;
  if (solid(ex, ey)) return;
  if (type === 'energy') energyDrops.push({ x: ex, y: ey });
  else if (type === 'mop') mopDrops.push({ x: ex, y: ey });
  else if (type === 'radar') radarDrops.push({ x: ex, y: ey });
  else if (type === 'beer') beerDrops.push({ x: ex, y: ey });
}

let lastScanX = -999, lastScanY = -999;
function scanRooms() {
  const pbx = Math.floor(player.x / B);
  const pby = Math.floor(player.y / B);
  if (Math.abs(pbx - lastScanX) < 2 && Math.abs(pby - lastScanY) < 2) return;
  lastScanX = pbx; lastScanY = pby;
  for (let dy = -4; dy <= 4; dy++)
    for (let dx = -4; dx <= 4; dx++)
      trySpawnItemsInRoom(pbx + dx, pby + dy);
}

function playPickupSfx(f1, f2) {
  if (!audioCtx) return;
  const t = audioCtx.currentTime;
  const o = audioCtx.createOscillator();
  const g = audioCtx.createGain();
  o.type = 'triangle';
  o.frequency.setValueAtTime(f1, t);
  o.frequency.exponentialRampToValueAtTime(f2, t + 0.15);
  g.gain.setValueAtTime(0.06, t);
  g.gain.exponentialRampToValueAtTime(0.001, t + 0.2);
  o.connect(g); g.connect(masterGain);
  o.start(t); o.stop(t + 0.22);
}

function updateItemPickup() {
  const pickup = (arr, type, sound) => {
    for (let i = arr.length - 1; i >= 0; i--) {
      const e = arr[i];
      const dx = e.x - player.x, dy = e.y - player.y;
      if (dx * dx + dy * dy < 0.7) {
        if (addItem(type)) {
          arr.splice(i, 1);
          if (type === 'energy') { energyCollected++; score += SCORE_PER_ENERGY; }
          if (audioCtx) sound();
        }
      }
    }
  };
  pickup(energyDrops, 'energy', () => playPickupSfx(660, 1320));
  pickup(mopDrops, 'mop', () => playPickupSfx(440, 880));
  pickup(radarDrops, 'radar', () => playPickupSfx(520, 1040));
  pickup(beerDrops, 'beer', () => playPickupSfx(330, 660));
  for (let i = echoDrops.length - 1; i >= 0; i--) {
    const e = echoDrops[i];
    const dx = e.x - player.x, dy = e.y - player.y;
    if (dx * dx + dy * dy < 0.78) {
      echoDrops.splice(i, 1);
      echoCount++;
      score += 35;
      stamina.cur = Math.min(STAM_MAX, stamina.cur + 25);
      playPickupSfx(740, 1480);
      eventMsgEl.textContent = `✧ ЭХО ПАМЯТИ ${echoCount}/${ECHO_GOAL} · +35`;
      if (echoCount >= ECHO_GOAL && !echoRewarded) {
        echoRewarded = true;
        score += ECHO_REWARD;
        eventMsgEl.textContent = `✧ ВСЕ ЭХО СОБРАНЫ · БОНУС +${ECHO_REWARD}`;
      }
    }
  }
}

function activateSlot(idx) {
  if (idx < 0 || idx >= 5) return;
  const item = inventory[idx];
  if (!item) { activeSlot = -1; updateInventoryUI(); return; }
  if (activeSlot === idx) { useActiveItem(); return; }
  activeSlot = idx;
  updateInventoryUI();
}
function useActiveItem() {
  if (activeSlot < 0) return;
  const item = inventory[activeSlot];
  if (!item) return;
  if (item.type === 'energy') drinkEnergy(activeSlot);
  else if (item.type === 'can') throwCan();
  else if (item.type === 'mop') useMop(activeSlot);
  else if (item.type === 'radar') useRadar(activeSlot);
  else if (item.type === 'beer') useBeer(activeSlot);
}
function drinkEnergy(idx) {
  const item = inventory[idx];
  if (!item || item.type !== 'energy') return;
  stamina.cur = Math.min(STAM_MAX, stamina.cur + ENERGY_HEAL);
  stamina.exhausted = false;
  boost.t = BOOST_DURATION;
  item.count--;
  if (item.count <= 0) { inventory[idx] = { type: 'can', count: 1 }; activeSlot = idx; }
  updateInventoryUI();
}
function useMop(idx) {
  const item = inventory[idx];
  if (!item || item.type !== 'mop') return;
  const signAngle = player.yaw + Math.PI * 0.5;
  puddles.push({ x: player.x, y: player.y, r: PUDDLE_RADIUS,
    signX: player.x + Math.cos(signAngle) * 0.95,
    signY: player.y + Math.sin(signAngle) * 0.95, life: PUDDLE_LIFE });
  item.count--;
  if (item.count <= 0) { inventory[idx] = null; if (activeSlot === idx) activeSlot = -1; }
  updateInventoryUI();
}
function useRadar(idx) {
  const item = inventory[idx];
  if (!item || item.type !== 'radar') return;
  radar.t = RADAR_DURATION;
  item.count--;
  if (item.count <= 0) { inventory[idx] = null; if (activeSlot === idx) activeSlot = -1; }
  updateInventoryUI();
}
function useBeer(idx) {
  const item = inventory[idx];
  if (!item || item.type !== 'beer') return;
  beer.t = BEER_DURATION;
  beer.punchCd = 0;
  shield = true;
  item.count--;
  if (item.count <= 0) { inventory[idx] = null; if (activeSlot === idx) activeSlot = -1; }
  updateInventoryUI();
  if (eventSys.active === null) {
    eventMsgEl.textContent = '🍺 ПЬЯНСТВО + ЩИТ + КУЛАК';
    setTimeout(() => { if (eventSys.active === null) eventMsgEl.textContent = ''; }, 2500);
  }
}
function tryPunch() {
  if (beer.t <= 0 || beer.punchCd > 0) return false;
  if (!monster.active || monster.mode === 'party_approach' || monster.mode === 'party_dance' || monster.mode === 'kart') return false;
  if (monster.stunTimer > 0 || monster.dist > 1.8) return false;
  monster.stunTimer = 2.0;
  addStunScore();
  beer.punchCd = 4.0;
  return true;
}
function addStunScore() {
  score += STUN_SCORE;
  if (eventSys.active === null) {
    eventMsgEl.textContent = '+' + STUN_SCORE + ' ЗА СТАН';
    setTimeout(() => { if (eventSys.active === null) eventMsgEl.textContent = ''; }, 900);
  }
}

function throwCan() {
  if (activeSlot < 0) return;
  const item = inventory[activeSlot];
  if (!item || item.type !== 'can') return;
  const ang = player.yaw;
  const maxDist = 6 + Math.random() * 3;
  let tx = player.x + Math.cos(ang) * maxDist;
  let ty = player.y + Math.sin(ang) * maxDist;
  let dist = maxDist;
  while (solid(tx, ty) && dist > 0.8) {
    dist -= 0.4;
    tx = player.x + Math.cos(ang) * dist;
    ty = player.y + Math.sin(ang) * dist;
  }
  if (solid(tx, ty)) return;
  item.count--;
  if (item.count <= 0) { inventory[activeSlot] = null; activeSlot = -1; }
  updateInventoryUI();
  thrownCans.push({ sx: player.x, sy: player.y, ex: tx, ey: ty, t: 0, duration: 0.35 });
}
function distractMonster(x, y) {
  if (!monster.active) return;
  if (monster.mode === 'party_approach' || monster.mode === 'party_dance' || monster.mode === 'kart') return;
  if (monster.hasLOS) return;
  monster.distractX = x; monster.distractY = y; monster.distractTimer = 5.0;
}
function updateThrownCans(dt) {
  for (let i = thrownCans.length - 1; i >= 0; i--) {
    const c = thrownCans[i];
    c.t += dt;
    if (c.t >= c.duration) {
      landedCans.push({ x: c.ex, y: c.ey, t: 0 });
      distractMonster(c.ex, c.ey);
      thrownCans.splice(i, 1);
    }
  }
}

/* ═══════════════════════════════════════════════════════════
   МОНСТР
   ═══════════════════════════════════════════════════════════ */
const monster = {
  x: player.x, y: player.y,
  active: false, mode: 'normal', state: 'idle',
  lastSeenX: player.x, lastSeenY: player.y,
  lostTimer: 0,
  idleTimer: MON_FIRST_MIN + Math.random() * (MON_FIRST_MAX - MON_FIRST_MIN),
  losTimer: 0, hasLOS: false,
  path: null, pathIndex: 0, pathTimer: 0, dist: 999,
  animT: 0, breathe: 0,
  distractX: 0, distractY: 0, distractTimer: 0,
  hat: false, partyTimer: 0, partyDanceT: 0, stunTimer: 0,
};

function hasLOS(x0, y0, x1, y1) {
  const dx = x1 - x0, dy = y1 - y0;
  const d2 = dx * dx + dy * dy;
  const range = currentLevel === 3 ? L3_MON_LOS_RANGE : currentLevel === 2 ? L2_MON_LOS_RANGE : currentLevel === 1 ? L1_MON_LOS_RANGE : MON_LOS_RANGE;
  if (d2 > range * range) return false;
  const steps = Math.ceil(Math.sqrt(d2) * 4);
  for (let i = 1; i < steps; i++) {
    const t = i / steps;
    if (solid(x0 + dx * t, y0 + dy * t)) return false;
  }
  return true;
}
function findPath(sx, sy, gx, gy) {
  if (sx === gx && sy === gy) return [[sx, sy]];
  const span = Math.min(Math.max(Math.abs(sx - gx), Math.abs(sy - gy)) + 5, 32);
  const parent = new Map();
  parent.set(sx + ',' + sy, null);
  const queue = [[sx, sy]];
  let head = 0, found = false;
  const dirs = [[1,0],[-1,0],[0,1],[0,-1]];
  while (head < queue.length && queue.length < 2500) {
    const cx = queue[head][0], cy = queue[head][1];
    head++;
    for (let i = 0; i < 4; i++) {
      const nx = cx + dirs[i][0], ny = cy + dirs[i][1];
      const key = nx + ',' + ny;
      if (parent.has(key)) continue;
      if (wallAt(nx, ny)) continue;
      if (Math.abs(nx - sx) > span || Math.abs(ny - sy) > span) continue;
      parent.set(key, [cx, cy]);
      if (nx === gx && ny === gy) { found = true; break; }
      queue.push([nx, ny]);
    }
    if (found) break;
  }
  if (!found) return null;
  const path = [];
  let cx = gx, cy = gy, safety = 200;
  while (cx !== null && safety-- > 0) {
    path.unshift([cx, cy]);
    const p = parent.get(cx + ',' + cy);
    if (!p) break;
    cx = p[0]; cy = p[1];
  }
  return path;
}
function spawnMonster() {
  const isL2 = currentLevel === 2, isL1 = currentLevel === 1 || currentLevel === 3;
  const minD = isL2 ? 6 : isL1 ? 8 : 10;
  const maxD = isL2 ? 16 : isL1 ? 18 : 20;
  for (let ring = 0; ring < 4; ring++) {
    const rMin = minD + ring * 4, rMax = maxD + ring * 6;
    for (let a = 0; a < 50; a++) {
      const ang = Math.random() * Math.PI * 2;
      const d = rMin + Math.random() * (rMax - rMin);
      const mx = player.x + Math.cos(ang) * d;
      const my = player.y + Math.sin(ang) * d;
      if (solid(mx - 0.35, my - 0.35) || solid(mx + 0.35, my - 0.35) ||
          solid(mx - 0.35, my + 0.35) || solid(mx + 0.35, my + 0.35)) continue;
      const los = hasLOS(player.x, player.y, mx, my);
      if (los && d < rMax * 0.85) continue;
      monster.x = mx; monster.y = my;
      monster.active = true; monster.mode = 'normal';
      monster.state = 'hunting';
      monster.hat = false; monster.stunTimer = 0;
      monster.hasLOS = los; monster.losTimer = 0; monster.lostTimer = 0;
      monster.distractTimer = 0;
      monster.lastSeenX = player.x; monster.lastSeenY = player.y;
      monster.path = null; monster.pathIndex = 0; monster.pathTimer = 0;
      return true;
    }
  }
  monster.idleTimer = 2;
  return false;
}
let lastMonStep = 0;
function updateMonster(dt, now) {
  if (monster.active && (monster.mode === 'party_approach' || monster.mode === 'party_dance')) {
    monster.partyTimer -= dt;
    monster.partyDanceT += dt;
    if (monster.mode === 'party_approach') {
      const dx = player.x - monster.x, dy = player.y - monster.y;
      const d = Math.sqrt(dx * dx + dy * dy);
      monster.dist = d;
      if (d > 1.6) {
        const sp = 6.0 * dt;
        const nx = monster.x + dx / d * sp;
        const ny = monster.y + dy / d * sp;
        if (!solid(nx, monster.y)) monster.x = nx;
        if (!solid(monster.x, ny)) monster.y = ny;
      } else monster.mode = 'party_dance';
    } else {
      monster.dist = Math.sqrt((player.x - monster.x) ** 2 + (player.y - monster.y) ** 2);
    }
    if (monster.partyTimer <= 0) {
      monster.active = false; monster.mode = 'normal'; monster.hat = false;
      const cm = currentLevel === 3 ? L3_MON_COOL_MIN : currentLevel === 2 ? L2_MON_COOL_MIN : currentLevel === 1 ? L1_MON_COOL_MIN : MON_COOL_MIN;
      const cM = currentLevel === 3 ? L3_MON_COOL_MAX : currentLevel === 2 ? L2_MON_COOL_MAX : currentLevel === 1 ? L1_MON_COOL_MAX : MON_COOL_MAX;
      monster.idleTimer = cm + Math.random() * (cM - cm);
    }
    return;
  }
  if (monster.active && monster.mode === 'kart') {
    if (!kartRace.active) return;
    const fdx = kartRace.finishX - monster.x, fdy = kartRace.finishY - monster.y;
    const fdist = Math.sqrt(fdx * fdx + fdy * fdy);
    monster.dist = Math.sqrt((player.x - monster.x) ** 2 + (player.y - monster.y) ** 2);
    if (fdist < 1.5) {
      if (!kartRace.playerWon && !kartRace.monsterWon) {
        kartRace.monsterWon = true;
        eventMsgEl.textContent = '💥 МОНСТР ФИНИШИРОВАЛ ПЕРВЫМ 💥';
        stamina.cur = Math.max(0, stamina.cur - 30);
        setTimeout(() => endEvent(), 2000);
      }
      return;
    }
    const step = (currentLevel === 3 ? L3_MON_SPEED : currentLevel === 2 ? L2_MON_SPEED : currentLevel === 1 ? L1_MON_SPEED : MON_SPEED) * 1.6 * dt;
    const nx = monster.x + fdx / fdist * step;
    const ny = monster.y + fdy / fdist * step;
    if (!solid(nx, monster.y)) monster.x = nx;
    if (!solid(monster.x, ny)) monster.y = ny;
    return;
  }
  if (!monster.active) {
    monster.idleTimer -= dt;
    if (monster.idleTimer <= 0) spawnMonster();
    return;
  }
  const isL2 = currentLevel === 2, isL1 = currentLevel === 1 || currentLevel === 3;
  const monSpeed = currentLevel === 3 ? L3_MON_SPEED : isL2 ? L2_MON_SPEED : isL1 ? L1_MON_SPEED : MON_SPEED;
  const sprintMult = currentLevel === 3 ? L3_MON_SPRINT_MULT : isL2 ? L2_MON_SPRINT_MULT : isL1 ? L1_MON_SPRINT_MULT : MON_SPRINT_MULT;
  const dx = player.x - monster.x, dy = player.y - monster.y;
  monster.dist = Math.sqrt(dx * dx + dy * dy);

  if (monster.stunTimer <= 0) {
    for (let i = 0; i < puddles.length; i++) {
      const p = puddles[i];
      const pdx = monster.x - p.x, pdy = monster.y - p.y;
      if (pdx * pdx + pdy * pdy < p.r * p.r) {
        monster.stunTimer = MON_STUN_DURATION;
        addStunScore();
        break;
      }
    }
  }
  if (monster.stunTimer > 0) { monster.stunTimer -= dt; return; }

  monster.losTimer -= dt;
  if (monster.losTimer <= 0) {
    monster.losTimer = 0.12;
    monster.hasLOS = hasLOS(monster.x, monster.y, player.x, player.y);
  }
  if (monster.hasLOS) {
    monster.lastSeenX = player.x; monster.lastSeenY = player.y;
    monster.lostTimer = 0; monster.state = 'hunting';
    monster.distractTimer = 0;
  } else {
    monster.lostTimer += dt;
    if (noisePulse.t > 0 && monster.dist < 14) {
      const ndx = noisePulse.x - monster.x, ndy = noisePulse.y - monster.y;
      if (ndx * ndx + ndy * ndy < 14 * 14) {
        monster.lastSeenX = noisePulse.x; monster.lastSeenY = noisePulse.y;
        monster.lostTimer = 0;
        monster.state = 'searching';
      }
    }
    if (monster.lostTimer > 2.0) monster.state = 'searching';
    const escaped = (monster.lostTimer > MON_ESCAPE_T && monster.dist > MON_ESCAPE_D) || monster.lostTimer > MON_SEARCH_T;
    if (escaped) {
      monster.active = false;
      const cm = isL2 ? L2_MON_COOL_MIN : isL1 ? L1_MON_COOL_MIN : MON_COOL_MIN;
      const cM = isL2 ? L2_MON_COOL_MAX : isL1 ? L1_MON_COOL_MAX : MON_COOL_MAX;
      monster.idleTimer = cm + Math.random() * (cM - cm);
      return;
    }
  }
  let tgtX, tgtY;
  if (monster.distractTimer > 0) {
    monster.distractTimer -= dt;
    tgtX = monster.distractX; tgtY = monster.distractY;
  } else {
    tgtX = (monster.state === 'hunting') ? player.x : monster.lastSeenX;
    tgtY = (monster.state === 'hunting') ? player.y : monster.lastSeenY;
  }
  monster.pathTimer -= dt;
  if (monster.pathTimer <= 0) {
    monster.pathTimer = 0.35;
    const p = findPath(Math.floor(monster.x), Math.floor(monster.y), Math.floor(tgtX), Math.floor(tgtY));
    if (p && p.length > 1) { monster.path = p; monster.pathIndex = 1; }
    else monster.path = null;
  }
  const stepLen = monSpeed * (monster.hasLOS ? sprintMult : 1.0) * dt;
  let moved = false;
  if (monster.path && monster.pathIndex < monster.path.length) {
    let remain = stepLen, iter = 0;
    while (remain > 0 && monster.pathIndex < monster.path.length && iter++ < 8) {
      const wp = monster.path[monster.pathIndex];
      const wx = wp[0] + 0.5, wy = wp[1] + 0.5;
      const ddx = wx - monster.x, ddy = wy - monster.y;
      const d = Math.sqrt(ddx * ddx + ddy * ddy);
      if (d <= remain) {
        monster.x = wx; monster.y = wy; remain -= d;
        monster.pathIndex++; moved = true;
      } else {
        monster.x += ddx / d * remain;
        monster.y += ddy / d * remain;
        remain = 0; moved = true;
      }
    }
  } else {
    const ddx = tgtX - monster.x, ddy = tgtY - monster.y;
    const d = Math.sqrt(ddx * ddx + ddy * ddy);
    if (d > 0.05) {
      const nx = monster.x + ddx / d * stepLen;
      const ny = monster.y + ddy / d * stepLen;
      if (!solid(nx, monster.y)) { monster.x = nx; moved = true; }
      if (!solid(monster.x, ny)) { monster.y = ny; moved = true; }
    }
  }
  if (moved) {
    monster.animT += dt; monster.breathe += dt;
    if (now - lastMonStep > 380 && monster.dist < 22 && audioCtx) {
      lastMonStep = now;
      playMonsterStep(monster.dist);
    }
  }
  if (monster.dist < MON_CAUGHT_D) onCaught();
}

/* ═══════════════════════════════════════════════════════════
   СМЕРТЬ
   ═══════════════════════════════════════════════════════════ */
const screamerEl = document.getElementById('screamer');
const screamerImg = document.getElementById('screamerImg');
screamerImg.src = screamerURL;
let deathTimer = 0, screamerActive = false, screamerT = 0;

function onCaught() {
  if (deathTimer > 0 || screamerActive || godMode) return;
  if (monster.mode === 'party_approach' || monster.mode === 'party_dance' || monster.mode === 'kart') return;
  if (monster.stunTimer > 0) return;
  if (shield) {
    shield = false; beer.t = 0;
    monster.stunTimer = 2.0;
    addStunScore();
    const dx = monster.x - player.x, dy = monster.y - player.y;
    const d = Math.sqrt(dx * dx + dy * dy) || 1;
    monster.x += dx / d * 2.5; monster.y += dy / d * 2.5;
    eventMsgEl.textContent = '🛡 ЩИТ ПОГЛОТИЛ УДАР';
    setTimeout(() => { if (eventSys.active === null) eventMsgEl.textContent = ''; }, 1600);
    return;
  }
  deathTimer = 1.2; screamerActive = true; screamerT = 0;
  monster.active = false; monster.mode = 'normal'; monster.hat = false;
  monster.idleTimer = 20;
  screamerImg.style.transform = 'scale(1.4)';
  screamerImg.style.filter = 'contrast(1.3) saturate(1.4)';
  screamerEl.style.transition = 'none';
  screamerEl.style.opacity = '1';
  if (audioCtx) {
    const t = audioCtx.currentTime;
    const o = audioCtx.createOscillator();
    const g = audioCtx.createGain();
    o.type = 'sawtooth';
    o.frequency.setValueAtTime(800, t);
    o.frequency.exponentialRampToValueAtTime(60, t + 0.6);
    g.gain.setValueAtTime(0.18, t);
    g.gain.exponentialRampToValueAtTime(0.001, t + 0.7);
    o.connect(g); g.connect(audioCtx.destination);
    o.start(t); o.stop(t + 0.72);
  }
  saveScoreToLeaderboard(Math.floor(score), energyCollected, currentLevel);
  setTimeout(() => {
    const s = findSpawn();
    player.x = s.x; player.y = s.y;
    bucket.x = s.x; bucket.y = s.y;
    player.yaw = Math.random() * Math.PI * 2;
    targetYaw = player.yaw;
    stamina.cur = STAM_MAX; stamina.exhausted = false; boost.t = 0;
  poolCurrent.active = 0; poolCurrent.timer = 22 + Math.random() * 10;
    beer.t = 0; radar.t = 0; shield = false;
  }, 300);
}
function updateScreamer(dt) {
  if (!screamerActive) return;
  screamerT += dt;
  const k = Math.min(1, screamerT / 0.5);
  const jx = (Math.random() - 0.5) * 8 * (1 - k * 0.3);
  const jy = (Math.random() - 0.5) * 8 * (1 - k * 0.3);
  const scale = 1.4 + Math.sin(screamerT * 40) * 0.05;
  screamerImg.style.transform = `translate(${jx}px, ${jy}px) scale(${scale})`;
  screamerImg.style.filter = `contrast(${1.3 + k * 0.5}) saturate(${1.4 + k * 0.8})`;
  if (screamerT > 0.9) {
    const fade = Math.min(1, (screamerT - 0.9) / 0.3);
    screamerEl.style.transition = 'opacity .3s';
    screamerEl.style.opacity = String(1 - fade);
    if (screamerT > 1.2) {
      screamerActive = false;
      screamerEl.style.opacity = '0';
      deathTimer = 0;
    }
  }
}

/* ═══════════════════════════════════════════════════════════
   ЛИДЕРБОРД
   ═══════════════════════════════════════════════════════════ */
function loadLeaderboard() {
  try { const r = localStorage.getItem(LB_KEY); return r ? JSON.parse(r) : []; }
  catch (e) { return []; }
}
function saveScoreToLeaderboard(sc, en, lvl) {
  const lb = loadLeaderboard();
  lb.push({ score: sc, energy: en, level: lvl, date: Date.now() });
  lb.sort((a, b) => b.score - a.score);
  try { localStorage.setItem(LB_KEY, JSON.stringify(lb.slice(0, 10))); } catch (e) {}
  renderLeaderboard();
}
function renderLeaderboard() {
  const lb = loadLeaderboard();
  const table = document.getElementById('lbTable');
  if (!table) return;
  let html = '<tr><td>#</td><td>ОЧКИ</td><td>ЭНЕРГЕТИКИ</td><td>УРОВЕНЬ</td></tr>';
  if (lb.length === 0) html += '<tr><td colspan="4" style="text-align:center;opacity:.5">пока пусто</td></tr>';
  else lb.forEach((e, i) => {
    html += `<tr><td>${i + 1}</td><td style="color:#fff">${e.score}</td><td>${e.energy}</td><td>${e.level}</td></tr>`;
  });
  table.innerHTML = html;
}
function toggleLeaderboard() {
  const el = document.getElementById('leaderboard');
  if (el.style.display === 'flex') el.style.display = 'none';
  else { renderLeaderboard(); el.style.display = 'flex'; }
}

/* ═══════════════════════════════════════════════════════════
   ПОРТАЛ
   ═══════════════════════════════════════════════════════════ */
function directionTo(angle) {
  while (angle > Math.PI) angle -= Math.PI * 2;
  while (angle < -Math.PI) angle += Math.PI * 2;
  if (angle > -Math.PI/4 && angle < Math.PI/4) return 'ВОСТОК';
  if (angle >= Math.PI/4 && angle < 3*Math.PI/4) return 'ЮГ';
  if (angle >= -3*Math.PI/4 && angle < -Math.PI/4) return 'СЕВЕР';
  return 'ЗАПАД';
}
function activatePortal() {
  if (portalActive) return;
  const targetScore = currentLevel === 0 ? PORTAL_SCORE_L1 : currentLevel === 1 ? PORTAL_SCORE_L2 : currentLevel === 2 ? PORTAL_SCORE_L3 : Infinity;
  if (score < targetScore) return;
  const pbx = Math.floor(player.x / B), pby = Math.floor(player.y / B);
  const candidates = [];
  for (let dy = -1; dy <= 1; dy++)
    for (let dx = -1; dx <= 1; dx++) {
      if (dx === 0 && dy === 0) continue;
      const cx = (pbx + dx) * B + B * 0.5, cy = (pby + dy) * B + B * 0.5;
      if (!solid(cx, cy)) candidates.push({ cx, cy });
    }
  if (candidates.length) {
    const pick = candidates[Math.floor(Math.random() * candidates.length)];
    portalX = pick.cx; portalY = pick.cy;
    portalActive = true;
    const ang = Math.atan2(portalY - player.y, portalX - player.x);
    if (eventSys.active === null) {
      eventMsgEl.textContent = `◈ ПОРТАЛ: ${directionTo(ang)} ${Math.round(Math.sqrt((portalX - player.x) ** 2 + (portalY - player.y) ** 2))}м`;
    }
  }
}
function checkPortal() {
  if (!portalActive) return;
  const dx = player.x - portalX, dy = player.y - portalY;
  if (dx * dx + dy * dy < 0.8) {
    if (currentLevel === 0) enterLevel1();
    else if (currentLevel === 1) enterLevel2();
    else if (currentLevel === 2) enterLevel3();
  }
}
function resetToLevel(lvl) {
  currentLevel = lvl;
  resize();
  portalActive = false;
  portalMsgTimer = 0;
  visitedRooms.clear();
  itemsSeen.clear();
  lastScanX = -999;
  lastScanY = -999;
  if (eventSys.active === null) eventMsgEl.textContent = '';
  let s = findSpawn();
  if (!canWalk(s.x, s.y)) {
    for (let i = 0; i < 500; i++) {
      const testX = 1000 + (hash(i, 7, 3) - 0.5) * 200;
      const testY = 1000 + (hash(i, 11, 4) - 0.5) * 200;
      if (canWalk(testX, testY)) { s = { x: testX, y: testY }; break; }
    }
  }
  player.x = s.x; player.y = s.y;
  bucket.x = s.x; bucket.y = s.y;
  player.yaw = Math.random() * Math.PI * 2;
  targetYaw = player.yaw;
  stamina.cur = STAM_MAX; stamina.exhausted = false; boost.t = 0;
  beer.t = 0; radar.t = 0; shield = false;
  puddles.length = 0; mopDrops.length = 0; energyDrops.length = 0;
  radarDrops.length = 0; beerDrops.length = 0;
  echoDrops.length = 0; echoCount = 0; echoRewarded = false;
  landedCans.length = 0; thrownCans.length = 0;
  kartRace.active = false;
  const names = ['LEVEL 0', 'LEVEL 1 — HABITABLE ZONE', 'LEVEL 2 — POOLROOMS', 'LEVEL 3 — CRIMSON ARCHIVES'];
  levelNameEl.textContent = names[lvl] || 'LEVEL ?';
  monster.active = false; monster.mode = 'normal'; monster.hat = false; monster.stunTimer = 0;
  crimsonAlarm.active=0; crimsonAlarm.timer=20+Math.random()*12;
  if (lvl === 3) monster.idleTimer=L3_MON_FIRST_MIN+Math.random()*(L3_MON_FIRST_MAX-L3_MON_FIRST_MIN);
  else if (lvl === 2) monster.idleTimer=L2_MON_FIRST_MIN+Math.random()*(L2_MON_FIRST_MAX-L2_MON_FIRST_MIN);
  else if (lvl === 1) monster.idleTimer=L1_MON_FIRST_MIN+Math.random()*(L1_MON_FIRST_MAX-L1_MON_FIRST_MIN);
  else monster.idleTimer = MON_FIRST_MIN + Math.random() * (MON_FIRST_MAX - MON_FIRST_MIN);
}
function enterLevel1() { resetToLevel(1); }
function enterLevel2() { resetToLevel(2); }
function enterLevel3() { resetToLevel(3); }

/* ═══════════════════════════════════════════════════════════
   КОНСОЛЬ (расширяемая)
   ═══════════════════════════════════════════════════════════ */
const commands = new Map();

function registerCommand(name, desc, usage, fn) {
  commands.set(name.toLowerCase(), { name, desc, usage, fn });
}

const consoleEl = document.getElementById('console');
const consoleLog = document.getElementById('consoleLog');
const consoleField = document.getElementById('consoleField');
let consoleOpen = false;

function logLine(text, cls) {
  const div = document.createElement('div');
  if (cls) div.className = cls;
  div.textContent = text;
  consoleLog.appendChild(div);
  consoleLog.scrollTop = consoleLog.scrollHeight;
}
function openConsole() {
  consoleOpen = true;
  running = false;
  clearMovementKeys();
  consoleEl.classList.add('open');
  consoleField.focus();
  if (document.pointerLockElement === canvas) document.exitPointerLock();
}
function closeConsole() {
  consoleOpen = false;
  consoleEl.classList.remove('open');
  consoleField.value = '';
  clearMovementKeys();
  startEl.classList.remove('hidden');
}
function runCommand(raw) {
  const line = raw.trim();
  if (!line) return;
  logLine('/' + line, 'cmd');
  const parts = line.split(/\s+/);
  const cmd = parts[0].toLowerCase();
  const args = parts.slice(1);
  const c = commands.get(cmd);
  if (!c) { logLine('неизвестная команда: ' + cmd + ' (help)', 'err'); return; }
  try { c.fn(args); }
  catch (e) { logLine('ошибка: ' + e.message, 'err'); }
}

/* ─── встроенные команды ─── */
registerCommand('help', 'список команд', 'help', () => {
  logLine('─── команды ───', 'info');
  const sorted = [...commands.values()].sort((a, b) => a.name.localeCompare(b.name));
  for (const c of sorted) logLine(`/${c.name} — ${c.desc}`, 'info');
});

registerCommand('lvl', 'перейти на уровень (0/1/2)', 'lvl <0|1|2>', (args) => {
  const l = parseInt(args[0], 10);
  if (isNaN(l) || l < 0 || l > 2) { logLine('укажи 0, 1 или 2', 'err'); return; }
  resetToLevel(l);
  logLine('уровень: ' + l, 'ok');
});

registerCommand('tp', 'телепорт в координаты', 'tp <x> <y>', (args) => {
  const x = parseFloat(args[0]), y = parseFloat(args[1]);
  if (isNaN(x) || isNaN(y)) { logLine('нужны координаты x y', 'err'); return; }
  player.x = x; player.y = y;
  logLine(`телепорт: ${x}, ${y}`, 'ok');
});

registerCommand('give', 'выдать предмет (energy/can/mop/radar/beer)', 'give <type> [count]', (args) => {
  const type = args[0];
  const cnt = parseInt(args[1] || '1', 10);
  const valid = ['energy', 'can', 'mop', 'radar', 'beer'];
  if (!valid.includes(type)) { logLine('типы: ' + valid.join(', '), 'err'); return; }
  for (let i = 0; i < cnt; i++) addItem(type);
  logLine(`выдано ${type} ×${cnt}`, 'ok');
});

registerCommand('score', 'установить очки', 'score <n>', (args) => {
  const n = parseInt(args[0], 10);
  if (isNaN(n)) { logLine('нужно число', 'err'); return; }
  score = n;
  logLine('очки: ' + n, 'ok');
});

registerCommand('spawn', 'заспавнить монстра', 'spawn', () => {
  spawnMonster();
  logLine('монстр заспавнен', 'ok');
});

registerCommand('kill', 'убрать монстра', 'kill', () => {
  monster.active = false;
  monster.idleTimer = 30;
  logLine('монстр убран', 'ok');
});

registerCommand('god', 'режим неуязвимости', 'god', () => {
  godMode = !godMode;
  logLine('god: ' + (godMode ? 'вкл' : 'выкл'), 'ok');
});

registerCommand('noclip', 'ходить сквозь стены', 'noclip', () => {
  noclipMode = !noclipMode;
  logLine('noclip: ' + (noclipMode ? 'вкл' : 'выкл'), 'ok');
});

registerCommand('stamina', 'установить стамину', 'stamina <0-100>', (args) => {
  const n = parseFloat(args[0]);
  if (isNaN(n)) { logLine('нужно число', 'err'); return; }
  stamina.cur = Math.max(0, Math.min(STAM_MAX, n));
  stamina.exhausted = false;
  logLine('стамина: ' + n, 'ok');
});

registerCommand('event', 'запустить ивент (birthday/supply/silence/blackout/kart)', 'event <type>', (args) => {
  const type = args[0];
  if (!['birthday', 'supply', 'silence', 'blackout', 'kart'].includes(type)) {
    logLine('типы: birthday, supply, silence, blackout, kart', 'err'); return;
  }
  endEvent();
  startEvent(type);
  logLine('ивент: ' + type, 'ok');
});

registerCommand('timescale', 'скорость времени', 'timescale <0.1-3>', (args) => {
  const n = parseFloat(args[0]);
  if (isNaN(n) || n < 0.1 || n > 3) { logLine('0.1 – 3.0', 'err'); return; }
  timeScale = n;
  logLine('timescale: ' + n, 'ok');
});

registerCommand('clear', 'очистить консоль', 'clear', () => { consoleLog.innerHTML = ''; });

registerCommand('exit', 'закрыть консоль', 'exit', () => { closeConsole(); });

/* ─── клавиатура консоли ─── */
consoleField.addEventListener('keydown', e => {
  if (e.key === 'Enter') {
    runCommand(consoleField.value);
    consoleField.value = '';
  } else if (e.key === 'Escape') {
    closeConsole();
  }
  e.stopPropagation();
});

/* ═══════════════════════════════════════════════════════════
   ИВЕНТЫ
   ═══════════════════════════════════════════════════════════ */
function updateEvents(dt) {
  if (eventSys.active) {
    eventSys.timeLeft -= dt;
    if (eventSys.timeLeft <= 0) endEvent();
    return;
  }
  eventSys.nextTimer -= dt;
  if (eventSys.nextTimer <= 0) {
    const roll = Math.random();
    let type;
    if (roll < 0.20) type = 'birthday';
    else if (roll < 0.38) type = 'supply';
    else if (roll < 0.54) type = 'silence';
    else if (roll < 0.70) type = 'blackout';
    else type = 'kart';
    startEvent(type);
    eventSys.nextTimer = 40 + Math.random() * 40;
  }
}
function startEvent(type) {
  eventSys.active = type;
  if (type === 'birthday') {
    eventSys.timeLeft = 22;
    eventMsgEl.textContent = '♥ PARTY TIME ♥';
    const ang = player.yaw + (Math.random() - 0.5);
    let mx = player.x + Math.cos(ang) * 10, my = player.y + Math.sin(ang) * 10;
    for (let i = 0; i < 20; i++) {
      if (!solid(mx, my)) break;
      mx = player.x + Math.cos(ang + i * 0.3) * (10 + i * 0.5);
      my = player.y + Math.sin(ang + i * 0.3) * (10 + i * 0.5);
    }
    monster.x = mx; monster.y = my;
    monster.active = true; monster.mode = 'party_approach'; monster.hat = true;
    monster.partyTimer = 20; monster.partyDanceT = 0;
  } else if (type === 'supply') {
    eventSys.timeLeft = 1;
    eventMsgEl.textContent = '✦ SUPPLY DROP ✦';
    for (let i = 0; i < 3; i++) {
      const ang = Math.random() * Math.PI * 2, d = 3 + Math.random() * 4;
      const ex = player.x + Math.cos(ang) * d, ey = player.y + Math.sin(ang) * d;
      if (!solid(ex, ey)) energyDrops.push({ x: ex, y: ey });
    }
  } else if (type === 'silence') {
    eventSys.timeLeft = 6;
    eventMsgEl.textContent = '◌ SILENCE ◌';
    if (masterGain && audioCtx) masterGain.gain.setTargetAtTime(0.001, audioCtx.currentTime, 0.1);
  } else if (type === 'blackout') {
    eventSys.timeLeft = 8;
    eventMsgEl.textContent = '⚠ BLACKOUT ⚠';
    blackoutActive = true;
  } else if (type === 'kart') {
    eventSys.timeLeft = 60;
    eventMsgEl.textContent = '🏁 KART RACE 🏁';
    startKartRace();
  }
}
function endEvent() {
  if (eventSys.active === 'silence' && masterGain && audioCtx) masterGain.gain.setTargetAtTime(0.05, audioCtx.currentTime, 0.3);
  if (eventSys.active === 'birthday' || eventSys.active === 'kart') {
    if (monster.mode === 'party_approach' || monster.mode === 'party_dance' || monster.mode === 'kart') {
      monster.active = false; monster.mode = 'normal'; monster.hat = false;
      monster.idleTimer = 20;
    }
    kartRace.active = false;
  }
  if (eventSys.active === 'blackout') blackoutActive = false;
  eventSys.active = null;
  eventMsgEl.textContent = '';
}
function startKartRace() {
  const dirs = [0, Math.PI/2, Math.PI, -Math.PI/2, Math.PI/4, -Math.PI/4, 3*Math.PI/4, -3*Math.PI/4];
  let bestDir = 0, bestDist = 0;
  for (const d of dirs) {
    let free = 0;
    for (let dist = 5; dist <= 80; dist += 2) {
      if (solid(player.x + Math.cos(d) * dist, player.y + Math.sin(d) * dist)) break;
      free = dist;
    }
    if (free > bestDist) { bestDist = free; bestDir = d; }
  }
  if (bestDist < 25) { endEvent(); return; }
  kartRace.active = true; kartRace.playerWon = false; kartRace.monsterWon = false;
  kartRace.finishX = player.x + Math.cos(bestDir) * (bestDist - 3);
  kartRace.finishY = player.y + Math.sin(bestDir) * (bestDist - 3);
  const perpAng = bestDir + Math.PI * 0.5;
  let placed = false;
  for (let a = 0; a < 60 && !placed; a++) {
    const ang = perpAng + (a % 2 === 0 ? 1 : -1) * (a * 0.08);
    const dx = player.x + Math.cos(ang) * 4, dy = player.y + Math.sin(ang) * 4;
    if (!solid(dx, dy)) { monster.x = dx; monster.y = dy; placed = true; }
  }
  if (!placed) { monster.x = player.x - Math.cos(bestDir) * 4; monster.y = player.y - Math.sin(bestDir) * 4; }
  monster.active = true; monster.mode = 'kart'; monster.state = 'hunting';
  monster.stunTimer = 0; monster.distractTimer = 0; monster.hat = false; monster.hasLOS = true;
}

/* ═══════════════════════════════════════════════════════════
   АУДИО
   ═══════════════════════════════════════════════════════════ */
let audioCtx = null, monsterGain = null, masterGain = null;
let lastPlayerStep = 0, breathTimer = 0;
function startAudio() {
  if (audioCtx) return;
  try {
    audioCtx = new (window.AudioContext || window.webkitAudioContext)();
    masterGain = audioCtx.createGain();
    masterGain.gain.value = 0.05;
    masterGain.connect(audioCtx.destination);
    const filt = audioCtx.createBiquadFilter();
    filt.type = 'lowpass'; filt.frequency.value = 240;
    filt.connect(masterGain);
    [60, 120.5, 180.7].forEach((freq, i) => {
      const o = audioCtx.createOscillator();
      o.type = i === 0 ? 'sawtooth' : 'sine';
      o.frequency.value = freq;
      const g = audioCtx.createGain();
      g.gain.value = i === 0 ? 0.5 : 0.25;
      o.connect(g); g.connect(filt); o.start();
    });
    monsterGain = audioCtx.createGain();
    monsterGain.gain.value = 0;
    monsterGain.connect(masterGain);
    const rg = audioCtx.createBiquadFilter();
    rg.type = 'lowpass'; rg.frequency.value = 180;
    rg.connect(monsterGain);
    const o1 = audioCtx.createOscillator();
    o1.type = 'sawtooth'; o1.frequency.value = 42;
    const g1 = audioCtx.createGain(); g1.gain.value = 0.45;
    o1.connect(g1); g1.connect(rg); o1.start();
  } catch (err) {}
}
function playPlayerStep(isSprint) {
  if (!audioCtx) return;
  const t = audioCtx.currentTime;
  const o = audioCtx.createOscillator();
  const g = audioCtx.createGain();
  const f = audioCtx.createBiquadFilter();
  f.type = 'lowpass'; f.frequency.value = 400;
  o.type = 'triangle';
  o.frequency.setValueAtTime(90 + Math.random() * 30, t);
  o.frequency.exponentialRampToValueAtTime(40, t + 0.08);
  g.gain.setValueAtTime(isSprint ? 0.06 : 0.035, t);
  g.gain.exponentialRampToValueAtTime(0.001, t + 0.10);
  o.connect(f); f.connect(g); g.connect(masterGain);
  o.start(t); o.stop(t + 0.12);
}
function playMonsterStep(dist) {
  if (!audioCtx) return;
  const t = audioCtx.currentTime;
  const vol = Math.max(0, 1 - dist / 22);
  if (vol <= 0.01) return;
  const o = audioCtx.createOscillator();
  const g = audioCtx.createGain();
  const f = audioCtx.createBiquadFilter();
  f.type = 'lowpass'; f.frequency.value = 220;
  o.type = 'sawtooth';
  o.frequency.setValueAtTime(55 + Math.random() * 20, t);
  o.frequency.exponentialRampToValueAtTime(28, t + 0.12);
  g.gain.setValueAtTime(vol * 0.12, t);
  g.gain.exponentialRampToValueAtTime(0.001, t + 0.15);
  o.connect(f); f.connect(g); g.connect(masterGain);
  o.start(t); o.stop(t + 0.18);
}
function playHeartbeat(vol) {
  if (!audioCtx || vol <= 0.01) return;
  const t = audioCtx.currentTime;
  for (let i = 0; i < 2; i++) {
    const dt2 = i * 0.14;
    const o = audioCtx.createOscillator();
    const g = audioCtx.createGain();
    o.type = 'sine';
    o.frequency.setValueAtTime(65, t + dt2);
    o.frequency.exponentialRampToValueAtTime(35, t + dt2 + 0.10);
    g.gain.setValueAtTime(vol * (i === 0 ? 0.15 : 0.10), t + dt2);
    g.gain.exponentialRampToValueAtTime(0.001, t + dt2 + 0.14);
    o.connect(g); g.connect(masterGain);
    o.start(t + dt2); o.stop(t + dt2 + 0.16);
  }
}
function playBreath(tired) {
  if (!audioCtx || !masterGain) return;
  const t = audioCtx.currentTime;
  const vol = 0.02 + tired * 0.05;
  const buf = audioCtx.createBuffer(1, audioCtx.sampleRate * 0.35, audioCtx.sampleRate);
  const d = buf.getChannelData(0);
  for (let i = 0; i < d.length; i++) {
    d[i] = (Math.random() * 2 - 1) * Math.sin(i / d.length * Math.PI);
  }
  const src = audioCtx.createBufferSource();
  src.buffer = buf;
  const filt = audioCtx.createBiquadFilter();
  filt.type = 'bandpass'; filt.frequency.value = 600 + tired * 400; filt.Q.value = 0.8;
  const g = audioCtx.createGain();
  g.gain.value = vol;
  src.connect(filt); filt.connect(g); g.connect(masterGain);
  src.start(t);
}

/* ═══════════════════════════════════════════════════════════
   ВВОД
   ═══════════════════════════════════════════════════════════ */
const keys = { w: false, a: false, s: false, d: false, shift: false };
function clearMovementKeys() {
  keys.w = false;
  keys.a = false;
  keys.s = false;
  keys.d = false;
  keys.shift = false;
}

window.addEventListener('keydown', e => {
  if (consoleOpen) return;
  const k = e.key.toLowerCase();
  if (k === 'w' || k === 'ц' || k === 'arrowup') keys.w = true;
  if (k === 's' || k === 'ы' || k === 'arrowdown') keys.s = true;
  if (k === 'a' || k === 'ф' || k === 'arrowleft') keys.a = true;
  if (k === 'd' || k === 'в' || k === 'arrowright') keys.d = true;
  if (k === 'shift') keys.shift = true;
  // Повтор клавиши нужен только для непрерывного движения, но не для действий.
  if (e.repeat) {
    if (['arrowup','arrowdown','arrowleft','arrowright',' '].includes(k)) e.preventDefault();
    return;
  }
  if (k >= '1' && k <= '5') activateSlot(parseInt(k) - 1);
  if (k === 'e' || k === 'у') useActiveItem();
  if (k === 'f' || k === 'а') {
    const item = activeSlot >= 0 ? inventory[activeSlot] : null;
    if (item && item.type === 'can') throwCan();
    else if (item && item.type === 'mop') useMop(activeSlot);
    else if (beer.t > 0) tryPunch();
  }
  if (k === 'l' || k === 'л') toggleLeaderboard();
  if (k === '/' || k === '.') { e.preventDefault(); openConsole(); return; }
  if (['arrowup','arrowdown','arrowleft','arrowright',' '].includes(k)) e.preventDefault();
});
window.addEventListener('keyup', e => {
  const k = e.key.toLowerCase();
  if (k === 'w' || k === 'ц' || k === 'arrowup') keys.w = false;
  if (k === 's' || k === 'ы' || k === 'arrowdown') keys.s = false;
  if (k === 'a' || k === 'ф' || k === 'arrowleft') keys.a = false;
  if (k === 'd' || k === 'в' || k === 'arrowright') keys.d = false;
  if (k === 'shift') keys.shift = false;
});
window.addEventListener('blur', clearMovementKeys);
document.addEventListener('visibilitychange', () => {
  if (document.hidden) clearMovementKeys();
});
document.addEventListener('mousemove', e => {
  if (document.pointerLockElement !== canvas) return;
  targetYaw += e.movementX * 0.0018;
});

/* ═══════════════════════════════════════════════════════════
   РЕНДЕР
   ═══════════════════════════════════════════════════════════ */
function drawSprite(tex, tw, th, wx, wy, sizeH, fl, W, H, px, py, dirX, dirY, planeX, planeY, horizon, arcOffset) {
  const sx = wx - px, sy = wy - py;
  const invDet = 1 / (planeX * dirY - dirX * planeY);
  const tx = invDet * (dirY * sx - dirX * sy);
  const ty = invDet * (-planeY * sx + planeX * sy);
  if (ty <= 0.15 || ty > 22) return;
  const centerX = (W * 0.5) * (1 + tx / ty);
  let floorY = horizon + (H * 0.5) / ty;
  if (arcOffset) floorY -= arcOffset * (H * 0.5) / ty * 0.5;
  const spriteHpx = sizeH * H / ty;
  const spriteWpx = spriteHpx * (tw / th);
  const dStartX = Math.max(0, Math.floor(centerX - spriteWpx * 0.5));
  const dEndX = Math.min(W, Math.ceil(centerX + spriteWpx * 0.5));
  const dStartY = Math.max(0, Math.floor(floorY - spriteHpx));
  const dEndY = Math.min(H, Math.ceil(floorY));
  const fogD = currentLevel === 2 ? 0.03 : currentLevel === 3 ? 0.085 : currentLevel === 1 ? 0.07 : FOG_D;
  let f = ty * fogD;
  if (f > 1) f = 1;
  f = f * f * (3 - 2 * f) * 0.94;
  const kk = (1 - f) * fl;
  const fr2 = currentLevel === 2 ? 35 * f : currentLevel === 3 ? 54 * f : currentLevel === 1 ? 18 * f : FOG_R * f;
  const fg2 = currentLevel === 2 ? 55 * f : currentLevel === 3 ? 7 * f : currentLevel === 1 ? 20 * f : FOG_G * f;
  const fb2 = currentLevel === 2 ? 65 * f : currentLevel === 3 ? 12 * f : currentLevel === 1 ? 24 * f : FOG_B * f;
  const vTop = floorY - spriteHpx;
  for (let x = dStartX; x < dEndX; x++) {
    if (ty >= depth[x]) continue;
    const u = (x - centerX + spriteWpx * 0.5) / spriteWpx;
    if (u < 0 || u >= 1) continue;
    const texX = (u * tw) | 0;
    if (texX >= tw) continue;
    for (let y = dStartY; y < dEndY; y++) {
      const v = (y - vTop) / spriteHpx;
      if (v < 0 || v >= 1) continue;
      const texY = (v * th) | 0;
      if (texY >= th) continue;
      const c = tex[texY * tw + texX];
      if ((c >>> 24) === 0) continue;
      buf[y * W + x] = 0xFF000000 |
        (((((c >> 16) & 255) * kk + fb2) | 0) << 16) |
        (((((c >> 8) & 255) * kk + fg2) | 0) << 8) |
        ((((c & 255) * kk + fr2) | 0));
    }
  }
}

function render() {
  const W = cw, H = ch;
  const px = player.x, py = player.y;
  const dirX = Math.cos(player.yaw), dirY = Math.sin(player.yaw);
  const planeX = -dirY * PLANE, planeY = dirX * PLANE;
  const horizon = (H * 0.5 + player.bob) | 0;
  const isL2 = currentLevel === 2, isL1 = currentLevel === 1 || currentLevel === 3;

  let fl = flicker;
  if (blackoutActive) fl *= 0.08;
  if (isL2) fl = 0.97 + 0.03 * Math.sin(performance.now() * 0.001);

  waterOverlay.style.opacity = isL2 ? '1' : '0';
  waterOverlay.classList.toggle('pool-surge', isL2 && poolCurrent.active > 0);
  document.body.classList.toggle('crimson-level', currentLevel === 3);
  document.body.classList.toggle('crimson-alarm', currentLevel === 3 && crimsonAlarm.active > 0);

  const fogD = isL2 ? 0.03 : currentLevel === 3 ? 0.085 : isL1 ? 0.07 : FOG_D;
  const fogR = isL2 ? 35 : currentLevel === 3 ? 54 : isL1 ? 18 : FOG_R;
  const fogG = isL2 ? 55 : currentLevel === 3 ? 7 : isL1 ? 20 : FOG_G;
  const fogB = isL2 ? 65 : currentLevel === 3 ? 12 : isL1 ? 24 : FOG_B;

  /* ─── стены ─── */
  for (let x = 0; x < W; x++) {
    const camX = 2 * x / W - 1;
    const rdx = dirX + planeX * camX;
    const rdy = dirY + planeY * camX;
    let mapX = Math.floor(px), mapY = Math.floor(py);
    const ddx = rdx === 0 ? 1e30 : Math.abs(1 / rdx);
    const ddy = rdy === 0 ? 1e30 : Math.abs(1 / rdy);
    let stepX, stepY, sdx, sdy;
    if (rdx < 0) { stepX = -1; sdx = (px - mapX) * ddx; }
    else { stepX = 1; sdx = (mapX + 1 - px) * ddx; }
    if (rdy < 0) { stepY = -1; sdy = (py - mapY) * ddy; }
    else { stepY = 1; sdy = (mapY + 1 - py) * ddy; }
    let side = 0, hit = false, hitX = 0, hitY = 0;
    for (let i = 0; i < 52; i++) {
      if (sdx < sdy) { sdx += ddx; mapX += stepX; side = 0; }
      else { sdy += ddy; mapY += stepY; side = 1; }
      if (wallAt(mapX, mapY)) { hit = true; hitX = mapX; hitY = mapY; break; }
    }
    if (!hit) { wallTop[x] = 0; wallBot[x] = 0; depth[x] = 1e30; continue; }
    const perp = side === 0 ? (sdx - ddx) : (sdy - ddy);
    depth[x] = perp;
    const isPortalWall = portalActive && hitX === Math.floor(portalX) && hitY === Math.floor(portalY);
    let texArr = isL2 ? wallTexL2 : isL1 ? wallTexL1 : wallTex;
    if (isPortalWall) texArr = portalTex;
    let wallX = side === 0 ? py + perp * rdy : px + perp * rdx;
    wallX -= Math.floor(wallX);
    let texX = (wallX * TEX) | 0;
    if (texX > TMASK) texX = TMASK;
    if (side === 0 ? rdx > 0 : rdy < 0) texX = TMASK - texX;
    const lineH = H / perp;
    let y0 = (horizon - lineH * 0.5) | 0;
    let y1 = (horizon + lineH * 0.5) | 0;
    if (y0 < 0) y0 = 0; if (y1 > H) y1 = H;
    wallTop[x] = y0; wallBot[x] = y1;
    if (y0 >= y1) continue;
    const stepTex = TEX / lineH;
    let texPos = (y0 - horizon + lineH * 0.5) * stepTex;
    let f = perp * fogD;
    if (f > 1) f = 1;
    f = f * f * (3 - 2 * f) * 0.94;
    const k = (1 - f) * (side === 1 ? 0.70 : 1.0) * fl;
    const fr = fogR * f, fg = fogG * f, fb = fogB * f;
    for (let y = y0; y < y1; y++) {
      let ty = texPos | 0;
      if (ty > TMASK) ty = TMASK; else if (ty < 0) ty = 0;
      texPos += stepTex;
      const c = texArr[(ty << TSHIFT) | texX];
      let r = (c & 255) * k + fr;
      let g = ((c >> 8) & 255) * k + fg;
      let b = ((c >> 16) & 255) * k + fb;
      if (isPortalWall) {
        const pulse = 0.7 + 0.3 * Math.sin(performance.now() * 0.006 + y * 0.1);
        r *= pulse; g *= pulse * 0.6; b *= pulse * 1.2;
      }
      buf[y * W + x] = 0xFF000000 | ((b | 0) << 16) | ((g | 0) << 8) | (r | 0);
    }
  }

  /* ─── пол / потолок ─── */
  const activePuddles = [];
  for (let i = 0; i < puddles.length; i++) {
    const p = puddles[i];
    const dx = p.x - px, dy = p.y - py;
    if (dx * dx + dy * dy < 400) activePuddles.push(p);
  }

  const rdx0 = dirX - planeX, rdy0 = dirY - planeY;
  const rdx1 = dirX + planeX, rdy1 = dirY + planeY;
  const wt = wallTop, wb = wallBot;
  const t = performance.now();
  /* анимация воды — один общий фазовый сдвиг */
  const waterPhase = t * 0.0015;
  const causticFrame = ((t * 1.1) | 0) & (WATER_CAUSTIC_FRAMES - 1);

  for (let y = 0; y < H; y++) {
    const dy = y - horizon;
    const base = y * W;
    if (dy === 0) {
      const fc = 0xFF000000 | (fogB << 16) | (fogG << 8) | fogR;
      for (let x = 0; x < W; x++) if (y < wt[x] || y >= wb[x]) buf[base + x] = fc;
      continue;
    }
    const ady = dy < 0 ? -dy : dy;
    const rowDist = (H * 0.5) / ady;
    const isCeil = dy < 0;
    const stX = rowDist * (rdx1 - rdx0) / W;
    const stY = rowDist * (rdy1 - rdy0) / W;
    let fx = px + rowDist * rdx0;
    let fy = py + rowDist * rdy0;
    let f = rowDist * fogD;
    if (f > 1) f = 1;
    f = f * f * (3 - 2 * f) * 0.94;
    const k = (1 - f) * fl;
    const fr = fogR * f, fg = fogG * f, fb = fogB * f;

    for (let x = 0; x < W; x++) {
      if (y >= wt[x] && y < wb[x]) { fx += stX; fy += stY; continue; }
      const tx = Math.floor(fx * TEX) & TMASK;
      const ty = Math.floor(fy * TEX) & TMASK;
      let r, g, b;

      if (isCeil) {
        const ct = isL2 ? ceilTexL2 : isL1 ? ceilTexL1 : ceilTex;
        const c = ct[(ty << TSHIFT) | tx];
        r = c & 255; g = (c >> 8) & 255; b = (c >> 16) & 255;
        if (isL1) {
          const lx = Math.floor(fx / 4), ly = Math.floor(fy / 4);
          if (hash(lx, ly, 888) > 0.92 && Math.abs(fx - lx * 4 - 2) < 0.8 && Math.abs(fy - ly * 4 - 2) < 0.8) {
            r = 240 * fl; g = 220 * fl; b = 180 * fl;
          }
        } else if (!isL2) {
          const rbx = Math.floor(fx / B), rby = Math.floor(fy / B);
          const rcx = rbx * B + B * 0.5, rcy = rby * B + B * 0.5;
          if (Math.abs(fx - rcx) < 1.1 && Math.abs(fy - rcy) < 1.1) {
            r = 252 * fl; g = 245 * fl; b = 208 * fl;
          }
        }
      } else {
        let wetPuddle = false;
        for (let pi = 0; pi < activePuddles.length; pi++) {
          const p = activePuddles[pi];
          const pdx = fx - p.x, pdy = fy - p.y;
          if (pdx * pdx + pdy * pdy < p.r * p.r) { wetPuddle = true; break; }
        }
        if (wetPuddle) {
          const pc = mopPuddleTex[(ty << TSHIFT) | tx];
          r = pc & 255; g = (pc >> 8) & 255; b = (pc >> 16) & 255;
        } else if (isL2) {
          /* ОПТИМИЗИРОВАНО: простая аддитивная вода без fbm на пиксель */
          const tc = floorTexL2[(ty << TSHIFT) | tx];
          r = tc & 255; g = (tc >> 8) & 255; b = (tc >> 16) & 255;
          /* накладываем полупрозрачный слой воды из текстуры */
          const wc = waterOverlayTexL2[((ty + ((waterPhase * 8) & 63)) << TSHIFT) | tx];
          const wr = wc & 255, wg = (wc >> 8) & 255, wb2 = (wc >> 16) & 255;
          r = (r * 0.55 + wr * 0.45);
          g = (g * 0.55 + wg * 0.45);
          b = (b * 0.55 + wb2 * 0.45);
          // Готовая таблица бликов заменяет дорогой Math.sin на каждом пикселе.
          const caustic = waterCausticLUT[causticFrame * TEX * TEX + (ty << TSHIFT) + tx] / 255;
          r *= caustic; g *= caustic; b *= caustic;
        } else {
          const ft = isL1 ? floorTexL1 : floorTex;
          const c = ft[(ty << TSHIFT) | tx];
          r = c & 255; g = (c >> 8) & 255; b = (c >> 16) & 255;
          if (isL1) {
            const pn = vnoise(fx * 0.3, fy * 0.3, 300);
            if (pn > 0.62) {
              const pc = puddleTex[(ty << TSHIFT) | tx];
              const tt = 0.6;
              r = r * (1 - tt) + (pc & 255) * tt;
              g = g * (1 - tt) + ((pc >> 8) & 255) * tt;
              b = b * (1 - tt) + ((pc >> 16) & 255) * tt;
            }
          }
        }
      }
      buf[base + x] = 0xFF000000 | (((b * k + fb) | 0) << 16) | (((g * k + fg) | 0) << 8) | ((r * k + fr) | 0);
      fx += stX; fy += stY;
    }
  }

  /* ─── спрайты ─── */
  for (let i = 0; i < activePuddles.length; i++) {
    const p = activePuddles[i];
    drawSprite(wetFloorSignTex, WF_W, WF_H, p.signX, p.signY, 0.6, fl, W, H, px, py, dirX, dirY, planeX, planeY, horizon);
  }
  for (let i = 0; i < energyDrops.length; i++) {
    const e = energyDrops[i];
    drawSprite(energyTex, ENW, ENH, e.x, e.y, 0.42, fl, W, H, px, py, dirX, dirY, planeX, planeY, horizon);
  }
  for (let i = 0; i < echoDrops.length; i++) {
    const e = echoDrops[i];
    const pulse = 0.48 + Math.sin(performance.now() * 0.004 + e.x) * 0.05;
    drawSprite(echoTex, ECHOW, ECHOH, e.x, e.y, pulse, fl, W, H, px, py, dirX, dirY, planeX, planeY, horizon);
  }
  for (let i = 0; i < mopDrops.length; i++) {
    const e = mopDrops[i];
    drawSprite(mopTex, MOPW, MOPH, e.x, e.y, 0.55, fl, W, H, px, py, dirX, dirY, planeX, planeY, horizon);
  }
  for (let i = 0; i < radarDrops.length; i++) {
    const e = radarDrops[i];
    drawSprite(radarTex, RDW, RDH, e.x, e.y, 0.30, fl, W, H, px, py, dirX, dirY, planeX, planeY, horizon);
  }
  for (let i = 0; i < beerDrops.length; i++) {
    const e = beerDrops[i];
    drawSprite(beerTex, BEWW, BEWH, e.x, e.y, 0.38, fl, W, H, px, py, dirX, dirY, planeX, planeY, horizon);
  }
  for (let i = 0; i < landedCans.length; i++) {
    const e = landedCans[i];
    drawSprite(crushedCanTex, CCW, CCH, e.x, e.y, 0.20, fl, W, H, px, py, dirX, dirY, planeX, planeY, horizon);
  }
  // Портал находится в свободной точке пола, поэтому его нужно рисовать как спрайт,
  // а не пытаться подменять им текстуру стены в raycaster.
  if (portalActive) {
    const portalSize = 1.35 + Math.sin(performance.now() * 0.004) * 0.08;
    drawSprite(portalTex, TEX, TEX, portalX, portalY, portalSize, fl, W, H,
      px, py, dirX, dirY, planeX, planeY, horizon);
  }
  for (let i = 0; i < thrownCans.length; i++) {
    const c = thrownCans[i];
    const p = c.t / c.duration;
    const wx = c.sx + (c.ex - c.sx) * p;
    const wy = c.sy + (c.ey - c.sy) * p;
    const arc = Math.sin(p * Math.PI) * 0.8;
    drawSprite(crushedCanTex, CCW, CCH, wx, wy, 0.20, fl, W, H, px, py, dirX, dirY, planeX, planeY, horizon, arc);
  }
  if (bucket.active) {
    drawSprite(bucketTex, BKW, BKH, bucket.x, bucket.y, 0.34, fl, W, H, px, py, dirX, dirY, planeX, planeY, horizon);
  }
  if (kartRace.active) {
    drawSprite(finishTex, FINW, FINH, kartRace.finishX, kartRace.finishY, 0.06, fl, W, H, px, py, dirX, dirY, planeX, planeY, horizon);
    if (monster.active && monster.mode === 'kart') {
      drawSprite(monsterKartTex, KMW, KMH, monster.x, monster.y, 0.20, fl, W, H, px, py, dirX, dirY, planeX, planeY, horizon);
    }
  }

  /* монстр */
  if (monster.active) {
    const isParty = monster.mode === 'party_dance' || monster.mode === 'party_approach';
    const isStunned = monster.stunTimer > 0;
    const sx = monster.x - px, sy = monster.y - py;
    const invDet = 1 / (planeX * dirY - dirX * planeY);
    const tx = invDet * (dirY * sx - dirX * sy);
    const ty = invDet * (-planeY * sx + planeX * sy);
    if (ty > 0.12) {
      const centerX = (W * 0.5) * (1 + tx / ty);
      const floorY = horizon + (H * 0.5) / ty;
      const spriteHpx = 1.05 * H / ty;
      const spriteWpx = spriteHpx * (MSW / MSH);
      const now = performance.now();
      let jitterX = 0, jitterY = 0;
      if (!isParty) {
        jitterX = Math.sin(now * 0.013) * (spriteWpx * 0.012);
        jitterY = Math.cos(now * 0.017) * (spriteHpx * 0.008);
      }
      let stunWobble = 0;
      if (isStunned) {
        stunWobble = Math.sin(now * 0.022) * spriteWpx * 0.12;
        jitterY += Math.cos(now * 0.03) * spriteHpx * 0.02;
      }
      let danceOffset = 0;
      if (monster.mode === 'party_dance') {
        danceOffset = Math.sin(monster.partyDanceT * 8) * spriteHpx * 0.04;
      }
      const finalCenterX = centerX + stunWobble;
      const dStartX = Math.max(0, Math.floor(finalCenterX - spriteWpx * 0.5 + jitterX));
      const dEndX = Math.min(W, Math.ceil(finalCenterX + spriteWpx * 0.5 + jitterX));
      const dStartY = Math.max(0, Math.floor(floorY - spriteHpx + jitterY + danceOffset));
      const dEndY = Math.min(H, Math.ceil(floorY + jitterY + danceOffset));
      let f = ty * fogD;
      if (f > 1) f = 1;
      f = f * f * (3 - 2 * f) * 0.94;
      const k = (1 - f) * fl;
      const fr = fogR * f, fg = fogG * f, fb = fogB * f;
      let eyePulse;
      if (isParty) eyePulse = 1.0;
      else if (isStunned) eyePulse = 0.25;
      else eyePulse = 0.7 + 0.35 * Math.sin(now * 0.014);
      const breatheScale = 1 + Math.sin(monster.breathe * 3.5) * 0.022;
      const vTop = floorY - spriteHpx * breatheScale + danceOffset;
      for (let x = dStartX; x < dEndX; x++) {
        if (ty >= depth[x]) continue;
        const u = (x - finalCenterX - jitterX + spriteWpx * 0.5) / spriteWpx;
        if (u < 0 || u >= 1) continue;
        const texX = (u * MSW) | 0;
        if (texX >= MSW) continue;
        for (let y = dStartY; y < dEndY; y++) {
          const v = (y - vTop) / (spriteHpx * breatheScale);
          if (v < 0 || v >= 1) continue;
          const texY = (v * MSH) | 0;
          if (texY >= MSH) continue;
          const c = monsterTex[texY * MSW + texX];
          if ((c >>> 24) === 0) continue;
          let r = c & 255, g = (c >> 8) & 255, b = (c >> 16) & 255;
          if (r > 100 && g < 80 && b < 80) {
            r *= eyePulse * 1.55; g *= eyePulse * 0.7; b *= eyePulse * 0.7;
            if (r > 255) r = 255;
          }
          r = r * k + fr; g = g * k + fg; b = b * k + fb;
          buf[y * W + x] = 0xFF000000 | ((b | 0) << 16) | ((g | 0) << 8) | (r | 0);
        }
      }
      if (monster.hat && dStartX < dEndX) {
        const hatCenterX = Math.floor(finalCenterX);
        if (hatCenterX >= 0 && hatCenterX < W && ty < depth[hatCenterX]) {
          const hatBaseY = Math.floor(vTop);
          const hatH = Math.floor(spriteHpx * 0.16);
          const hatWidth = spriteWpx * 0.42;
          for (let dy = 0; dy < hatH; dy++) {
            const rowY = hatBaseY - dy;
            if (rowY < 0 || rowY >= H) continue;
            const halfW = hatWidth * (1 - dy / hatH) * 0.5;
            for (let dx = -halfW; dx <= halfW; dx++) {
              const px2 = Math.floor(hatCenterX + dx);
              if (px2 < 0 || px2 >= W) continue;
              if (ty >= depth[px2]) continue;
              const v = 0.85 + hash(px2, rowY, 500) * 0.15;
              buf[rowY * W + px2] = pack(230 * v, 80 * v, 200 * v) | 0xFF000000;
            }
          }
        }
      }
      if (isStunned && dStartX < dEndX) {
        const headCenterX = Math.floor(finalCenterX);
        const headTopY = Math.floor(vTop) - 4;
        const tt = now * 0.005;
        for (let s = 0; s < 3; s++) {
          const angle = tt + s * (Math.PI * 2 / 3);
          const starX = Math.floor(headCenterX + Math.cos(angle) * spriteWpx * 0.12);
          const starY = Math.floor(headTopY + Math.sin(angle) * spriteHpx * 0.03);
          if (starX >= 0 && starX < W && starY >= 0 && starY < H && ty < depth[starX]) {
            buf[starY * W + starX] = pack(255, 240, 80) | 0xFF000000;
          }
        }
      }
    }
  }

  /* предмет в руке */
  if (activeSlot >= 0 && inventory[activeSlot]) {
    const item = inventory[activeSlot];
    let tex, tw, th;
    if (item.type === 'energy') { tex = handEnergyTex; tw = HNW; th = HNH; }
    else if (item.type === 'can') { tex = handCanTex; tw = HCNW; th = HCNH; }
    else if (item.type === 'mop') { tex = handMopTex; tw = HMW; th = HMH; }
    else if (item.type === 'radar') { tex = handRadarTex; tw = HRW; th = HRH; }
    else if (item.type === 'beer') { tex = handBeerTex; tw = HBW; th = HBH; }
    else tex = null;
    if (tex) {
      const shake = boost.t > 0 ? Math.sin(performance.now() * 0.05) * 2 : 0;
      const bobX = player.bob * 0.5;
      const bobY = Math.sin(player.bobT) * 1.5;
      const handScale = Math.round(H * 0.42 / th);
      const dispW = tw * handScale, dispH = th * handScale;
      const offsetX = Math.round(W * 0.72 + bobX + shake);
      const offsetY = Math.round(H * 0.55 + bobY + Math.abs(player.bob) * 0.3);
      for (let sy = 0; sy < dispH; sy++) {
        const dy = offsetY + sy;
        if (dy < 0 || dy >= H) continue;
        const srcY = ((sy / handScale) | 0);
        if (srcY >= th) continue;
        for (let sx = 0; sx < dispW; sx++) {
          const dx = offsetX + sx;
          if (dx < 0 || dx >= W) continue;
          const srcX = ((sx / handScale) | 0);
          if (srcX >= tw) continue;
          const c = tex[srcY * tw + srcX];
          if ((c >>> 24) === 0) continue;
          const idx = dy * W + dx;
          const old = buf[idx];
          const a = 0.88;
          const r = (c & 255) * a + (old & 255) * (1 - a);
          const g = ((c >> 8) & 255) * a + ((old >> 8) & 255) * (1 - a);
          const b = ((c >> 16) & 255) * a + ((old >> 16) & 255) * (1 - a);
          buf[idx] = 0xFF000000 | ((b | 0) << 16) | ((g | 0) << 8) | (r | 0);
        }
      }
    }
  }

  /* руль карта */
  if (kartRace.active) {
    const tt = performance.now();
    const dispScale = Math.max(1, Math.round(W * 0.55 / KAW));
    const dispW = KAW * dispScale, dispH = KAH * dispScale;
    const offX = Math.round((W - dispW) / 2);
    const offY = Math.round(H - dispH + Math.sin(tt * 0.008) * 2);
    for (let sy = 0; sy < dispH; sy++) {
      const dy = offY + sy;
      if (dy < 0 || dy >= H) continue;
      const srcY = (sy / dispScale) | 0;
      if (srcY >= KAH) continue;
      for (let sx = 0; sx < dispW; sx++) {
        const dx = offX + sx;
        if (dx < 0 || dx >= W) continue;
        const srcX = (sx / dispScale) | 0;
        if (srcX >= KAW) continue;
        const c = handKartTex[srcY * KAW + srcX];
        if ((c >>> 24) === 0) continue;
        buf[dy * W + dx] = c;
      }
    }
  }

  ctx.putImageData(img, 0, 0);
}

/* ═══════════════════════════════════════════════════════════
   СТРЕЛКИ
   ═══════════════════════════════════════════════════════════ */
const dirMarkersEl = document.getElementById('dirMarkers');
const arrowEls = [];
for (let i = 0; i < 4; i++) {
  const el = document.createElement('div');
  el.className = 'dirArrow';
  el.textContent = '➤';
  dirMarkersEl.appendChild(el);
  arrowEls.push(el);
}

function updateDirectionMarker() {
  const now = performance.now();
  const isParty = monster.mode === 'party_dance' || monster.mode === 'party_approach';
  const isStunned = monster.stunTimer > 0;
  const W = window.innerWidth, H = window.innerHeight;
  const cx = W / 2, cy = H / 2;
  if (!monster.active || isParty) {
    for (let i = 0; i < 2; i++) arrowEls[i].style.opacity = '0';
  } else {
    const dx = monster.x - player.x, dy = monster.y - player.y;
    const dist = Math.sqrt(dx * dx + dy * dy);
    let relAngle = Math.atan2(dy, dx) - player.yaw;
    while (relAngle > Math.PI) relAngle -= Math.PI * 2;
    while (relAngle < -Math.PI) relAngle += Math.PI * 2;
    if (monster.hasLOS && Math.abs(relAngle) < 0.6 && !isStunned && monster.mode !== 'kart') {
      for (let i = 0; i < 2; i++) arrowEls[i].style.opacity = '0';
    } else {
      const alpha = (0.15 + Math.max(0, 1 - dist / 40) * 0.85) * (isStunned ? 0.5 : 1);
      const radius = Math.min(W, H) * 0.38;
      const ax = cx + Math.sin(relAngle) * radius;
      const ay = cy - Math.cos(relAngle) * radius;
      const main = arrowEls[0];
      main.style.left = (ax - 18) + 'px';
      main.style.top = (ay - 18) + 'px';
      main.style.transform = `rotate(${relAngle * 180 / Math.PI + 90}deg)`;
      main.style.opacity = String(alpha);
      main.style.color = isStunned ? '#5090c0' : (monster.hasLOS ? '#ff3020' : '#c84030');
      arrowEls[1].style.opacity = '0';
    }
  }

  if (portalActive) {
    const dx = portalX - player.x, dy = portalY - player.y;
    let relAngle = Math.atan2(dy, dx) - player.yaw;
    while (relAngle > Math.PI) relAngle -= Math.PI * 2;
    while (relAngle < -Math.PI) relAngle += Math.PI * 2;
    const radius = Math.min(W, H) * 0.42;
    const ax = cx + Math.sin(relAngle) * radius;
    const ay = cy - Math.cos(relAngle) * radius;
    const p = arrowEls[2];
    p.style.left = (ax - 18) + 'px';
    p.style.top = (ay - 18) + 'px';
    p.style.transform = `rotate(${relAngle * 180 / Math.PI + 90}deg)`;
    p.style.opacity = '0.85';
    p.style.color = '#c060ff';
    p.style.fontSize = '26px';
    p.textContent = '◈';
  } else arrowEls[2].style.opacity = '0';

  if (kartRace.active) {
    const dx = kartRace.finishX - player.x, dy = kartRace.finishY - player.y;
    let relAngle = Math.atan2(dy, dx) - player.yaw;
    while (relAngle > Math.PI) relAngle -= Math.PI * 2;
    while (relAngle < -Math.PI) relAngle += Math.PI * 2;
    const radius = Math.min(W, H) * 0.44;
    const ax = cx + Math.sin(relAngle) * radius;
    const ay = cy - Math.cos(relAngle) * radius;
    const p = arrowEls[3];
    p.style.left = (ax - 18) + 'px';
    p.style.top = (ay - 18) + 'px';
    p.style.transform = `rotate(${relAngle * 180 / Math.PI + 90}deg)`;
    p.style.opacity = '0.9';
    p.style.color = '#ffc840';
    p.style.fontSize = '28px';
    p.textContent = '🏁';
  } else arrowEls[3].style.opacity = '0';
}

/* ═══════════════════════════════════════════════════════════
   ОБНОВЛЕНИЕ
   ═══════════════════════════════════════════════════════════ */
let heartTimer = 0;

function update(dt, now) {
  if (deathTimer > 0) { deathTimer -= dt; updateScreamer(dt); return; }
  if (screamerActive) { updateScreamer(dt); return; }

  const smoothFactor = Math.min(1, dt * 20);
  player.yaw += (targetYaw - player.yaw) * smoothFactor;

  const scoreRate = currentLevel === 2 ? SCORE_PER_SEC_L2 : currentLevel === 1 ? SCORE_PER_SEC_L1 : SCORE_PER_SEC_L0;
  score += scoreRate * dt;

  /* новая комната */
  const bx = Math.floor(player.x / B), by = Math.floor(player.y / B);
  const roomKey = bx + ',' + by;
  if (!visitedRooms.has(roomKey)) { visitedRooms.add(roomKey); score += SCORE_PER_ROOM; }

  if (!portalActive) {
    const targetScore = currentLevel === 0 ? PORTAL_SCORE_L1 : currentLevel === 1 ? PORTAL_SCORE_L2 : Infinity;
    if (score >= targetScore) activatePortal();
  }

  scanRooms();
  updateItemPickup();
  updateThrownCans(dt);
  updateEvents(dt);

  // Периодическое течение Poolrooms: предупреждает игрока и сносит его по залу.
  if (currentLevel === 3) {
    if (crimsonAlarm.active > 0) {
      crimsonAlarm.active=Math.max(0,crimsonAlarm.active-dt);
      if (crimsonAlarm.active===0) { crimsonAlarm.timer=27+Math.random()*17; if(eventSys.active===null) eventMsgEl.textContent='▰ АВАРИЙНЫЙ СВЕТ ПОГАС'; }
    } else {
      crimsonAlarm.timer-=dt;
      if(crimsonAlarm.timer<=0) { crimsonAlarm.active=7; if(eventSys.active===null) eventMsgEl.textContent='⚠ ТРЕВОГА! ОНО СЛЫШИТ ТЕБЯ!'; }
    }
  } else { crimsonAlarm.active=0; crimsonAlarm.timer=24; }

  if (currentLevel === 2) {
    if (poolCurrent.active > 0) {
      poolCurrent.active = Math.max(0, poolCurrent.active - dt);
      if (poolCurrent.active === 0) {
        poolCurrent.timer = 27 + Math.random() * 18;
        if (eventSys.active === null) eventMsgEl.textContent = '≈ ТЕЧЕНИЕ УСПОКОИЛОСЬ';
      }
    } else {
      poolCurrent.timer -= dt;
      if (poolCurrent.timer <= 0) {
        poolCurrent.active = 6.5;
        poolCurrent.angle = Math.random() * Math.PI * 2;
        if (eventSys.active === null) eventMsgEl.textContent = '⚠ СИЛЬНОЕ ТЕЧЕНИЕ! ДЕРЖИСЬ!';
      }
    }
  } else {
    poolCurrent.active = 0;
    poolCurrent.timer = 26;
  }

  if (radar.t > 0) radar.t -= dt;
  if (beer.t > 0) beer.t -= dt;
  if (beer.punchCd > 0) beer.punchCd -= dt;

  for (let i = puddles.length - 1; i >= 0; i--) {
    puddles[i].life -= dt;
    if (puddles[i].life <= 0) puddles.splice(i, 1);
  }
  for (let i = landedCans.length - 1; i >= 0; i--) {
    landedCans[i].t += dt;
    if (landedCans[i].t > 60) landedCans.splice(i, 1);
  }

  const hasMop = inventory.some(it => it && it.type === 'mop');
  bucket.active = hasMop;
  if (hasMop) {
    const side = player.yaw + 2.4;
    const tx = player.x + Math.cos(side) * 0.8;
    const ty = player.y + Math.sin(side) * 0.8;
    bucket.x += (tx - bucket.x) * Math.min(1, dt * 5);
    bucket.y += (ty - bucket.y) * Math.min(1, dt * 5);
  }

  if (portalActive) {
    portalMsgTimer -= dt;
    if (portalMsgTimer <= 0) {
      portalMsgTimer = 0.5;
      const dx = portalX - player.x, dy = portalY - player.y;
      const dist = Math.sqrt(dx * dx + dy * dy);
      if (eventSys.active === null) {
        eventMsgEl.textContent = `◈ ПОРТАЛ: ${directionTo(Math.atan2(dy, dx))} ${Math.round(dist)}м`;
      }
    }
  }

  checkPortal();

  if (kartRace.active && !kartRace.playerWon && !kartRace.monsterWon) {
    const fdx = kartRace.finishX - player.x, fdy = kartRace.finishY - player.y;
    if (fdx * fdx + fdy * fdy < 2.5) {
      kartRace.playerWon = true;
      score += 100;
      eventMsgEl.textContent = '🏆 ВЫ ФИНИШИРОВАЛИ ПЕРВЫМ! +100 🏆';
      setTimeout(() => endEvent(), 2000);
    }
  }

  if (boost.t > 0) boost.t -= dt;

  const boosted = boost.t > 0;
  const canSprint = keys.shift && !stamina.exhausted && !boosted;
  const isFast = boosted || canSprint;
  let speedMult = 1.0;
  if (boosted) speedMult = BOOST_MULT;
  else if (canSprint) speedMult = 1.9;
  if (beer.t > 0) speedMult *= BEER_SLOW;
  if (kartRace.active) speedMult *= 1.6;
  if (currentLevel === 2) speedMult *= 0.85;
  if (currentLevel === 3 && crimsonAlarm.active > 0) speedMult *= 0.92;

  const baseSpeed = currentLevel === 2 ? 2.8 : currentLevel === 1 ? 2.6 : 3.0;
  const speed = baseSpeed * speedMult * dt * timeScale;
  const cs = Math.cos(player.yaw), sn = Math.sin(player.yaw);
  let mx = 0, my = 0;
  if (keys.w) { mx += cs; my += sn; }
  if (keys.s) { mx -= cs; my -= sn; }
  if (keys.a) { mx += sn; my -= cs; }
  if (keys.d) { mx -= sn; my += cs; }
  const len = Math.sqrt(mx * mx + my * my);
  const moving = len > 0;
  if (currentLevel === 2 && poolCurrent.active > 0) {
    const drift = 0.72 * dt * timeScale;
    const dx = Math.cos(poolCurrent.angle) * drift;
    const dy = Math.sin(poolCurrent.angle) * drift;
    if (canWalk(player.x + dx, player.y)) player.x += dx;
    if (canWalk(player.x, player.y + dy)) player.y += dy;
    if (moving && canSprint) stamina.cur = Math.max(0, stamina.cur - 5 * dt);
  }
  if (moving) {
    mx = mx / len * speed; my = my / len * speed;
    if (canSprint) { noisePulse.x = player.x; noisePulse.y = player.y; noisePulse.t = 1.15; }
    if (canWalk(player.x + mx, player.y)) player.x += mx;
    if (canWalk(player.x, player.y + my)) player.y += my;
    player.bobT += dt * (isFast ? 13 : 8.5);
    const stepInterval = isFast ? 260 : 480;
    if (now - lastPlayerStep > stepInterval) {
      lastPlayerStep = now;
      playPlayerStep(isFast);
    }
  }
  if (moving && canSprint) {
    stamina.cur -= STAM_DRAIN * dt;
    if (stamina.cur <= 0) { stamina.cur = 0; stamina.exhausted = true; }
  } else {
    stamina.cur += (moving ? STAM_REGEN : STAM_IDLE) * dt;
    if (stamina.cur > STAM_MAX) stamina.cur = STAM_MAX;
    if (stamina.exhausted && stamina.cur >= STAM_RECOVER) stamina.exhausted = false;
  }
  if (currentLevel === 2) stamina.cur = Math.min(STAM_MAX, stamina.cur + dt * 1.5);

  const baseBob = moving ? Math.sin(player.bobT) * 2.4 : 0;
  const beerBob = beer.t > 0 ? Math.sin(now * 0.003) * 7 + Math.cos(now * 0.005) * 5 : 0;
  player.bob += ((baseBob + beerBob) - player.bob) * Math.min(1, dt * 12);

  if (beer.t > 0) {
    const wobble = Math.sin(now * 0.002) * 20;
    viewEl.style.filter = `blur(0.8px) hue-rotate(${wobble}deg) saturate(1.3) brightness(1.05)`;
    viewEl.style.transform = `translateX(${Math.sin(now * 0.0015) * 5}px) translateY(${Math.cos(now * 0.0025) * 4}px)`;
  } else if (viewEl.style.filter) {
    viewEl.style.filter = '';
    viewEl.style.transform = '';
  }

  const t = now * 0.001;
  flicker = 0.945 + 0.055 * Math.sin(t * 8.3) * Math.sin(t * 2.17 + 1.3);
  if (currentLevel === 2) flicker = 0.97 + 0.03 * Math.sin(now * 0.001);
  else if (currentLevel === 3) flicker = crimsonAlarm.active > 0 ? 0.35 + 0.25 * Math.sin(now * 0.025) : 0.88 + 0.12 * Math.sin(now * 0.004);
  else if (currentLevel === 1) { if (hash((now * 0.03) | 0, 5, 7) > 0.96) flicker *= 0.25; }
  else { if (hash((now * 0.02) | 0, 3, 9) > 0.982) flicker *= 0.42; }
  if (flicker < 0.15) flicker = 0.15;

  if (noisePulse.t > 0) noisePulse.t = Math.max(0, noisePulse.t - dt);
  updateMonster(dt * timeScale, now);

  staminaFill.style.width = stamina.cur + '%';
  staminaFill.classList.toggle('exhausted', stamina.exhausted);
  scoreEl.textContent = Math.floor(score);
  energyEl.textContent = energyCollected;
  echoEl.textContent = `${echoCount}/${ECHO_GOAL}`;

  let danger = 0;
  const isParty = monster.mode === 'party_dance' || monster.mode === 'party_approach';
  const isStunned = monster.stunTimer > 0;
  if (monster.active && !isParty && !isStunned && monster.mode !== 'kart') {
    const d = monster.dist;
    danger = Math.max(0, 1 - d / 14);
    if (monster.hasLOS) danger = Math.min(1, danger * 1.3);
    if (monsterGain && audioCtx) {
      const vol = Math.max(0, 1 - d / 22) * (monster.hasLOS ? 0.10 : 0.06);
      monsterGain.gain.setTargetAtTime(vol, audioCtx.currentTime, 0.15);
    }
    heartTimer -= dt;
    if (danger > 0.15) {
      const hbInterval = 1.4 - danger * 0.95;
      if (heartTimer <= 0) { heartTimer = hbInterval; playHeartbeat(danger * 0.9); }
    }
  } else if (monsterGain && audioCtx) {
    monsterGain.gain.setTargetAtTime(0, audioCtx.currentTime, 0.3);
  }

  breathTimer -= dt;
  if (breathTimer <= 0) {
    const tiredFactor = 1 - stamina.cur / STAM_MAX;
    const interval = 2.2 - tiredFactor * 1.1 - (moving && canSprint ? 0.6 : 0);
    breathTimer = Math.max(0.55, interval);
    playBreath(tiredFactor);
  }

  dangerEl.style.opacity = (danger * 0.9).toFixed(2);
  boostEl.style.opacity = (boosted ? 0.8 : 0).toFixed(2);

  updateDirectionMarker();
  drawRadarOverlay();
}

/* ─── радар ─── */
const radarCanvas = document.getElementById('radarCanvas');
const radarCtx = radarCanvas.getContext('2d');
function drawRadarOverlay() {
  if (radar.t <= 0) { radarCanvas.style.display = 'none'; return; }
  radarCanvas.style.display = 'block';
  const W = 140, H = 140, cx = W / 2, cy = H / 2, R = W / 2 - 6;
  radarCtx.clearRect(0, 0, W, H);
  radarCtx.beginPath(); radarCtx.arc(cx, cy, R, 0, Math.PI * 2);
  radarCtx.fillStyle = 'rgba(15, 35, 20, 0.85)'; radarCtx.fill();
  radarCtx.strokeStyle = '#50c060'; radarCtx.lineWidth = 2; radarCtx.stroke();
  radarCtx.strokeStyle = 'rgba(80, 192, 96, 0.35)'; radarCtx.lineWidth = 1;
  radarCtx.beginPath();
  radarCtx.moveTo(cx - R, cy); radarCtx.lineTo(cx + R, cy);
  radarCtx.moveTo(cx, cy - R); radarCtx.lineTo(cx, cy + R);
  radarCtx.stroke();
  radarCtx.beginPath(); radarCtx.arc(cx, cy, R * 0.5, 0, Math.PI * 2); radarCtx.stroke();
  radarCtx.fillStyle = '#80ff90';
  radarCtx.beginPath(); radarCtx.arc(cx, cy, 3, 0, Math.PI * 2); radarCtx.fill();
  if (monster.active) {
    const dx = monster.x - player.x, dy = monster.y - player.y;
    const dist = Math.sqrt(dx * dx + dy * dy);
    const scale = Math.min(1, dist / 25);
    const ang = Math.atan2(dy, dx) - player.yaw - Math.PI / 2;
    const mx = cx + Math.cos(ang) * R * scale;
    const my = cy + Math.sin(ang) * R * scale;
    radarCtx.fillStyle = '#ff3020';
    radarCtx.beginPath(); radarCtx.arc(mx, my, 4, 0, Math.PI * 2); radarCtx.fill();
  }
}

/* ═══════════════════════════════════════════════════════════
   СТАРТ И ЦИКЛ
   ═══════════════════════════════════════════════════════════ */
const startEl = document.getElementById('start');
let running = false;
let last = 0, fpsAcc = 0, fpsCnt = 0, fpsT = 0;

startEl.addEventListener('click', () => {
  startEl.classList.add('hidden');
  tryPointerLock();
  startAudio();
  if (audioCtx && audioCtx.state === 'suspended') audioCtx.resume();
  running = true;
  last = performance.now();
  renderLeaderboard();
});
function tryPointerLock(retries = 3) {
  if (!canvas.requestPointerLock) return;
  try {
    const p = canvas.requestPointerLock();
    if (p && p.catch) {
      p.catch(() => { if (retries > 0) setTimeout(() => tryPointerLock(retries - 1), 600); });
    }
  } catch (err) { if (retries > 0) setTimeout(() => tryPointerLock(retries - 1), 600); }
}
document.addEventListener('pointerlockchange', () => {
  if (document.pointerLockElement !== canvas) {
    clearMovementKeys();
    if (!consoleOpen) {
      running = false;
      startEl.classList.remove('hidden');
    }
  }
});

function loop(now) {
  requestAnimationFrame(loop);
  let dt = (now - last) * 0.001;
  last = now;
  if (!running) dt = 0;
  if (dt > 0.06) dt = 0.06;
  if (dt > 0) update(dt, now);
  render();
  fpsCnt++;
  if (now - fpsT >= 500) {
    fpsEl.textContent = String(Math.round(fpsCnt * 1000 / Math.max(1, now - fpsT)));
    fpsCnt = 0; fpsT = now;
  }
}
last = performance.now();
requestAnimationFrame(loop);

})();