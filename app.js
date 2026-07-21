/**
 * Maze Runner - HTML5 Game Engine
 * Features: Kruskal's Maze Generation, Dijkstra Pathfinding AI,
 * Smooth movement interpolation, Particle systems, Premium effects.
 */

// -------------------------------------------------------------------------
// Game Configuration
// -------------------------------------------------------------------------
const TILE = 28; // Size of each tile in pixels
const ROWS = 21; // Must be odd
const COLS = 31; // Must be odd
const FPS = 60;

const PLAYER_SPEED = 6.5;
const ENEMY_SPEED = 3.2;
const DIJKSTRA_RECOMPUTE_FRAMES = 12;
const TIMER_SECONDS = 120;
const COINS_COUNT = 12;

// Colors
const COLOR_WALL = "#161623";
const COLOR_WALL_BORDER = "#252538";
const COLOR_FLOOR = "#0e0e14";
const COLOR_PLAYER = "#3c78dc";
const COLOR_ENEMY = "#dc3c3c";
const COLOR_COIN = "#e6b414";
const COLOR_EXIT_LOCKED = "#555560";
const COLOR_EXIT_ACTIVE = "#28b428";

// -------------------------------------------------------------------------
// Helper: Seedable LCG Random (for reproducible mazes)
// -------------------------------------------------------------------------
class SeededRandom {
  constructor(seed) {
    this.seed = seed;
  }
  
  // Mulberry32 generator
  next() {
    let t = this.seed += 0x6D2B79F5;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  }

  // Shuffle array deterministically
  shuffle(array) {
    for (let i = array.length - 1; i > 0; i--) {
      const j = Math.floor(this.next() * (i + 1));
      [array[i], array[j]] = [array[j], array[i]];
    }
    return array;
  }

  // Sample array deterministically
  sample(array, count) {
    const shuffled = [...array];
    this.shuffle(shuffled);
    return shuffled.slice(0, count);
  }

  // Choice deterministically
  choice(array) {
    return array[Math.floor(this.next() * array.length)];
  }
}

// -------------------------------------------------------------------------
// Kruskal's Maze Generation Algorithm
// -------------------------------------------------------------------------
function generateKruskalMaze(rows, cols, seed) {
  const rng = new SeededRandom(seed);
  const grid = Array.from({ length: rows }, () => Array(cols).fill(1));

  const parent = {};
  function find(nodeStr) {
    let curr = nodeStr;
    while (parent[curr] !== curr) {
      parent[curr] = parent[parent[curr]];
      curr = parent[curr];
    }
    return curr;
  }
  
  function union(nodeA, nodeB) {
    const ra = find(nodeA);
    const rb = find(nodeB);
    parent[rb] = ra;
  }

  // Initialize nodes for odd rows/cols
  const cells = [];
  for (let r = 1; r < rows; r += 2) {
    for (let c = 1; c < cols; c += 2) {
      const key = `${r},${c}`;
      parent[key] = key;
      grid[r][c] = 0;
      cells.push([r, c]);
    }
  }

  // Generate edges
  const edges = [];
  for (const [r, c] of cells) {
    const key = `${r},${c}`;
    const neighbors = [
      [r + 2, c],
      [r, c + 2]
    ];
    for (const [nr, nc] of neighbors) {
      const nKey = `${nr},${nc}`;
      if (parent[nKey] !== undefined) {
        edges.push({
          a: [r, c],
          b: [nr, nc],
          w: rng.next()
        });
      }
    }
  }

  // Sort edges by weight to generate MST
  edges.sort((x, y) => x.w - y.w);

  for (const edge of edges) {
    const aKey = `${edge.a[0]},${edge.a[1]}`;
    const bKey = `${edge.b[0]},${edge.b[1]}`;
    if (find(aKey) !== find(bKey)) {
      union(aKey, bKey);
      const wr = Math.floor((edge.a[0] + edge.b[0]) / 2);
      const wc = Math.floor((edge.a[1] + edge.b[1]) / 2);
      grid[wr][wc] = 0;
    }
  }

  return grid;
}

// -------------------------------------------------------------------------
// Pathfinding: Dijkstra
// -------------------------------------------------------------------------
function dijkstra(grid, start, goal) {
  const startStr = `${start[0]},${start[1]}`;
  const goalStr = `${goal[0]},${goal[1]}`;
  
  const dist = {};
  dist[startStr] = 0;
  
  const parent = {};
  const pq = [{ d: 0, pos: start }];
  const visited = new Set();
  
  while (pq.length > 0) {
    // Sort array to act as a priority queue
    pq.sort((x, y) => x.d - y.d);
    const curr = pq.shift();
    const u = curr.pos;
    const uStr = `${u[0]},${u[1]}`;
    
    if (visited.has(uStr)) continue;
    visited.add(uStr);
    
    if (u[0] === goal[0] && u[1] === goal[1]) break;
    
    const dirs = [[-1, 0], [1, 0], [0, -1], [0, 1]];
    for (const [dr, dc] of dirs) {
      const nr = u[0] + dr;
      const nc = u[1] + dc;
      if (nr < 0 || nr >= grid.length || nc < 0 || nc >= grid[0].length) continue;
      if (grid[nr][nc] === 1) continue;
      
      const vStr = `${nr},${nc}`;
      const nd = curr.d + 1;
      const oldD = dist[vStr] !== undefined ? dist[vStr] : Infinity;
      
      if (nd < oldD) {
        dist[vStr] = nd;
        parent[vStr] = u;
        pq.push({ d: nd, pos: [nr, nc] });
      }
    }
  }
  
  if (parent[goalStr] === undefined && (start[0] !== goal[0] || start[1] !== goal[1])) {
    return null;
  }
  
  const path = [goal];
  let currStr = goalStr;
  while (currStr !== startStr) {
    const prev = parent[currStr];
    path.push(prev);
    currStr = `${prev[0]},${prev[1]}`;
  }
  path.reverse();
  return path;
}

// -------------------------------------------------------------------------
// Helper: Farthest Cell (BFS)
// -------------------------------------------------------------------------
function farthestCell(grid, start) {
  const startStr = `${start[0]},${start[1]}`;
  const q = [start];
  const dist = {};
  dist[startStr] = 0;
  let last = start;
  
  while (q.length > 0) {
    const u = q.shift();
    last = u;
    const uStr = `${u[0]},${u[1]}`;
    const uDist = dist[uStr];
    
    const dirs = [[-1, 0], [1, 0], [0, -1], [0, 1]];
    for (const [dr, dc] of dirs) {
      const nr = u[0] + dr;
      const nc = u[1] + dc;
      const vStr = `${nr},${nc}`;
      
      if (nr >= 0 && nr < grid.length && nc >= 0 && nc < grid[0].length) {
        if (grid[nr][nc] === 0 && dist[vStr] === undefined) {
          dist[vStr] = uDist + 1;
          q.push([nr, nc]);
        }
      }
    }
  }
  return { last, dist };
}

// -------------------------------------------------------------------------
// Particle Sparkle System
// -------------------------------------------------------------------------
class ParticleSystem {
  constructor() {
    this.particles = [];
  }
  
  spawn(x, y, color, count = 8) {
    for (let i = 0; i < count; i++) {
      const angle = Math.random() * Math.PI * 2;
      const speed = 1 + Math.random() * 3;
      this.particles.push({
        x: x,
        y: y,
        vx: Math.cos(angle) * speed,
        vy: Math.sin(angle) * speed,
        alpha: 1.0,
        decay: 0.02 + Math.random() * 0.03,
        size: 2 + Math.random() * 3,
        color: color
      });
    }
  }
  
  update() {
    for (let i = this.particles.length - 1; i >= 0; i--) {
      const p = this.particles[i];
      p.x += p.vx;
      p.y += p.vy;
      p.alpha -= p.decay;
      if (p.alpha <= 0) {
        this.particles.splice(i, 1);
      }
    }
  }
  
  draw(ctx) {
    ctx.save();
    for (const p of this.particles) {
      ctx.globalAlpha = p.alpha;
      ctx.fillStyle = p.color;
      ctx.beginPath();
      ctx.arc(p.x, p.y, p.size, 0, Math.PI * 2);
      ctx.fill();
    }
    ctx.restore();
  }
}

// -------------------------------------------------------------------------
// Game Entity (Player & Enemy)
// -------------------------------------------------------------------------
class Entity {
  constructor(cell, color, speed) {
    this.cell = cell; // [r, c]
    this.color = color;
    this.speed = speed;
    this.moving = false;
    this.next = null;
    this.progress = 0;
  }
  
  startMove(target) {
    this.moving = true;
    this.next = target;
    this.progress = 0;
  }
  
  tick(dt) {
    if (!this.moving) return;
    this.progress += dt * this.speed;
    if (this.progress >= 1) {
      this.cell = this.next;
      this.moving = false;
      this.next = null;
      this.progress = 0;
    }
  }
  
  getPos() {
    let r = this.cell[0];
    let c = this.cell[1];
    if (this.moving && this.next) {
      r += (this.next[0] - this.cell[0]) * this.progress;
      c += (this.next[1] - this.cell[1]) * this.progress;
    }
    return [r, c];
  }
  
  draw(ctx) {
    const [r, c] = this.getPos();
    const x = c * TILE + TILE / 2;
    const y = r * TILE + TILE / 2;
    const radius = TILE / 2 - 3;
    
    ctx.save();
    ctx.beginPath();
    
    // Add glow
    ctx.shadowBlur = 12;
    ctx.shadowColor = this.color;
    ctx.fillStyle = this.color;
    
    ctx.arc(x, y, radius, 0, Math.PI * 2);
    ctx.fill();
    
    // Core center light
    ctx.shadowBlur = 0;
    ctx.fillStyle = "#ffffff";
    ctx.beginPath();
    ctx.arc(x, y, radius / 2.5, 0, Math.PI * 2);
    ctx.fill();
    
    ctx.restore();
  }
}

// -------------------------------------------------------------------------
// Main Game Engine
// -------------------------------------------------------------------------
class MazeRunnerGame {
  constructor() {
    this.canvas = document.getElementById("gameCanvas");
    this.ctx = this.canvas.getContext("2d");
    
    // Configure Canvas Size
    this.canvas.width = COLS * TILE;
    this.canvas.height = ROWS * TILE;
    
    // UI Elements
    this.timeProgress = document.getElementById("timeProgress");
    this.timeVal = document.getElementById("timeVal");
    this.coinsVal = document.getElementById("coinsVal");
    this.seedVal = document.getElementById("seedVal");
    
    // Modals
    this.gameOverDialog = document.getElementById("gameOverDialog");
    this.victoryDialog = document.getElementById("victoryDialog");
    
    // Buttons
    document.getElementById("btnNewGame").addEventListener("click", () => this.generateNewSeed());
    document.getElementById("btnRestart").addEventListener("click", () => this.reset(this.seed));
    
    document.getElementById("btnLostRetry").addEventListener("click", () => { this.gameOverDialog.close(); this.reset(this.seed); });
    document.getElementById("btnLostNew").addEventListener("click", () => { this.gameOverDialog.close(); this.generateNewSeed(); });
    
    document.getElementById("btnWinRetry").addEventListener("click", () => { this.victoryDialog.close(); this.reset(this.seed); });
    document.getElementById("btnWinNew").addEventListener("click", () => { this.victoryDialog.close(); this.generateNewSeed(); });
    
    // Setup controls
    this.keys = {};
    window.addEventListener("keydown", (e) => this.handleKeyDown(e));
    window.addEventListener("keyup", (e) => { this.keys[e.key] = false; });
    
    // Animation/State Properties
    this.seed = Math.floor(Math.random() * 1000000000);
    this.particles = new ParticleSystem();
    
    this.reset(this.seed);
    
    // Start game loop
    this.lastTime = performance.now();
    this.loop();
  }
  
  generateNewSeed() {
    this.seed = Math.floor(Math.random() * 1000000000);
    this.reset(this.seed);
  }
  
  reset(seed) {
    this.seed = seed;
    this.seedVal.textContent = seed;
    
    this.grid = generateKruskalMaze(ROWS, COLS, seed);
    this.start = [1, 1];
    
    const farthest = farthestCell(this.grid, this.start);
    this.exit = farthest.last;
    
    this.player = new Entity(this.start, COLOR_PLAYER, PLAYER_SPEED);
    
    // Collect open cells for placement
    const openCells = [];
    for (let r = 0; r < ROWS; r++) {
      for (let c = 0; c < COLS; c++) {
        if (this.grid[r][c] === 0 && 
            (r !== this.start[0] || c !== this.start[1]) && 
            (r !== this.exit[0] || c !== this.exit[1])) {
          openCells.push([r, c]);
        }
      }
    }
    
    // Spawn Coins & Enemy deterministically
    const rng = new SeededRandom(seed);
    const coinCells = rng.sample(openCells, Math.min(COINS_COUNT, openCells.length));
    this.coins = new Set(coinCells.map(c => `${c[0]},${c[1]}`));
    
    const enemyCell = rng.choice(openCells);
    this.enemy = new Entity(enemyCell, COLOR_ENEMY, ENEMY_SPEED);
    
    this.enemyPath = [];
    this.frames = 0;
    this.state = "RUNNING";
    this.timer = TIMER_SECONDS;
    this.collected = 0;
    
    this.updateUI();
  }
  
  handleKeyDown(e) {
    this.keys[e.key] = true;
    
    // Handle keyboard hotkeys
    if (e.key.toLowerCase() === 'r') {
      this.gameOverDialog.close();
      this.victoryDialog.close();
      this.reset(this.seed);
    }
    if (e.key.toLowerCase() === 'n') {
      this.gameOverDialog.close();
      this.victoryDialog.close();
      this.generateNewSeed();
    }
  }
  
  handleInput() {
    if (this.player.moving || this.state !== "RUNNING") return;
    
    let dr = 0;
    let dc = 0;
    
    if (this.keys["ArrowUp"] || this.keys["w"] || this.keys["W"]) {
      dr = -1;
    } else if (this.keys["ArrowDown"] || this.keys["s"] || this.keys["S"]) {
      dr = 1;
    } else if (this.keys["ArrowLeft"] || this.keys["a"] || this.keys["A"]) {
      dc = -1;
    } else if (this.keys["ArrowRight"] || this.keys["d"] || this.keys["D"]) {
      dc = 1;
    }
    
    if (dr !== 0 || dc !== 0) {
      const [r, c] = this.player.cell;
      const nr = r + dr;
      const nc = c + dc;
      if (nr >= 0 && nr < ROWS && nc >= 0 && nc < COLS && this.grid[nr][nc] === 0) {
        this.player.startMove([nr, nc]);
      }
    }
  }
  
  update(dt) {
    if (this.state !== "RUNNING") return;
    
    // Timer Countdown
    this.timer -= dt;
    if (this.timer <= 0) {
      this.timer = 0;
      this.triggerGameOver("Out of time!");
      return;
    }
    
    this.player.tick(dt);
    
    // Check coin collection
    if (!this.player.moving) {
      const cellKey = `${this.player.cell[0]},${this.player.cell[1]}`;
      if (this.coins.has(cellKey)) {
        this.coins.delete(cellKey);
        this.collected++;
        
        // Spawn gold particle explosion
        const cx = this.player.cell[1] * TILE + TILE / 2;
        const cy = this.player.cell[0] * TILE + TILE / 2;
        this.particles.spawn(cx, cy, COLOR_COIN, 12);
        
        this.updateUI();
      }
      
      // Check win condition
      if (this.player.cell[0] === this.exit[0] && this.player.cell[1] === this.exit[1]) {
        if (this.coins.size === 0) {
          this.triggerVictory();
          return;
        }
      }
    }
    
    // Enemy logic: Recompute Dijkstra path
    this.frames++;
    this.enemy.tick(dt);
    
    if (!this.enemy.moving) {
      if (this.frames % DIJKSTRA_RECOMPUTE_FRAMES === 0 || this.enemyPath.length === 0) {
        const path = dijkstra(this.grid, this.enemy.cell, this.player.cell);
        if (path && path.length > 1) {
          this.enemyPath = path.slice(1);
        }
      }
      if (this.enemyPath.length > 0) {
        const nxt = this.enemyPath.shift();
        this.enemy.startMove(nxt);
      }
    }
    
    // Visual-based collision check
    const [pr, pc] = this.player.getPos();
    const [er, ec] = this.enemy.getPos();
    const dist = Math.hypot(pr - er, pc - ec);
    if (dist < 0.7) {
      // Spawn red splash
      const px = pr * TILE + TILE/2;
      const py = pc * TILE + TILE/2;
      this.particles.spawn(px, py, COLOR_ENEMY, 24);
      this.triggerGameOver("Caught by the enemy!");
    }
  }
  
  triggerGameOver(reason) {
    this.state = "LOST";
    document.getElementById("lostReason").textContent = reason;
    document.getElementById("lostCoins").textContent = `${this.collected} / ${COINS_COUNT}`;
    document.getElementById("lostTime").textContent = `${Math.ceil(this.timer)}s`;
    this.gameOverDialog.showModal();
    this.updateUI();
  }
  
  triggerVictory() {
    this.state = "WON";
    document.getElementById("winCoins").textContent = `${this.collected} / ${COINS_COUNT}`;
    document.getElementById("winTime").textContent = `${Math.ceil(this.timer)}s`;
    
    // Spawn massive victory green particles
    const ex = this.exit[1] * TILE + TILE / 2;
    const ey = this.exit[0] * TILE + TILE / 2;
    this.particles.spawn(ex, ey, COLOR_EXIT_ACTIVE, 40);
    
    this.victoryDialog.showModal();
    this.updateUI();
  }
  
  updateUI() {
    this.coinsVal.textContent = `${this.collected} / ${COINS_COUNT}`;
    this.timeVal.textContent = `${Math.ceil(this.timer)}s`;
    
    // Update progress bar
    const progressPercent = (this.timer / TIMER_SECONDS) * 100;
    this.timeProgress.style.width = `${progressPercent}%`;
  }
  
  draw() {
    const ctx = this.ctx;
    ctx.clearRect(0, 0, this.canvas.width, this.canvas.height);
    
    // 1. Draw floor grid
    ctx.fillStyle = COLOR_FLOOR;
    ctx.fillRect(0, 0, this.canvas.width, this.canvas.height);
    
    // 2. Draw walls & cells
    for (let r = 0; r < ROWS; r++) {
      for (let c = 0; c < COLS; c++) {
        if (this.grid[r][c] === 1) {
          // Wall
          ctx.fillStyle = COLOR_WALL;
          ctx.fillRect(c * TILE, r * TILE, TILE, TILE);
          
          ctx.strokeStyle = COLOR_WALL_BORDER;
          ctx.lineWidth = 1;
          ctx.strokeRect(c * TILE, r * TILE, TILE, TILE);
        } else {
          // Floor grid line dots
          ctx.fillStyle = "rgba(255, 255, 255, 0.02)";
          ctx.fillRect(c * TILE + TILE/2 - 1, r * TILE + TILE/2 - 1, 2, 2);
        }
      }
    }
    
    // 3. Draw exit portal
    const ex = this.exit[1] * TILE + TILE/2;
    const ey = this.exit[0] * TILE + TILE/2;
    const active = this.coins.size === 0;
    const exitColor = active ? COLOR_EXIT_ACTIVE : COLOR_EXIT_LOCKED;
    
    ctx.save();
    ctx.shadowBlur = active ? 15 : 0;
    ctx.shadowColor = exitColor;
    ctx.strokeStyle = exitColor;
    ctx.lineWidth = 3;
    
    // Draw exit square / circle portal
    ctx.beginPath();
    ctx.arc(ex, ey, TILE / 2 - 4, 0, Math.PI * 2);
    ctx.stroke();
    
    if (active) {
      // Glow fill inner active portal
      ctx.fillStyle = "rgba(40, 180, 40, 0.15)";
      ctx.fill();
    } else {
      // Draw a small lock keyhole icon
      ctx.fillStyle = exitColor;
      ctx.fillRect(ex - 3, ey - 1, 6, 6);
      ctx.beginPath();
      ctx.arc(ex, ey - 2, 3, 0, Math.PI * 2);
      ctx.stroke();
    }
    ctx.restore();
    
    // Draw "GOAL" or "LOCKED" label above exit portal
    ctx.save();
    ctx.font = "bold 9px 'Space Grotesk', sans-serif";
    ctx.fillStyle = exitColor;
    ctx.textAlign = "center";
    ctx.fillText(active ? "GOAL" : "LOCKED", ex, ey - TILE/2 - 5);
    ctx.restore();
    
    // 4. Draw coins
    const pulse = 1 + 0.15 * Math.sin(performance.now() / 150);
    for (const key of this.coins) {
      const [r, c] = key.split(",").map(Number);
      const cx = c * TILE + TILE / 2;
      const cy = r * TILE + TILE / 2;
      
      ctx.save();
      ctx.shadowBlur = 10;
      ctx.shadowColor = COLOR_COIN;
      ctx.fillStyle = COLOR_COIN;
      
      ctx.beginPath();
      ctx.arc(cx, cy, (TILE / 5) * pulse, 0, Math.PI * 2);
      ctx.fill();
      ctx.restore();
    }
    
    // 5. Draw particles
    this.particles.draw(ctx);
    
    // 6. Draw entities
    this.enemy.draw(ctx);
    this.player.draw(ctx);
  }
  
  loop() {
    const now = performance.now();
    const dt = (now - this.lastTime) / 1000;
    this.lastTime = now;
    
    this.handleInput();
    this.update(dt);
    this.particles.update();
    this.draw();
    
    requestAnimationFrame(() => this.loop());
  }
}

// Instantiate engine when DOM is ready
window.addEventListener("DOMContentLoaded", () => {
  new MazeRunnerGame();
});
