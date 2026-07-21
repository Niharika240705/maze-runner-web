#!/usr/bin/env python
# coding: utf-8

# In[1]:

# (pip install removed)


# In[2]:


# pyrefly: ignore [missing-import]
import pygame


# In[3]:


"""
Maze Runner with Kruskal's Algorithm (maze generation) and
Dijkstra's Algorithm (pathfinding).
"""

# pyrefly: ignore [missing-import]
import pygame, random, heapq
from collections import defaultdict, deque

# -----------------------
# Config
# -----------------------
TILE = 24
ROWS, COLS = 21, 31   # must be odd
SCREEN_W, SCREEN_H = COLS*TILE, ROWS*TILE+40
FPS = 60

PLAYER_SPEED = 6.0
ENEMY_SPEED = 3.0
DIJKSTRA_RECOMPUTE_FRAMES = 12
TIMER_SECONDS = 120
COINS = 12

# Colors
WALL_COLOR = (30,30,30)
FLOOR_COLOR = (220,220,220)
PLAYER_COLOR = (60,120,220)
ENEMY_COLOR = (220,60,60)
EXIT_COLOR = (40,180,40)
COIN_COLOR = (230,180,20)
UI_BG = (25,25,25)
UI_TEXT = (240,240,240)

# -----------------------
# Maze Generation: Kruskal
# -----------------------
def kruskal_maze(rows, cols, seed=None):
    rng = random.Random(seed)
    grid = [[1 for _ in range(cols)] for _ in range(rows)]

    # Each cell treated as disjoint set node
    parent = {}
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    def union(a,b):
        ra, rb = find(a), find(b)
        parent[rb] = ra

    # Init sets
    cells = [(r,c) for r in range(1,rows,2) for c in range(1,cols,2)]
    for c in cells: parent[c] = c
    for r,c in cells: grid[r][c] = 0

    # All walls between neighboring cells
    edges = []
    for r,c in cells:
        for dr,dc in [(2,0),(0,2)]:
            nr,nc = r+dr,c+dc
            if (nr,nc) in parent:
                w = rng.random()
                edges.append(((r,c),(nr,nc),w))
    rng.shuffle(edges)

    # Kruskal’s MST
    for a,b,w in sorted(edges, key=lambda x:x[2]):
        if find(a)!=find(b):
            union(a,b)
            # knock down wall
            wall = ((a[0]+b[0])//2,(a[1]+b[1])//2)
            grid[wall[0]][wall[1]] = 0

    return grid

# -----------------------
# Pathfinding: Dijkstra
# -----------------------
def dijkstra(grid,start,goal):
    dist = {start:0}
    parent = {}
    pq = [(0,start)]
    visited=set()
    while pq:
        d,u = heapq.heappop(pq)
        if u in visited: continue
        visited.add(u)
        if u==goal: break
        for dr,dc in [(-1,0),(1,0),(0,-1),(0,1)]:
            v=(u[0]+dr,u[1]+dc)
            if not (0<=v[0]<len(grid) and 0<=v[1]<len(grid[0])): continue
            if grid[v[0]][v[1]]==1: continue
            nd = d+1
            if nd<dist.get(v,1e9):
                dist[v]=nd; parent[v]=u
                heapq.heappush(pq,(nd,v))
    if goal not in parent and goal!=start: return None
    path=[goal];
    while path[-1]!=start: path.append(parent[path[-1]])
    return path[::-1]

# -----------------------
# Helpers
# -----------------------
def farthest_cell(grid,start):
    q=deque([start]); dist={start:0}; last=start
    while q:
        u=q.popleft(); last=u
        for dr,dc in [(-1,0),(1,0),(0,-1),(0,1)]:
            v=(u[0]+dr,u[1]+dc)
            if 0<=v[0]<len(grid) and 0<=v[1]<len(grid[0]) and grid[v[0]][v[1]]==0 and v not in dist:
                dist[v]=dist[u]+1; q.append(v)
    return last, dist

class Entity:
    def __init__(self,cell,color,speed):
        self.cell=cell; self.color=color; self.speed=speed
        self.moving=False; self.next=None; self.progress=0
    def start_move(self,target): self.moving=True; self.next=target; self.progress=0
    def tick(self,dt):
        if not self.moving: return
        self.progress+=dt*self.speed
        if self.progress>=1:
            self.cell=self.next; self.moving=False; self.progress=0
    def get_pos(self):
        r,c=self.cell
        if self.moving:
            r+= (self.next[0]-self.cell[0])*self.progress
            c+= (self.next[1]-self.cell[1])*self.progress
        return r,c
    def draw(self,surf,offy=0):
        r,c=self.get_pos()
        pygame.draw.rect(surf,self.color,(c*TILE+2,offy+r*TILE+2,TILE-4,TILE-4))

# -----------------------
# Game
# -----------------------
class MazeRunner:
    def __init__(self):
        pygame.init()
        self.screen=pygame.display.set_mode((SCREEN_W,SCREEN_H))
        pygame.display.set_caption("Maze Runner - Kruskal + Dijkstra")
        self.font=pygame.font.SysFont(None,20); self.big=pygame.font.SysFont(None,28)
        self.clock=pygame.time.Clock()
        self.seed=random.randrange(1_000_000_000)   # FIXED
        self.reset(self.seed)
    def reset(self,seed):
        self.seed=seed
        self.grid=kruskal_maze(ROWS,COLS,seed)
        self.start=(1,1); self.exit,_=farthest_cell(self.grid,self.start)
        self.player=Entity(self.start,PLAYER_COLOR,PLAYER_SPEED)
        open_cells=[(r,c) for r in range(ROWS) for c in range(COLS) if self.grid[r][c]==0 and (r,c)!=self.start and (r,c)!=self.exit]
        rng=random.Random(seed)
        self.coins=set(rng.sample(open_cells,min(COINS,len(open_cells))))
        self.enemy=Entity(rng.choice(open_cells),ENEMY_COLOR,ENEMY_SPEED)
        self.enemy_path=[]; self.frames=0
        self.state='RUNNING'; self.timer=TIMER_SECONDS
        self.collected=0
    def handle_input(self):
        if self.player.moving: return
        keys=pygame.key.get_pressed()
        for dr,dc,key in [(-1,0,pygame.K_UP),(1,0,pygame.K_DOWN),(0,-1,pygame.K_LEFT),(0,1,pygame.K_RIGHT)]:
            if keys[key]:
                r,c=self.player.cell; nr,nc=r+dr,c+dc
                if 0<=nr<ROWS and 0<=nc<COLS and self.grid[nr][nc]==0:
                    self.player.start_move((nr,nc)); break
    def update(self,dt):
        if self.state!='RUNNING': return
        self.timer-=dt;
        if self.timer<=0: self.state='LOST'
        self.player.tick(dt)
        if not self.player.moving:
            if self.player.cell in self.coins:
                self.coins.remove(self.player.cell); self.collected+=1
            if self.player.cell==self.exit and len(self.coins)==0: self.state='WON'
        # enemy logic: recompute dijkstra path every few frames
        self.frames+=1; self.enemy.tick(dt)
        if not self.enemy.moving:
            if self.frames%DIJKSTRA_RECOMPUTE_FRAMES==0 or not self.enemy_path:
                p=dijkstra(self.grid,self.enemy.cell,self.player.cell)
                if p and len(p)>1: self.enemy_path=p[1:]
            if self.enemy_path:
                nxt=self.enemy_path.pop(0); self.enemy.start_move(nxt)
        # Collision detection (float-based check to prevent tunneling when passing through each other)
        pr, pc = self.player.get_pos()
        er, ec = self.enemy.get_pos()
        dist = ((pr - er)**2 + (pc - ec)**2)**0.5
        if dist < 0.7: self.state='LOST'
    def draw(self):
        s=self.screen; s.fill(UI_BG)
        for r in range(ROWS):
            for c in range(COLS):
                rect=(c*TILE,r*TILE,TILE,TILE)
                pygame.draw.rect(s,WALL_COLOR if self.grid[r][c] else FLOOR_COLOR,rect)
        
        # Draw exit: active (green) if all coins collected, otherwise locked (gray/dim red)
        if len(self.coins) == 0:
            pygame.draw.rect(s,EXIT_COLOR,(self.exit[1]*TILE+2,self.exit[0]*TILE+2,TILE-4,TILE-4))
        else:
            pygame.draw.rect(s,(100,100,100),(self.exit[1]*TILE+2,self.exit[0]*TILE+2,TILE-4,TILE-4))
            pygame.draw.rect(s,(60,60,60),(self.exit[1]*TILE+TILE//3,self.exit[0]*TILE+TILE//3,TILE//3,TILE//3))
            
        for r,c in self.coins: pygame.draw.circle(s,COIN_COLOR,(c*TILE+TILE//2,r*TILE+TILE//2),TILE//4)
        self.enemy.draw(s); self.player.draw(s)
        pygame.draw.rect(s,UI_BG,(0,ROWS*TILE,SCREEN_W,40))
        s.blit(self.big.render(f"Time: {int(max(0,self.timer))}",1,UI_TEXT),(8,ROWS*TILE+5))
        s.blit(self.font.render(f"Coins: {self.collected}/{COINS}",1,UI_TEXT),(150,ROWS*TILE+10))
        
        # Draw status text
        if len(self.coins) > 0:
            status_text = "Collect all coins!"
            status_color = COIN_COLOR
        else:
            status_text = "Exit open! Reach exit!"
            status_color = EXIT_COLOR
            
        if self.state == 'WON':
            status_text = "VICTORY!"
            status_color = EXIT_COLOR
        elif self.state == 'LOST':
            status_text = "GAME OVER!"
            status_color = ENEMY_COLOR
            
        s.blit(self.font.render(status_text,1,status_color),(280,ROWS*TILE+10))
        
        # Draw end-game overlay
        if self.state != 'RUNNING':
            overlay = pygame.Surface((SCREEN_W, SCREEN_H), pygame.SRCALPHA)
            if self.state == 'WON':
                overlay.fill((40, 180, 40, 150))  # Greenish tint
                title_text = "VICTORY!"
                sub_text = "You successfully navigated the maze!"
            else:
                overlay.fill((180, 40, 40, 150))  # Reddish tint
                title_text = "GAME OVER"
                if self.timer <= 0:
                    sub_text = "Out of time!"
                else:
                    sub_text = "Caught by the enemy!"
            
            title_surf = self.big.render(title_text, True, (255, 255, 255))
            sub_surf = self.font.render(sub_text, True, (255, 255, 255))
            restart_surf = self.font.render("Press 'R' to Retry Same Maze | 'N' for New Maze", True, (255, 255, 255))
            
            title_rect = title_surf.get_rect(center=(SCREEN_W // 2, SCREEN_H // 2 - 35))
            sub_rect = sub_surf.get_rect(center=(SCREEN_W // 2, SCREEN_H // 2 + 5))
            restart_rect = restart_surf.get_rect(center=(SCREEN_W // 2, SCREEN_H // 2 + 35))
            
            overlay.blit(title_surf, title_rect)
            overlay.blit(sub_surf, sub_rect)
            overlay.blit(restart_surf, restart_rect)
            s.blit(overlay, (0, 0))
    def run(self):
        run=True
        while run:
            dt=self.clock.tick(FPS)/1000
            for e in pygame.event.get():
                if e.type==pygame.QUIT: run=False
                if e.type==pygame.KEYDOWN:
                    if e.key==pygame.K_ESCAPE: run=False
                    if e.key==pygame.K_r: self.reset(self.seed)
                    if e.key==pygame.K_n: self.reset(random.randrange(1_000_000_000))   # FIXED
            if self.state=='RUNNING': self.handle_input()
            self.update(dt); self.draw(); pygame.display.flip()
        pygame.quit()

if __name__=="__main__":
    MazeRunner().run()


# In[ ]:





# In[ ]:




