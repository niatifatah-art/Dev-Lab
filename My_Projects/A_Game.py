#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Arcadia — fixed single-file text roguelike. Standard library only."""

import heapq
import json
import math
import os
import random
import time
from collections import defaultdict, deque
from pathlib import Path

BASE = Path(__file__).resolve().parent
CONFIG = {
    "width": 60, "height": 30, "max_rooms": 18, "room_min": 4, "room_max": 10,
    "fov": 8, "seed": None, "save": "arcadia_save.json", "log": "arcadia_log.txt",
}
BIOMES = ["Meadow", "Forest", "Desert", "Tundra", "Swamp", "Highlands", "Ruins"]
GLYPH = {"Meadow": ",", "Forest": '"', "Desert": ":", "Tundra": ".", "Swamp": ";", "Highlands": "^", "Ruins": "."}
ITEMS = {
    "Bread": {"kind": "consumable", "heal": 5, "value": 3},
    "Water": {"kind": "consumable", "heal": 3, "value": 2},
    "Health Potion": {"kind": "consumable", "heal": 12, "value": 15},
    "Rusty Sword": {"kind": "equipment", "slot": "Weapon", "atk": 2, "def": 0, "value": 8},
    "Dagger": {"kind": "equipment", "slot": "Weapon", "atk": 2, "def": 0, "value": 10},
    "Iron Sword": {"kind": "equipment", "slot": "Weapon", "atk": 4, "def": 0, "value": 20},
    "Leather Armor": {"kind": "equipment", "slot": "Armor", "atk": 0, "def": 2, "value": 12},
    "Chainmail": {"kind": "equipment", "slot": "Armor", "atk": 0, "def": 4, "value": 25},
    "Coin": {"kind": "money", "value": 1}, "Lockpick": {"kind": "material", "value": 10},
    "Iron Ore": {"kind": "material", "value": 4}, "Wood": {"kind": "material", "value": 2},
    "Herb": {"kind": "material", "value": 2},
}
RECIPES = {
    "Iron Sword": {"needs": {"Iron Ore": 2, "Wood": 1}},
    "Health Potion": {"needs": {"Herb": 2, "Water": 1}},
}


def log(msg):
    try:
        with (BASE / CONFIG["log"]).open("a", encoding="utf-8") as f:
            f.write(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] {msg}\n")
    except OSError:
        pass


def norm_name(s):
    return " ".join(s.strip().lower().split())


def dist(a, b):
    return math.hypot(a[0] - b[0], a[1] - b[1])


class Tile:
    def __init__(self, walk=False, transparent=False, char="#", biome="Meadow"):
        self.walk, self.transparent, self.char, self.biome = walk, transparent, char, biome

    def dump(self):
        return [self.walk, self.transparent, self.char, self.biome]

    @classmethod
    def load(cls, d):
        return cls(bool(d[0]), bool(d[1]), str(d[2]), str(d[3]))


class Rect:
    def __init__(self, x, y, w, h):
        self.x1, self.y1, self.x2, self.y2 = x, y, x + w, y + h

    def center(self):
        return ((self.x1 + self.x2) // 2, (self.y1 + self.y2) // 2)

    def intersects(self, o):
        return not (self.x2 <= o.x1 or self.x1 >= o.x2 or self.y2 <= o.y1 or self.y1 >= o.y2)

    def contains(self, x, y):
        return self.x1 <= x < self.x2 and self.y1 <= y < self.y2

    def dump(self):
        return [self.x1, self.y1, self.x2, self.y2]

    @classmethod
    def load(cls, d):
        r = cls(d[0], d[1], 1, 1); r.x2, r.y2 = d[2], d[3]; return r


class World:
    def __init__(self, w, h):
        self.w, self.h = w, h
        self.tiles = [[Tile() for _ in range(h)] for _ in range(w)]
        self.rooms, self.entities = [], []
        self.items = defaultdict(list)
        self.fog = [[True for _ in range(h)] for _ in range(w)]

    def inside(self, x, y): return 0 <= x < self.w and 0 <= y < self.h
    def walkable(self, x, y): return self.inside(x, y) and self.tiles[x][y].walk

    def entity_at(self, x, y, exclude=None):
        return next((e for e in self.entities if e is not exclude and e.alive and (e.x, e.y) == (x, y)), None)

    def open(self, x, y, exclude=None): return self.walkable(x, y) and self.entity_at(x, y, exclude) is None

    def carve_room(self, r, biome):
        for x in range(r.x1, r.x2):
            for y in range(r.y1, r.y2): self.tiles[x][y] = Tile(True, True, GLYPH[biome], biome)

    def tunnel_h(self, x1, x2, y, biome):
        for x in range(min(x1, x2), max(x1, x2) + 1): self.tiles[x][y] = Tile(True, True, GLYPH[biome], biome)

    def tunnel_v(self, y1, y2, x, biome):
        for y in range(min(y1, y2), max(y1, y2) + 1): self.tiles[x][y] = Tile(True, True, GLYPH[biome], biome)

    def generate(self):
        rooms = []
        for _ in range(CONFIG["max_rooms"] * 4):
            if len(rooms) >= CONFIG["max_rooms"]: break
            rw, rh = random.randint(CONFIG["room_min"], CONFIG["room_max"]), random.randint(CONFIG["room_min"], CONFIG["room_max"])
            r = Rect(random.randint(1, self.w-rw-2), random.randint(1, self.h-rh-2), rw, rh)
            if any(r.intersects(o) for o in rooms): continue
            biome = random.choice(BIOMES); self.carve_room(r, biome)
            if rooms:
                a, b = rooms[-1].center(), r.center()
                if random.random() < .5: self.tunnel_h(a[0], b[0], a[1], biome); self.tunnel_v(a[1], b[1], b[0], biome)
                else: self.tunnel_v(a[1], b[1], a[0], biome); self.tunnel_h(a[0], b[0], b[1], biome)
            rooms.append(r)
        if not rooms:
            r = Rect(self.w//2-3, self.h//2-2, 7, 5); self.carve_room(r, "Meadow"); rooms = [r]
        self.rooms = rooms

    def place(self, e, pos):
        if not self.open(*pos, exclude=e): return False
        e.x, e.y = pos
        if e not in self.entities: self.entities.append(e)
        return True

    def random_open(self, room=None):
        for _ in range(100):
            x = random.randrange(room.x1, room.x2) if room else random.randrange(1, self.w-1)
            y = random.randrange(room.y1, room.y2) if room else random.randrange(1, self.h-1)
            if self.open(x, y): return (x, y)
        return None

    def los(self, x0, y0, x1, y1):
        dx, dy, x, y = abs(x1-x0), abs(y1-y0), x0, y0
        sx, sy, err = (1 if x0 < x1 else -1), (1 if y0 < y1 else -1), abs(x1-x0)-abs(y1-y0)
        while True:
            if (x, y) != (x0, y0) and not self.tiles[x][y].transparent: return (x, y) == (x1, y1)
            if (x, y) == (x1, y1): return True
            e2 = 2*err
            if e2 > -dy: err -= dy; x += sx
            if e2 < dx: err += dx; y += sy

    def fov(self, origin, radius, reveal=True):
        out, ox, oy = set(), *origin
        for x in range(ox-radius, ox+radius+1):
            for y in range(oy-radius, oy+radius+1):
                if self.inside(x, y) and dist(origin, (x, y)) <= radius and self.los(ox, oy, x, y):
                    out.add((x, y))
                    if reveal: self.fog[x][y] = False
        return out


class Inventory:
    def __init__(self): self.items, self.equipment = defaultdict(int), {}
    def add(self, name, n=1): self.items[name] += max(0, n)

    def find(self, q):
        q = norm_name(q); return next((n for n in self.items if norm_name(n) == q), None)

    def remove(self, name, n=1):
        name = self.find(name) or name
        if self.items.get(name, 0) < n: return False
        self.items[name] -= n
        if self.items[name] <= 0: self.items.pop(name, None)
        return True

    def equip(self, name):
        real = self.find(name)
        if not real or ITEMS.get(real, {}).get("kind") != "equipment": return False, "You do not own that equipment."
        slot = ITEMS[real]["slot"]
        if not self.remove(real): return False, "Could not equip it."
        if slot in self.equipment: self.add(self.equipment[slot])
        self.equipment[slot] = real
        return True, f"Equipped {real}."

    def atk(self): return sum(ITEMS.get(n, {}).get("atk", 0) for n in self.equipment.values())
    def defense(self): return sum(ITEMS.get(n, {}).get("def", 0) for n in self.equipment.values())
    def dump(self): return {"items": dict(self.items), "equipment": self.equipment}

    @classmethod
    def load(cls, d):
        i = cls(); i.items = defaultdict(int, {k:int(v) for k,v in d.get("items",{}).items()}); i.equipment = dict(d.get("equipment",{})); return i


class Stats:
    def __init__(self, hp, atk, defense, level=1, xp=0): self.max_hp, self.hp, self.atk, self.defense, self.level, self.xp = hp, hp, atk, defense, level, xp
    def dump(self): return vars(self).copy()
    @classmethod
    def load(cls, d):
        s = cls(d["max_hp"], d["atk"], d["defense"], d.get("level",1), d.get("xp",0)); s.hp = d["hp"]; return s

    def gain_xp(self, n):
        self.xp += n; levels = []
        while self.xp >= 100*self.level:
            self.xp -= 100*self.level; self.level += 1; self.max_hp += 5; self.hp = self.max_hp; self.atk += 1; self.defense += 1; levels.append(self.level)
        return levels


class Entity:
    def __init__(self, name, x, y, char, stats): self.name, self.x, self.y, self.char, self.stats, self.alive = name, x, y, char, stats, True
    def atk(self): return self.stats.atk
    def defense(self): return self.stats.defense

    def hit(self, amount):
        dmg = max(0, amount-self.defense()); self.stats.hp -= dmg
        if self.stats.hp <= 0: self.stats.hp, self.alive = 0, False
        return dmg


class Player(Entity):
    def __init__(self, name, x, y):
        super().__init__(name, x, y, "@", Stats(30,5,1)); self.inv = Inventory(); self.gold = 50; self.messages = deque(maxlen=10)
        self.explored, self.kills = set(), defaultdict(int); self.quests = {"First Steps":False, "Bandit Trouble":False}
    def atk(self): return self.stats.atk + self.inv.atk()
    def defense(self): return self.stats.defense + self.inv.defense()
    def msg(self, s): self.messages.append(s); log(s)


class Monster(Entity):
    def __init__(self, name, x=0, y=0):
        defs = {
            "Goblin":("g",12,4,0,18,["Coin","Bread","Herb"]), "Bandit":("b",16,5,1,26,["Coin","Iron Ore","Dagger"]),
            "Wolf":("w",11,5,0,20,["Herb","Coin"]), "Skeleton":("s",15,5,1,24,["Coin","Iron Ore","Rusty Sword"]),
            "Slime":("o",10,3,0,14,["Water","Herb"]), "Cultist":("c",14,6,0,28,["Coin","Health Potion","Herb"]),
        }
        ch,hp,atk,de,xp,loot = defs[name]; super().__init__(name,x,y,ch,Stats(hp,atk,de)); self.xp_reward, self.loot = xp, loot

    def turn(self, world, player):
        if not self.alive or not player.alive: return
        if dist((self.x,self.y),(player.x,player.y)) <= 1:
            dmg = player.hit(self.atk()); player.msg(f"{self.name} hits you for {dmg}."); return
        if (player.x,player.y) not in world.fov((self.x,self.y), CONFIG["fov"], reveal=False):
            dx,dy = random.choice([(1,0),(-1,0),(0,1),(0,-1),(0,0)]); nx,ny=self.x+dx,self.y+dy
            if world.open(nx,ny,exclude=self): self.x,self.y=nx,ny
            return
        path = astar(world,(self.x,self.y),(player.x,player.y),self)
        if len(path)>1 and path[1] != (player.x,player.y):
            nx,ny=path[1]
            if world.open(nx,ny,exclude=self): self.x,self.y=nx,ny


def astar(world, start, goal, mover=None):
    q=[(0,start)]; came={}; g=defaultdict(lambda:10**9); g[start]=0; seen=set()
    while q:
        _,cur=heapq.heappop(q)
        if cur in seen: continue
        if cur==goal:
            path=[cur]
            while cur in came: cur=came[cur]; path.append(cur)
            return path[::-1]
        seen.add(cur)
        x,y=cur
        for dx,dy in ((1,0),(-1,0),(0,1),(0,-1)):
            n=(x+dx,y+dy)
            if not world.walkable(*n): continue
            block=world.entity_at(*n,exclude=mover)
            if block and n!=goal: continue
            ng=g[cur]+1
            if ng<g[n]: came[n]=cur; g[n]=ng; heapq.heappush(q,(ng+dist(n,goal),n))
    return []


class Merchant(Entity):
    def __init__(self,x=0,y=0): super().__init__("Merchant",x,y,"M",Stats(30,2,2))


def make_monster(name=None): return Monster(name or random.choice(["Goblin","Bandit","Wolf","Skeleton","Slime","Cultist"]))


def update_quests(p,w):
    for i,r in enumerate(w.rooms):
        if r.contains(p.x,p.y):
            if i not in p.explored: p.explored.add(i); p.msg(f"Discovered room {len(p.explored)} ({w.tiles[p.x][p.y].biome}).")
            break
    if len(p.explored)>=3 and not p.quests["First Steps"]: p.quests["First Steps"]=True; p.gold+=20; p.inv.add("Bread"); p.msg("Quest complete: First Steps! +20 gold, +Bread.")
    if p.kills.get("Bandit",0)>=1 and not p.quests["Bandit Trouble"]: p.quests["Bandit Trouble"]=True; p.gold+=30; p.inv.add("Iron Sword"); p.msg("Quest complete: Bandit Trouble! +30 gold, +Iron Sword.")


def kill_monster(p,w,m):
    p.kills[m.name]+=1; levels=p.stats.gain_xp(m.xp_reward); drop=random.choice(m.loot) if m.loot and random.random()<.8 else None
    if drop: w.items[(m.x,m.y)].append(drop)
    if m in w.entities: w.entities.remove(m)
    p.msg(f"Defeated {m.name}. +{m.xp_reward} XP" + (f", dropped {drop}." if drop else "."))
    for level in levels: p.msg(f"Level up! You are now level {level}.")
    update_quests(p,w)


def player_attack(p,w,m):
    critical=random.random()<.05; raw=int(p.atk()*1.5) if critical else p.atk(); dmg=m.hit(raw)
    p.msg(f"You hit {m.name} for {dmg}." + (" CRITICAL!" if critical else ""))
    if not m.alive: kill_monster(p,w,m)


def init_game(seed=None):
    random.seed(CONFIG["seed"] if seed is None else seed); w=World(CONFIG["width"],CONFIG["height"]); w.generate(); px,py=w.rooms[0].center(); p=Player("Abdelfatah",px,py)
    p.inv.add("Rusty Sword"); p.inv.add("Bread"); p.inv.add("Water"); p.inv.equip("Rusty Sword"); w.place(p,(px,py))
    for i,r in enumerate(w.rooms[1:],1):
        if random.random()<.75:
            pos=w.random_open(r)
            if pos: w.place(make_monster(),pos)
    if len(w.rooms)>1:
        pos=w.random_open(w.rooms[1]);
        if pos: w.place(Merchant(),pos)
    pool=["Coin","Bread","Water","Iron Ore","Wood","Herb","Leather Armor","Rusty Sword"]
    for _ in range(24):
        pos=w.random_open()
        if pos: w.items[pos].append(random.choice(pool))
    state={"turn":0,"events":set(),"discount":1.2}; update_quests(p,w); p.msg("Welcome to Arcadia. Type help for controls."); return p,w,state


def entity_dump(e):
    d={"type":"monster" if isinstance(e,Monster) else "merchant","name":e.name,"x":e.x,"y":e.y,"stats":e.stats.dump(),"alive":e.alive}
    if isinstance(e,Monster): d.update({"xp":e.xp_reward,"loot":e.loot,"char":e.char})
    return d


def save_game(p,w,state):
    data={"version":2,"player":{"name":p.name,"x":p.x,"y":p.y,"stats":p.stats.dump(),"inv":p.inv.dump(),"gold":p.gold,"messages":list(p.messages),"explored":list(p.explored),"kills":dict(p.kills),"quests":p.quests,"alive":p.alive},
          "world":{"w":w.w,"h":w.h,"tiles":[[w.tiles[x][y].dump() for y in range(w.h)] for x in range(w.w)],"rooms":[r.dump() for r in w.rooms],"fog":w.fog,"items":{f"{x},{y}":v for (x,y),v in w.items.items() if v},"entities":[entity_dump(e) for e in w.entities if e is not p]},
          "state":{"turn":state["turn"],"events":list(state["events"]),"discount":state["discount"]}}
    try:
        (BASE/CONFIG["save"]).write_text(json.dumps(data,indent=2),encoding="utf-8"); p.msg("Game saved."); return True
    except (OSError,TypeError) as e: p.msg(f"Save failed: {e}"); return False


def load_game():
    try:
        d=json.loads((BASE/CONFIG["save"]).read_text(encoding="utf-8"))
        if d.get("version")!=2: raise ValueError("old save format")
        wd=d["world"]; w=World(wd["w"],wd["h"]); w.tiles=[[Tile.load(wd["tiles"][x][y]) for y in range(w.h)] for x in range(w.w)]; w.rooms=[Rect.load(r) for r in wd["rooms"]]; w.fog=wd["fog"]; w.items=defaultdict(list,{tuple(map(int,k.split(','))):list(v) for k,v in wd["items"].items()})
        for e in wd["entities"]:
            obj=Monster(e["name"]) if e["type"]=="monster" else Merchant(); obj.x,obj.y=e["x"],e["y"]; obj.stats=Stats.load(e["stats"]); obj.alive=e.get("alive",True)
            if isinstance(obj,Monster): obj.xp_reward=e.get("xp",obj.xp_reward); obj.loot=e.get("loot",obj.loot); obj.char=e.get("char",obj.char)
            if obj.alive and w.open(obj.x,obj.y): w.place(obj,(obj.x,obj.y))
        pd=d["player"]; p=Player(pd["name"],pd["x"],pd["y"]); p.stats=Stats.load(pd["stats"]); p.inv=Inventory.load(pd["inv"]); p.gold=pd["gold"]; p.messages=deque(pd.get("messages",[]),maxlen=10); p.explored=set(pd.get("explored",[])); p.kills=defaultdict(int,pd.get("kills",{})); p.quests=dict(pd.get("quests",p.quests)); p.alive=pd.get("alive",True)
        if not w.walkable(p.x,p.y): raise ValueError("invalid player position")
        block=w.entity_at(p.x,p.y)
        if block in w.entities: w.entities.remove(block)
        w.place(p,(p.x,p.y)); st=d["state"]; state={"turn":st["turn"],"events":set(st.get("events",[])),"discount":st.get("discount",1.2)}; p.msg("Game loaded."); return p,w,state
    except (OSError,ValueError,KeyError,TypeError,json.JSONDecodeError) as e: log(f"Load failed: {e}"); return None


def nearby_merchant(p,w): return next((e for e in w.entities if isinstance(e,Merchant) and e.alive and dist((e.x,e.y),(p.x,p.y))<=1.5),None)


def process_turn(p,w,state):
    state["turn"]+=1
    for e in list(w.entities):
        if isinstance(e,Monster) and e.alive and p.alive: e.turn(w,p)
    update_quests(p,w)
    if state["turn"]>=50 and "discount" not in state["events"]: state["events"].add("discount"); state["discount"]=.9; p.msg("The merchant announces a temporary discount!")
    if state["turn"]>=80 and "raid" not in state["events"]:
        state["events"].add("raid"); p.msg("A bandit raid sweeps the dungeon!")
        for _ in range(3):
            pos=w.random_open(random.choice(w.rooms));
            if pos: w.place(Monster("Bandit"),pos)


def draw(w,p,state):
    os.system("cls" if os.name=="nt" else "clear"); vis=w.fov((p.x,p.y),CONFIG["fov"]); ents={(e.x,e.y):e for e in w.entities if e is not p and e.alive and (e.x,e.y) in vis}
    print(f"Arcadia — HP {p.stats.hp}/{p.stats.max_hp} | ATK {p.atk()} | DEF {p.defense()} | Gold {p.gold} | Lvl {p.stats.level} XP {p.stats.xp}/{100*p.stats.level} | Turn {state['turn']}")
    for y in range(w.h):
        row=[]
        for x in range(w.w):
            pos=(x,y)
            if pos==(p.x,p.y): row.append("@")
            elif w.fog[x][y] and pos not in vis: row.append(" ")
            elif pos in ents: row.append(ents[pos].char)
            elif pos in vis and w.items.get(pos): row.append("!")
            else: row.append(w.tiles[x][y].char)
        print("".join(row))
    print(f"\nLocation: {w.tiles[p.x][p.y].biome} | Rooms explored: {len(p.explored)}/{len(w.rooms)}")
    print("\nMessages:"); [print(" -",m) for m in p.messages] if p.messages else print(" - The dungeon is quiet.")
    print("\nCommands: w/a/s/d | attack | g | i | e | u | t | q | c | p | save | load | wait | help | exit")


def inventory_menu(p):
    print("\nInventory:")
    for n,c in sorted(p.inv.items.items()): print(f" - {n} x{c}")
    print("Equipment:")
    for s,n in p.inv.equipment.items(): print(f" - {s}: {n}")
    input("\nEnter...")


def shop_menu(p,state):
    stock=["Bread","Water","Health Potion","Iron Sword","Chainmail","Lockpick","Iron Ore","Wood","Herb"]
    while True:
        print(f"\nArcadian Bazaar — Gold {p.gold}")
        for n in stock: print(f" - {n}: {max(1,int(ITEMS[n]['value']*state['discount']))} gold")
        line=input("buy <item> | sell <item> | back\n> ").strip()
        if norm_name(line)=="back": return
        if line.lower().startswith("buy "):
            q=line[4:].strip(); name=next((n for n in stock if norm_name(n)==norm_name(q)),None)
            if not name: p.msg("Item not found."); continue
            price=max(1,int(ITEMS[name]["value"]*state["discount"]))
            if p.gold<price: p.msg("Not enough gold.")
            else: p.gold-=price; p.inv.add(name); p.msg(f"Bought {name} for {price} gold.")
        elif line.lower().startswith("sell "):
            name=p.inv.find(line[5:].strip())
            if not name: p.msg("You do not own that item.")
            else: price=max(1,ITEMS.get(name,{"value":2})["value"]//2); p.inv.remove(name); p.gold+=price; p.msg(f"Sold {name} for {price} gold.")


def command(cmd,p,w,state):
    c=norm_name(cmd)
    if c in "wasd" and len(c)==1:
        dx,dy={"w":(0,-1),"s":(0,1),"a":(-1,0),"d":(1,0)}[c]; nx,ny=p.x+dx,p.y+dy
        if not w.walkable(nx,ny): p.msg("A wall blocks the way."); return "turn"
        block=w.entity_at(nx,ny,exclude=p)
        if isinstance(block,Monster): player_attack(p,w,block); return "turn"
        if block: p.msg(f"{block.name} is in the way. Try t to talk."); return "free"
        p.x,p.y=nx,ny; update_quests(p,w)
        if w.items.get((p.x,p.y)): p.msg("You see: "+", ".join(w.items[(p.x,p.y)])+". Press g.")
        return "turn"
    if c=="attack":
        m=next((e for e in w.entities if isinstance(e,Monster) and e.alive and dist((e.x,e.y),(p.x,p.y))<=1),None)
        if m: player_attack(p,w,m)
        else: p.msg("No adjacent enemy.")
        return "turn"
    if c=="g":
        stack=w.items.get((p.x,p.y),[])
        if not stack: p.msg("Nothing to pick up."); return "free"
        n=stack.pop(0)
        if not stack: w.items.pop((p.x,p.y),None)
        if n=="Coin": p.gold+=1; p.msg("Picked up 1 gold.")
        else: p.inv.add(n); p.msg(f"Picked up {n}.")
        return "turn"
    if c=="i": inventory_menu(p); return "free"
    if c=="e":
        choices=[n for n in p.inv.items if ITEMS.get(n,{}).get("kind")=="equipment"]
        if not choices: p.msg("You have no equipment to equip."); return "free"
        print("\nEquipment:"); [print(f" {i}. {n}") for i,n in enumerate(choices,1)]; raw=input("> ").strip(); name=choices[int(raw)-1] if raw.isdigit() and 1<=int(raw)<=len(choices) else p.inv.find(raw)
        ok,msg=p.inv.equip(name or ""); p.msg(msg); return "turn" if ok else "free"
    if c=="u":
        choices=[n for n in p.inv.items if ITEMS.get(n,{}).get("kind")=="consumable"]
        if not choices: p.msg("You have no consumables."); return "free"
        print("\nConsumables:"); [print(f" {i}. {n}") for i,n in enumerate(choices,1)]; raw=input("> ").strip(); name=choices[int(raw)-1] if raw.isdigit() and 1<=int(raw)<=len(choices) else p.inv.find(raw)
        if not name or ITEMS[name]["kind"]!="consumable": p.msg("Invalid consumable."); return "free"
        if p.stats.hp>=p.stats.max_hp: p.msg("You are already at full health."); return "free"
        p.inv.remove(name); before=p.stats.hp; p.stats.hp=min(p.stats.max_hp,p.stats.hp+ITEMS[name]["heal"]); p.msg(f"Used {name}. Restored {p.stats.hp-before} HP."); return "turn"
    if c=="t":
        if nearby_merchant(p,w): print("\nMerchant: Welcome, traveler. Need supplies?"); shop_menu(p,state)
        else: p.msg("Nobody is close enough to talk to.")
        return "free"
    if c=="p":
        if nearby_merchant(p,w): shop_menu(p,state)
        else: p.msg("Stand next to the merchant first.")
        return "free"
    if c=="q":
        print(f"\nFirst Steps: {'Completed' if p.quests['First Steps'] else f'{len(p.explored)}/3 rooms'}")
        print(f"Bandit Trouble: {'Completed' if p.quests['Bandit Trouble'] else f'{p.kills.get('Bandit',0)}/1 Bandit'}"); input("\nEnter..."); return "free"
    if c=="c":
        names=list(RECIPES); print("\nCrafting:"); [print(f" {i}. {n} <- {RECIPES[n]['needs']}") for i,n in enumerate(names,1)]; raw=input("> ").strip()
        if not raw.isdigit() or not 1<=int(raw)<=len(names): p.msg("Crafting cancelled."); return "free"
        name=names[int(raw)-1]; needs=RECIPES[name]["needs"]
        if not all(p.inv.items.get(n,0)>=k for n,k in needs.items()): p.msg("Missing ingredients."); return "free"
        for n,k in needs.items(): p.inv.remove(n,k)
        p.inv.add(name); p.msg(f"Crafted {name}."); return "turn"
    if c=="save": save_game(p,w,state); return "free"
    if c=="load": return "load"
    if c=="wait": p.msg("You wait."); return "turn"
    if c=="help":
        print("\nMove: w/a/s/d. Walk into monsters or use attack. g picks loot; i inventory; e equip; u use; t talk; q quests; c craft; p shop; save/load; wait; exit.\nSymbols: @ you, ! loot, M merchant, lowercase letters monsters, # walls."); input("\nEnter..."); return "free"
    if c=="exit": return "exit"
    if c: p.msg("Unknown command. Type help.")
    return "free"


def main():
    p,w,state=init_game()
    while True:
        draw(w,p,state)
        if not p.alive:
            c=norm_name(input("\nYOU DIED — load | restart | exit\n> "))
            if c=="load":
                loaded=load_game()
                if loaded: p,w,state=loaded
            elif c=="restart": p,w,state=init_game()
            elif c=="exit": break
            continue
        try: result=command(input("> "),p,w,state)
        except EOFError: break
        if result=="exit": break
        if result=="load":
            loaded=load_game()
            if loaded: p,w,state=loaded
            else: p.msg("Load failed or no compatible save exists.")
        elif result=="turn": process_turn(p,w,state)
    print("Goodbye.")


if __name__ == "__main__":
    try: main()
    except KeyboardInterrupt: print("\nGoodbye.")
