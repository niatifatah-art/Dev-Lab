#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# Title: Arcadia — A Text Roguelike Engine (Single-file Edition)
# Description:
#   A feature-rich, modular, and extensible text-based roguelike engine.
#   Systems included:
#     - World map generation (biomes, rooms, corridors)
#     - Entities (Player, NPCs, Monsters) with stats, leveling, and AI
#     - Inventory, equipment, crafting, shops, and economy
#     - Combat (melee, ranged, crits, status effects, resistances)
#     - Pathfinding (A*), field-of-view (FOV), and fog-of-war
#     - Quests, dialogue trees, events, and factions
#     - Save/Load (JSON), logging, and configuration
#     - Procedural loot tables and rarity tiers
#     - Turn scheduler and time system
#     - Simple UI loop with commands
#
# Note:
#   This is a single-file version intended for demonstration. In a real project,
#   split into modules. You can expand content (biomes, items, quests) easily.

import sys
import os
import json
import math
import random
import time
from collections import deque, defaultdict, namedtuple
from typing import List, Dict, Tuple, Optional, Set

# -----------------------------
# Configuration and Constants
# -----------------------------

CONFIG = {
    "world_width": 60,
    "world_height": 30,
    "max_rooms": 18,
    "room_min_size": 4,
    "room_max_size": 10,
    "seed": None,  # set to int for reproducibility
    "fog_of_war": True,
    "fov_radius": 8,
    "starting_gold": 50,
    "starting_items": ["Rusty Sword", "Bread", "Water"],
    "starting_skills": ["Survival", "Swordsmanship"],
    "difficulty": "Normal",
    "crit_chance_base": 0.05,
    "crit_multiplier": 1.5,
    "status_effects_enabled": True,
    "save_file": "arcadia_save.json",
    "log_file": "arcadia_log.txt",
    "turn_delay": 0.0,  # set >0 for slow mode
}

RARITY_TIERS = ["Common", "Uncommon", "Rare", "Epic", "Legendary"]

BIOMES = ["Meadow", "Forest", "Desert", "Tundra", "Swamp", "Highlands", "Ruins"]

FACTIONS = {
    "Arcadian Guard": {"alignment": "Lawful", "relations": {"Bandits": -50, "Merchants": +20}},
    "Bandits": {"alignment": "Chaotic", "relations": {"Arcadian Guard": -50, "Merchants": -20}},
    "Merchants": {"alignment": "Neutral", "relations": {"Arcadian Guard": +20, "Bandits": -20}},
    "Wanderers": {"alignment": "Neutral", "relations": {}},
}

DAMAGE_TYPES = ["Physical", "Fire", "Ice", "Poison", "Arcane"]

STATUS_EFFECTS = {
    "Bleed": {"duration": (2, 4), "tick_damage": (2, 5), "type": "Physical"},
    "Burn": {"duration": (2, 4), "tick_damage": (3, 6), "type": "Fire"},
    "Freeze": {"duration": (1, 2), "speed_penalty": 0.5, "type": "Ice"},
    "Poison": {"duration": (3, 6), "tick_damage": (2, 4), "type": "Poison"},
    "Weakness": {"duration": (2, 4), "attack_penalty": 2, "type": "Arcane"},
}

# -----------------------------
# Utility and Logging
# -----------------------------

def log(message: str):
    ts = time.strftime("%Y-%m-%d %H:%M:%S")
    line = f"[{ts}] {message}"
    print(line)
    try:
        with open(CONFIG["log_file"], "a", encoding="utf-8") as f:
            f.write(line + "\n")
    except Exception:
        pass

def clamp(val, lo, hi):
    return max(lo, min(hi, val))

def roll(chance: float) -> bool:
    return random.random() < chance

def weighted_choice(choices: List[Tuple[str, float]]) -> str:
    total = sum(w for _, w in choices)
    r = random.uniform(0, total)
    upto = 0
    for item, weight in choices:
        if upto + weight >= r:
            return item
        upto += weight
    return choices[-1][0]

def distance(a: Tuple[int, int], b: Tuple[int, int]) -> float:
    return math.hypot(a[0] - b[0], a[1] - b[1])

# -----------------------------
# Map and Tiles
# -----------------------------

class Tile:
    def __init__(self, walkable: bool, transparent: bool, char: str, biome: str = "Meadow"):
        self.walkable = walkable
        self.transparent = transparent
        self.char = char
        self.biome = biome
        self.explored = False

class Rect:
    def __init__(self, x, y, w, h):
        self.x1 = x
        self.y1 = y
        self.x2 = x + w
        self.y2 = y + h

    def center(self):
        return ((self.x1 + self.x2) // 2, (self.y1 + self.y2) // 2)

    def intersect(self, other) -> bool:
        return (self.x1 <= other.x2 and self.x2 >= other.x1 and
                self.y1 <= other.y2 and self.y2 >= other.y1)

class World:
    def __init__(self, width: int, height: int):
        self.width = width
        self.height = height
        self.tiles = [[Tile(False, False, "#") for _ in range(height)] for _ in range(width)]
        self.rooms: List[Rect] = []
        self.biome_map: Dict[Tuple[int, int], str] = {}
        self.entities: List["Entity"] = []
        self.items_on_ground: Dict[Tuple[int, int], List["Item"]] = defaultdict(list)
        self.fog = [[True for _ in range(height)] for _ in range(width)] if CONFIG["fog_of_war"] else None

    def in_bounds(self, x, y) -> bool:
        return 0 <= x < self.width and 0 <= y < self.height

    def is_walkable(self, x, y) -> bool:
        return self.in_bounds(x, y) and self.tiles[x][y].walkable

    def carve_room(self, room: Rect, biome: str):
        for x in range(room.x1, room.x2):
            for y in range(room.y1, room.y2):
                self.tiles[x][y] = Tile(True, True, ".", biome)
                self.biome_map[(x, y)] = biome

    def carve_h_tunnel(self, x1, x2, y, biome: str):
        for x in range(min(x1, x2), max(x1, x2) + 1):
            self.tiles[x][y] = Tile(True, True, ".", biome)
            self.biome_map[(x, y)] = biome

    def carve_v_tunnel(self, y1, y2, x, biome: str):
        for y in range(min(y1, y2), max(y1, y2) + 1):
            self.tiles[x][y] = Tile(True, True, ".", biome)
            self.biome_map[(x, y)] = biome

    def generate(self):
        log("Generating world...")
        rooms = []
        for _ in range(CONFIG["max_rooms"]):
            w = random.randint(CONFIG["room_min_size"], CONFIG["room_max_size"])
            h = random.randint(CONFIG["room_min_size"], CONFIG["room_max_size"])
            x = random.randint(1, self.width - w - 2)
            y = random.randint(1, self.height - h - 2)
            new_room = Rect(x, y, w, h)
            if any(new_room.intersect(other) for other in rooms):
                continue
            biome = random.choice(BIOMES)
            self.carve_room(new_room, biome)
            if rooms:
                (prev_x, prev_y) = rooms[-1].center()
                (new_x, new_y) = new_room.center()
                if random.random() < 0.5:
                    self.carve_h_tunnel(prev_x, new_x, prev_y, biome)
                    self.carve_v_tunnel(prev_y, new_y, new_x, biome)
                else:
                    self.carve_v_tunnel(prev_y, new_y, prev_x, biome)
                    self.carve_h_tunnel(prev_x, new_x, new_y, biome)
            rooms.append(new_room)
        self.rooms = rooms
        log(f"Generated {len(rooms)} rooms.")

    def place_entity(self, entity: "Entity", pos: Tuple[int, int]):
        entity.x, entity.y = pos
        self.entities.append(entity)

    def remove_entity(self, entity: "Entity"):
        if entity in self.entities:
            self.entities.remove(entity)

    def get_entities_at(self, x, y) -> List["Entity"]:
        return [e for e in self.entities if e.x == x and e.y == y]

    def add_item(self, item: "Item", pos: Tuple[int, int]):
        self.items_on_ground[pos].append(item)

    def remove_item(self, item: "Item", pos: Tuple[int, int]):
        if item in self.items_on_ground.get(pos, []):
            self.items_on_ground[pos].remove(item)

    def compute_fov(self, origin: Tuple[int, int], radius: int) -> Set[Tuple[int, int]]:
        visible = set()
        ox, oy = origin
        for x in range(ox - radius, ox + radius + 1):
            for y in range(oy - radius, oy + radius + 1):
                if not self.in_bounds(x, y):
                    continue
                if distance((ox, oy), (x, y)) <= radius:
                    if self._los(ox, oy, x, y):
                        visible.add((x, y))
                        if self.fog:
                            self.fog[x][y] = False
        return visible

    def _los(self, x0, y0, x1, y1) -> bool:
        # Bresenham's line algorithm for line-of-sight
        dx = abs(x1 - x0)
        dy = abs(y1 - y0)
        x, y = x0, y0
        sx = 1 if x0 < x1 else -1
        sy = 1 if y0 < y1 else -1
        err = dx - dy
        while True:
            if not self.tiles[x][y].transparent:
                return x == x1 and y == y1
            if x == x1 and y == y1:
                return True
            e2 = 2 * err
            if e2 > -dy:
                err -= dy
                x += sx
            if e2 < dx:
                err += dx
                y += sy

# -----------------------------
# Items, Equipment, and Crafting
# -----------------------------

class Item:
    def __init__(self, name: str, rarity: str = "Common", value: int = 1, stackable: bool = True):
        self.name = name
        self.rarity = rarity
        self.value = value
        self.stackable = stackable

    def __repr__(self):
        return f"{self.name}({self.rarity})"

class Equipment(Item):
    def __init__(self, name: str, slot: str, attack: int = 0, defense: int = 0,
                 damage_type: str = "Physical", rarity: str = "Common", value: int = 1):
        super().__init__(name, rarity, value, stackable=False)
        self.slot = slot
        self.attack = attack
        self.defense = defense
        self.damage_type = damage_type

class Consumable(Item):
    def __init__(self, name: str, heal: int = 0, status_apply: Optional[str] = None,
                 rarity: str = "Common", value: int = 1):
        super().__init__(name, rarity, value, stackable=True)
        self.heal = heal
        self.status_apply = status_apply

class CraftingRecipe:
    def __init__(self, name: str, inputs: Dict[str, int], output: Item):
        self.name = name
        self.inputs = inputs
        self.output = output

class LootTable:
    def __init__(self, entries: List[Tuple[Item, float]]):
        self.entries = entries

    def roll(self) -> Optional[Item]:
        if not self.entries:
            return None
        total = sum(w for _, w in self.entries)
        r = random.uniform(0, total)
        upto = 0
        for item, weight in self.entries:
            if upto + weight >= r:
                return item
            upto += weight
        return self.entries[-1][0]

# -----------------------------
# Stats, Effects, and Entities
# -----------------------------

class Stats:
    def __init__(self, hp: int, attack: int, defense: int, speed: float = 1.0, level: int = 1, xp: int = 0):
        self.max_hp = hp
        self.hp = hp
        self.attack = attack
        self.defense = defense
        self.speed = speed
        self.level = level
        self.xp = xp
        self.resistances: Dict[str, float] = {dt: 0.0 for dt in DAMAGE_TYPES}

    def gain_xp(self, amount: int):
        self.xp += amount
        threshold = 100 * self.level
        if self.xp >= threshold:
            self.level += 1
            self.xp -= threshold
            self.max_hp += 5
            self.hp = self.max_hp
            self.attack += 1
            self.defense += 1
            log(f"Level up! Now level {self.level}.")

class StatusInstance:
    def __init__(self, name: str, duration: int, data: Dict):
        self.name = name
        self.duration = duration
        self.data = data

    def tick(self, entity: "Entity"):
        self.duration -= 1
        if self.name in ("Bleed", "Burn", "Poison"):
            dmg = random.randint(*STATUS_EFFECTS[self.name]["tick_damage"])
            entity.take_damage(dmg, STATUS_EFFECTS[self.name]["type"], source=f"{self.name} tick")
        # Freeze and Weakness handled in entity modifiers
        return self.duration <= 0

class Inventory:
    def __init__(self):
        self.items: Dict[str, int] = defaultdict(int)
        self.equipment: Dict[str, Equipment] = {}  # slot -> equipment

    def add(self, item: Item, count: int = 1):
        if item.stackable:
            self.items[item.name] += count
        else:
            self.items[item.name] += 1

    def remove(self, name: str, count: int = 1) -> bool:
        if self.items.get(name, 0) >= count:
            self.items[name] -= count
            if self.items[name] <= 0:
                del self.items[name]
            return True
        return False

    def equip(self, equipment: Equipment) -> bool:
        slot = equipment.slot
        if slot in self.equipment:
            log(f"Unequipped {self.equipment[slot].name} from {slot}.")
        self.equipment[slot] = equipment
        log(f"Equipped {equipment.name} on {slot}.")
        return True

    def total_attack_bonus(self) -> int:
        return sum(eq.attack for eq in self.equipment.values())

    def total_defense_bonus(self) -> int:
        return sum(eq.defense for eq in self.equipment.values())

class Entity:
    def __init__(self, name: str, x: int, y: int, char: str, faction: str, stats: Stats):
        self.name = name
        self.x = x
        self.y = y
        self.char = char
        self.faction = faction
        self.stats = stats
        self.inventory = Inventory()
        self.statuses: List[StatusInstance] = []
        self.alive = True
        self.ai: Optional["AIBase"] = None
        self.vision_radius = CONFIG["fov_radius"]

    def move(self, dx: int, dy: int, world: World):
        nx, ny = self.x + dx, self.y + dy
        if world.is_walkable(nx, ny):
            self.x, self.y = nx, ny

    def take_damage(self, amount: int, damage_type: str = "Physical", source: str = "Unknown"):
        resist = self.stats.resistances.get(damage_type, 0.0)
        mitigated = int(amount * (1.0 - resist))
        defense = self.stats.defense + self.inventory.total_defense_bonus()
        mitigated = clamp(mitigated - defense, 0, 9999)
        self.stats.hp -= mitigated
        log(f"{self.name} takes {mitigated} {damage_type} damage from {source}. HP: {self.stats.hp}/{self.stats.max_hp}")
        if self.stats.hp <= 0:
            self.die()

    def die(self):
        self.alive = False
        log(f"{self.name} has died.")

    def apply_status(self, name: str):
        if name not in STATUS_EFFECTS:
            return
        dur = random.randint(*STATUS_EFFECTS[name]["duration"])
        self.statuses.append(StatusInstance(name, dur, STATUS_EFFECTS[name]))
        log(f"{self.name} is affected by {name} for {dur} turns.")

    def tick_statuses(self):
        remaining = []
        for st in self.statuses:
            expired = st.tick(self)
            if not expired:
                remaining.append(st)
            else:
                log(f"{self.name}'s {st.name} has worn off.")
        self.statuses = remaining

    def attack_target(self, target: "Entity", damage_type: str = "Physical"):
        base_attack = self.stats.attack + self.inventory.total_attack_bonus()
        crit = roll(CONFIG["crit_chance_base"])
        dmg = base_attack
        if crit:
            dmg = int(dmg * CONFIG["crit_multiplier"])
            log(f"Critical hit by {self.name}!")
        target.take_damage(dmg, damage_type, source=f"{self.name}'s attack")

class Player(Entity):
    def __init__(self, name: str, x: int, y: int):
        super().__init__(name, x, y, "@", "Wanderers", Stats(hp=30, attack=5, defense=1))
        self.gold = CONFIG["starting_gold"]
        for it in CONFIG["starting_items"]:
            self.inventory.add(Item(it))
        self.skills = set(CONFIG["starting_skills"])
        self.quest_log: List["Quest"] = []
        self.messages: deque[str] = deque(maxlen=10)

    def message(self, text: str):
        self.messages.append(text)
        log(f"[MSG] {text}")

class Monster(Entity):
    def __init__(self, name: str, x: int, y: int, char: str, faction: str, stats: Stats, loot: LootTable):
        super().__init__(name, x, y, char, faction, stats)
        self.loot = loot

    def drop_loot(self, world: World):
        item = self.loot.roll()
        if item:
            world.add_item(item, (self.x, self.y))
            log(f"{self.name} dropped {item}.")

# -----------------------------
# AI and Pathfinding
# -----------------------------

class AIBase:
    def __init__(self, owner: Entity):
        self.owner = owner

    def take_turn(self, world: World, player: Player):
        pass

class AggressiveAI(AIBase):
    def take_turn(self, world: World, player: Player):
        if not self.owner.alive:
            return
        # If player in FOV, chase; else wander
        visible = world.compute_fov((self.owner.x, self.owner.y), self.owner.vision_radius)
        if (player.x, player.y) in visible:
            path = a_star(world, (self.owner.x, self.owner.y), (player.x, player.y))
            if path and len(path) > 1:
                nx, ny = path[1]
                self.owner.move(nx - self.owner.x, ny - self.owner.y, world)
            else:
                # Adjacent? Attack
                if distance((self.owner.x, self.owner.y), (player.x, player.y)) <= 1.5:
                    self.owner.attack_target(player)
        else:
            # Wander randomly
            dx, dy = random.choice([(1,0),(-1,0),(0,1),(0,-1),(0,0)])
            self.owner.move(dx, dy, world)

class DefensiveAI(AIBase):
    def take_turn(self, world: World, player: Player):
        if not self.owner.alive:
            return
        # Avoid player if low HP, otherwise patrol
        if self.owner.stats.hp < self.owner.stats.max_hp * 0.4:
            # Flee
            dx = -1 if player.x > self.owner.x else 1
            dy = -1 if player.y > self.owner.y else 1
            self.owner.move(dx, dy, world)
        else:
            # Patrol
            dx, dy = random.choice([(1,0),(-1,0),(0,1),(0,-1),(0,0)])
            self.owner.move(dx, dy, world)

def a_star(world: World, start: Tuple[int, int], goal: Tuple[int, int]) -> List[Tuple[int, int]]:
    open_set: Set[Tuple[int, int]] = set([start])
    came_from: Dict[Tuple[int, int], Tuple[int, int]] = {}
    g_score = defaultdict(lambda: float("inf"))
    f_score = defaultdict(lambda: float("inf"))
    g_score[start] = 0
    f_score[start] = distance(start, goal)
    while open_set:
        current = min(open_set, key=lambda p: f_score[p])
        if current == goal:
            return reconstruct_path(came_from, current)
        open_set.remove(current)
        for nx, ny in neighbors(world, current):
            tentative_g = g_score[current] + 1
            if tentative_g < g_score[(nx, ny)]:
                came_from[(nx, ny)] = current
                g_score[(nx, ny)] = tentative_g
                f_score[(nx, ny)] = tentative_g + distance((nx, ny), goal)
                if (nx, ny) not in open_set:
                    open_set.add((nx, ny))
    return []

def neighbors(world: World, pos: Tuple[int, int]) -> List[Tuple[int, int]]:
    x, y = pos
    result = []
    for dx, dy in [(1,0),(-1,0),(0,1),(0,-1)]:
        nx, ny = x + dx, y + dy
        if world.is_walkable(nx, ny):
            result.append((nx, ny))
    return result

def reconstruct_path(came_from: Dict[Tuple[int, int], Tuple[int, int]], current: Tuple[int, int]) -> List[Tuple[int, int]]:
    path = [current]
    while current in came_from:
        current = came_from[current]
        path.append(current)
    path.reverse()
    return path

# -----------------------------
# Dialogue, Quests, and Events
# -----------------------------

class DialogueNode:
    def __init__(self, text: str, options: Dict[str, Optional["DialogueNode"]]):
        self.text = text
        self.options = options  # option_text -> next_node

class Quest:
    def __init__(self, title: str, description: str, objectives: List[str], reward_gold: int = 0, reward_items: Optional[List[Item]] = None):
        self.title = title
        self.description = description
        self.objectives = objectives
        self.completed = False
        self.reward_gold = reward_gold
        self.reward_items = reward_items or []

    def complete(self, player: Player):
        if not self.completed:
            self.completed = True
            player.gold += self.reward_gold
            for it in self.reward_items:
                player.inventory.add(it)
            player.message(f"Quest completed: {self.title}! Rewards: {self.reward_gold} gold, items: {[it.name for it in self.reward_items]}")

class Event:
    def __init__(self, name: str, trigger_turn: int, action):
        self.name = name
        self.trigger_turn = trigger_turn
        self.action = action
        self.triggered = False

    def try_trigger(self, current_turn: int):
        if not self.triggered and current_turn >= self.trigger_turn:
            self.action()
            self.triggered = True
            log(f"Event triggered: {self.name}")

# -----------------------------
# Economy and Shops
# -----------------------------

class Shop:
    def __init__(self, name: str, inventory: List[Item], price_multiplier: float = 1.0):
        self.name = name
        self.inventory = inventory
        self.price_multiplier = price_multiplier

    def list_items(self):
        return [(it.name, int(it.value * self.price_multiplier), it.rarity) for it in self.inventory]

    def buy(self, player: Player, item_name: str):
        for it in self.inventory:
            if it.name == item_name:
                price = int(it.value * self.price_multiplier)
                if player.gold >= price:
                    player.gold -= price
                    player.inventory.add(it)
                    player.message(f"Bought {it.name} for {price} gold.")
                    return True
                else:
                    player.message("Not enough gold.")
                    return False
        player.message("Item not found.")
        return False

    def sell(self, player: Player, item_name: str):
        # Simple sell: half value
        # If player has item, remove and give gold
        if player.inventory.items.get(item_name, 0) > 0:
            # Find item template in shop inventory to get base value
            template = next((it for it in self.inventory if it.name == item_name), None)
            base_value = template.value if template else 5
            price = int(base_value * 0.5)
            player.inventory.remove(item_name, 1)
            player.gold += price
            player.message(f"Sold {item_name} for {price} gold.")
            return True
        player.message("You don't have that item.")
        return False

# -----------------------------
# Turn Scheduler and Time
# -----------------------------

class Scheduler:
    def __init__(self):
        self.turn = 0
        self.queue: deque[Entity] = deque()

    def add(self, entity: Entity):
        self.queue.append(entity)

    def next_turn(self) -> Optional[Entity]:
        if not self.queue:
            return None
        self.turn += 1
        ent = self.queue.popleft()
        self.queue.append(ent)
        return ent

# -----------------------------
# Save/Load
# -----------------------------

def save_game(player: Player, world: World, scheduler: Scheduler):
    data = {
        "player": {
            "name": player.name,
            "x": player.x,
            "y": player.y,
            "hp": player.stats.hp,
            "max_hp": player.stats.max_hp,
            "attack": player.stats.attack,
            "defense": player.stats.defense,
            "level": player.stats.level,
            "xp": player.stats.xp,
            "gold": player.gold,
            "inventory": dict(player.inventory.items),
            "equipment": {slot: eq.name for slot, eq in player.inventory.equipment.items()},
            "skills": list(player.skills),
        },
        "world": {
            "width": world.width,
            "height": world.height,
            "tiles": [[world.tiles[x][y].char for y in range(world.height)] for x in range(world.width)],
            "biomes": {f"{x},{y}": world.biome_map.get((x, y), "Meadow") for x in range(world.width) for y in range(world.height)},
            "items_on_ground": {f"{x},{y}": [it.name for it in items] for (x, y), items in world.items_on_ground.items()},
            "entities": [
                {
                    "name": e.name,
                    "x": e.x,
                    "y": e.y,
                    "char": e.char,
                    "faction": e.faction,
                    "hp": e.stats.hp,
                    "max_hp": e.stats.max_hp,
                    "attack": e.stats.attack,
                    "defense": e.stats.defense,
                    "level": e.stats.level,
                    "xp": e.stats.xp,
                    "alive": e.alive,
                }
                for e in world.entities if not isinstance(e, Player)
            ],
        },
        "scheduler": {"turn": scheduler.turn},
    }
    try:
        with open(CONFIG["save_file"], "w", encoding="utf-8") as f:
            json.dump(data, f, indent=2)
        log("Game saved.")
    except Exception as e:
        log(f"Save failed: {e}")

def load_game() -> Optional[Tuple[Player, World, Scheduler]]:
    try:
        with open(CONFIG["save_file"], "r", encoding="utf-8") as f:
            data = json.load(f)
        world = World(data["world"]["width"], data["world"]["height"])
        # Rebuild tiles
        for x in range(world.width):
            for y in range(world.height):
                ch = data["world"]["tiles"][x][y]
                walkable = ch in (".", ",")
                transparent = ch in (".", ",")
                biome = data["world"]["biomes"].get(f"{x},{y}", "Meadow")
                world.tiles[x][y] = Tile(walkable, transparent, ch, biome)
        # Items on ground
        for key, names in data["world"]["items_on_ground"].items():
            x, y = map(int, key.split(","))
            for nm in names:
                world.add_item(Item(nm), (x, y))
        # Entities
        for ed in data["world"]["entities"]:
            m = Monster(ed["name"], ed["x"], ed["y"], ed["char"], ed["faction"],
                        Stats(ed["max_hp"], ed["attack"], ed["defense"], level=ed["level"], xp=ed["xp"]),
                        LootTable([]))
            m.stats.hp = ed["hp"]
            m.alive = ed["alive"]
            m.ai = AggressiveAI(m)
            world.place_entity(m, (m.x, m.y))
        # Player
        pd = data["player"]
        player = Player(pd["name"], pd["x"], pd["y"])
        player.stats.hp = pd["hp"]
        player.stats.max_hp = pd["max_hp"]
        player.stats.attack = pd["attack"]
        player.stats.defense = pd["defense"]
        player.stats.level = pd["level"]
        player.stats.xp = pd["xp"]
        player.gold = pd["gold"]
        player.inventory.items = defaultdict(int, pd["inventory"])
        # Equipment reconstruction (simple)
        for slot, name in pd["equipment"].items():
            player.inventory.equipment[slot] = Equipment(name, slot, attack=2, defense=1)
        player.skills = set(pd["skills"])
        scheduler = Scheduler()
        scheduler.turn = data["scheduler"]["turn"]
        log("Game loaded.")
        return player, world, scheduler
    except Exception as e:
        log(f"Load failed: {e}")
        return None

# -----------------------------
# Content Generation
# -----------------------------

def generate_monster(world: World) -> Monster:
    names = ["Goblin", "Bandit", "Wolf", "Skeleton", "Slime", "Cultist"]
    name = random.choice(names)
    char = random.choice(["g", "b", "w", "s", "o", "c"])
    faction = random.choice(list(FACTIONS.keys()))
    hp = random.randint(10, 20)
    attack = random.randint(3, 6)
    defense = random.randint(0, 2)
    stats = Stats(hp=hp, attack=attack, defense=defense)
    loot_entries = [
        (Item("Coin", rarity="Common", value=1), 0.6),
        (Consumable("Bread", heal=5, rarity="Common", value=3), 0.3),
        (Equipment("Dagger", slot="Weapon", attack=2, defense=0, rarity="Uncommon", value=10), 0.1),
    ]
    loot = LootTable(loot_entries)
    m = Monster(name, 0, 0, char, faction, stats, loot)
    m.ai = AggressiveAI(m)
    return m

def populate_world(world: World, player: Player):
    for room in world.rooms:
        cx, cy = room.center()
        if random.random() < 0.7:
            m = generate_monster(world)
            world.place_entity(m, (cx, cy))
    # Place some items
    for _ in range(20):
        x = random.randint(1, world.width - 2)
        y = random.randint(1, world.height - 2)
        if world.is_walkable(x, y):
            it = random.choice([
                Item("Coin", value=1),
                Consumable("Bread", heal=5, value=3),
                Consumable("Water", heal=3, value=2),
                Equipment("Rusty Sword", slot="Weapon", attack=2, defense=0, value=8),
                Equipment("Leather Armor", slot="Armor", attack=0, defense=2, value=12),
            ])
            world.add_item(it, (x, y))

def generate_shop() -> Shop:
    inventory = [
        Consumable("Bread", heal=5, value=3),
        Consumable("Water", heal=3, value=2),
        Equipment("Iron Sword", slot="Weapon", attack=4, defense=0, rarity="Uncommon", value=20),
        Equipment("Chainmail", slot="Armor", attack=0, defense=4, rarity="Uncommon", value=25),
        Item("Lockpick", rarity="Uncommon", value=10),
    ]
    return Shop("Arcadian Bazaar", inventory, price_multiplier=1.2)

def generate_dialogue_tree() -> DialogueNode:
    end = DialogueNode("Safe travels.", {})
    trade = DialogueNode("Take a look at my wares.", {"Back": end})
    greet = DialogueNode("Welcome, traveler. What do you need?", {"Trade": trade, "Leave": end})
    return greet

def generate_quests() -> List[Quest]:
    return [
        Quest("First Steps", "Explore three rooms.", ["Explore 3 rooms"], reward_gold=20, reward_items=[Consumable("Bread", heal=5)]),
        Quest("Bandit Trouble", "Defeat a bandit.", ["Defeat 1 Bandit"], reward_gold=30, reward_items=[Equipment("Iron Sword", "Weapon", attack=4)]),
    ]

# -----------------------------
# Command Handling and UI
# -----------------------------

def draw(world: World, player: Player, visible: Set[Tuple[int, int]]):
    os.system("cls" if os.name == "nt" else "clear")
    print(f"Arcadia — HP {player.stats.hp}/{player.stats.max_hp} | ATK {player.stats.attack + player.inventory.total_attack_bonus()} | DEF {player.stats.defense + player.inventory.total_defense_bonus()} | Gold {player.gold} | Lvl {player.stats.level} XP {player.stats.xp}")
    for y in range(world.height):
        row = []
        for x in range(world.width):
            ent_here = world.get_entities_at(x, y)
            if (x, y) == (player.x, player.y):
                row.append("@")
            elif ent_here:
                row.append(ent_here[0].char)
            else:
                tile = world.tiles[x][y]
                if CONFIG["fog_of_war"]:
                    if world.fog[x][y] and (x, y) not in visible:
                        row.append(" ")
                    else:
                        row.append(tile.char)
                else:
                    row.append(tile.char)
        print("".join(row))
    print("\nMessages:")
    for msg in player.messages:
        print(f" - {msg}")
    print("\nCommands: w/a/s/d move | g get | i inventory | e equip | u use | t talk | q quests | c craft | p shop | save | load | attack | wait | help | exit")

def handle_input(cmd: str, player: Player, world: World, shop: Shop, dialogue: DialogueNode, scheduler: Scheduler):
    cmd = cmd.strip().lower()
    if cmd in ("w", "a", "s", "d"):
        dx, dy = {"w": (0,-1), "s": (0,1), "a": (-1,0), "d": (1,0)}[cmd]
        player.move(dx, dy, world)
        player.message(f"Moved to ({player.x},{player.y}).")
    elif cmd == "g":
        pos = (player.x, player.y)
        items = world.items_on_ground.get(pos, [])
        if items:
            it = items.pop(0)
            player.inventory.add(it)
            player.message(f"Picked up {it.name}.")
        else:
            player.message("Nothing to pick up.")
    elif cmd == "i":
        print("\nInventory:")
        for name, count in player.inventory.items.items():
            print(f" - {name} x{count}")
        print("Equipment:")
        for slot, eq in player.inventory.equipment.items():
            print(f" - {slot}: {eq.name} (ATK {eq.attack}, DEF {eq.defense})")
        input("\nPress Enter...")
    elif cmd == "e":
        print("\nEquip what? (exact name)")
        name = input("> ").strip()
        # Simple equipment creation if not template known
        eq = Equipment(name, slot="Weapon", attack=2, defense=0)
        player.inventory.equip(eq)
    elif cmd == "u":
        print("\nUse what? (exact name)")
        name = input("> ").strip()
        if player.inventory.items.get(name, 0) > 0:
            # Assume consumable heal
            heal = 5
            player.inventory.remove(name, 1)
            player.stats.hp = clamp(player.stats.hp + heal, 0, player.stats.max_hp)
            player.message(f"Used {name}. Healed {heal}.")
        else:
            player.message("You don't have that.")
    elif cmd == "attack":
        # Attack nearest enemy in adjacent tile
        targets = [e for e in world.entities if isinstance(e, Monster) and distance((e.x, e.y), (player.x, player.y)) <= 1.5 and e.alive]
        if targets:
            target = targets[0]
            player.attack_target(target)
            if not target.alive:
                target.drop_loot(world)
                player.stats.gain_xp(20)
        else:
            player.message("No adjacent enemy.")
    elif cmd == "t":
        # Talk: simple dialogue
        node = dialogue
        while True:
            print("\nNPC:", node.text)
            if not node.options:
                break
            for i, opt in enumerate(node.options.keys(), 1):
                print(f" {i}. {opt}")
            choice = input("> ").strip()
            try:
                idx = int(choice) - 1
                opt_text = list(node.options.keys())[idx]
                node = node.options[opt_text] or node
                if opt_text.lower() == "trade":
                    # Show shop
                    print("\nShop Inventory:")
                    for name, price, rarity in shop.list_items():
                        print(f" - {name} ({rarity}) — {price} gold")
                    print("Type 'buy <item>' or 'sell <item>' or 'back'")
                    while True:
                        line = input("> ").strip().lower()
                        if line == "back":
                            break
                        elif line.startswith("buy "):
                            item_name = line[4:].strip().title()
                            shop.buy(player, item_name)
                        elif line.startswith("sell "):
                            item_name = line[5:].strip().title()
                            shop.sell(player, item_name)
                        else:
                            print("Unknown trade command.")
            except Exception:
                break
    elif cmd == "q":
        print("\nQuests:")
        for q in player.quest_log:
            status = "Completed" if q.completed else "Active"
            print(f" - {q.title}: {status} — {q.description}")
        input("\nPress Enter...")
    elif cmd == "c":
        # Crafting demo
        recipes = [
            CraftingRecipe("Iron Sword", {"Iron Ore": 2, "Wood": 1}, Equipment("Iron Sword", "Weapon", attack=4, value=20)),
            CraftingRecipe("Health Potion", {"Herb": 2, "Water": 1}, Consumable("Health Potion", heal=10, value=15)),
        ]
        print("\nCrafting:")
        for i, r in enumerate(recipes, 1):
            print(f" {i}. {r.name} -> requires {r.inputs}")
        choice = input("> ").strip()
        try:
            idx = int(choice) - 1
            r = recipes[idx]
            ok = all(player.inventory.items.get(nm, 0) >= cnt for nm, cnt in r.inputs.items())
            if ok:
                for nm, cnt in r.inputs.items():
                    player.inventory.remove(nm, cnt)
                player.inventory.add(r.output)
                player.message(f"Crafted {r.output.name}.")
            else:
                player.message("Missing ingredients.")
        except Exception:
            player.message("Invalid crafting choice.")
    elif cmd == "p":
        # Quick shop access
        print("\nShop Inventory:")
        for name, price, rarity in shop.list_items():
            print(f" - {name} ({rarity}) — {price} gold")
        print("Type 'buy <item>' or 'sell <item>' or 'back'")
        while True:
            line = input("> ").strip().lower()
            if line == "back":
                break
            elif line.startswith("buy "):
                item_name = line[4:].strip().title()
                shop.buy(player, item_name)
            elif line.startswith("sell "):
                item_name = line[5:].strip().title()
                shop.sell(player, item_name)
            else:
                print("Unknown trade command.")
    elif cmd == "save":
        save_game(player, world, scheduler)
    elif cmd == "load":
        loaded = load_game()
        if loaded:
            lp, lw, ls = loaded
            player.name = lp.name
            player.x, player.y = lp.x, lp.y
            player.stats = lp.stats
            player.gold = lp.gold
            player.inventory = lp.inventory
            world.tiles = lw.tiles
            world.biome_map = lw.biome_map
            world.items_on_ground = lw.items_on_ground
            world.entities = lw.entities + [player]
            scheduler.turn = ls.turn
            player.message("Loaded game state.")
        else:
            player.message("Load failed.")
    elif cmd == "wait":
        player.message("You wait for a moment.")
    elif cmd == "help":
        print("\nHelp:")
        print(" - Move with w/a/s/d")
        print(" - g: pick up item on ground")
        print(" - i: view inventory and equipment")
        print(" - e: equip an item by name")
        print(" - u: use a consumable by name")
        print(" - attack: attack adjacent enemy")
        print(" - t: talk to NPC (dialogue and trade)")
        print(" - q: view quests")
        print(" - c: crafting")
        print(" - p: shop")
        print(" - save/load: save or load game")
        print(" - wait: skip a turn")
        print(" - exit: quit")
        input("\nPress Enter...")
    elif cmd == "exit":
        sys.exit(0)
    else:
        player.message("Unknown command.")

# -----------------------------
# Game Initialization
# -----------------------------

def init_game(seed: Optional[int] = None) -> Tuple[Player, World, Scheduler, Shop, DialogueNode]:
    if seed is not None:
        random.seed(seed)
    else:
        random.seed(CONFIG["seed"])
    world = World(CONFIG["world_width"], CONFIG["world_height"])
    world.generate()
    # Place player in first room center
    if world.rooms:
        px, py = world.rooms[0].center()
    else:
        px, py = world.width // 2, world.height // 2
    player = Player("Abdelfatah", px, py)
    # Equip starter
    player.inventory.equip(Equipment("Rusty Sword", "Weapon", attack=2))
    # Populate
    populate_world(world, player)
    # Add player to world entities
    world.place_entity(player, (player.x, player.y))
    # Add some NPCs
    if len(world.rooms) >= 2:
        nx, ny = world.rooms[1].center()
        npc_stats = Stats(hp=20, attack=2, defense=1)
        npc = Entity("Merchant", nx, ny, "M", "Merchants", npc_stats)
        world.place_entity(npc, (nx, ny))
    # Scheduler
    scheduler = Scheduler()
    for e in world.entities:
        scheduler.add(e)
    # Shop and dialogue
    shop = generate_shop()
    dialogue = generate_dialogue_tree()
    # Quests
    for q in generate_quests():
        player.quest_log.append(q)
    return player, world, scheduler, shop, dialogue

# -----------------------------
# Turn Processing
# -----------------------------

def process_turn(player: Player, world: World, scheduler: Scheduler):
    ent = scheduler.next_turn()
    if ent is None:
        return
    if ent is player:
        # Player turn handled by input
        pass
    else:
        if ent.ai:
            ent.ai.take_turn(world, player)
        ent.tick_statuses()

    # Quest progress (simple examples)
    # Explore rooms: count unique rooms visited
    visited_rooms = set()
    for r in world.rooms:
        x1, y1, x2, y2 = r.x1, r.y1, r.x2, r.y2
        if x1 <= player.x < x2 and y1 <= player.y < y2:
            visited_rooms.add(r)
    for q in player.quest_log:
        if q.title == "First Steps" and not q.completed:
            # If visited >= 3 rooms
            # We'll track via player.messages length as a proxy for exploration events
            if len(visited_rooms) >= 3:
                q.complete(player)
        if q.title == "Bandit Trouble" and not q.completed:
            # If any bandit dead
            if any(e.name == "Bandit" and not e.alive for e in world.entities):
                q.complete(player)

# -----------------------------
# Main Loop
# -----------------------------

def main():
    player, world, scheduler, shop, dialogue = init_game()
    # Events demo
    events = [
        Event("Merchant Discount", trigger_turn=50, action=lambda: setattr(shop, "price_multiplier", 0.9)),
        Event("Bandit Raid", trigger_turn=80, action=lambda: spawn_bandits(world)),
    ]
    while True:
        visible = world.compute_fov((player.x, player.y), player.vision_radius)
        draw(world, player, visible)
        for ev in events:
            ev.try_trigger(scheduler.turn)
        cmd = input("> ")
        handle_input(cmd, player, world, shop, dialogue, scheduler)
        process_turn(player, world, scheduler)
        time.sleep(CONFIG["turn_delay"])

def spawn_bandits(world: World):
    log("A bandit raid sweeps the area!")
    for _ in range(3):
        m = Monster("Bandit", 0, 0, "b", "Bandits", Stats(hp=15, attack=5, defense=1), LootTable([]))
        m.ai = AggressiveAI(m)
        # Place near random room
        if world.rooms:
            rx, ry = random.choice(world.rooms).center()
            # Find nearby walkable tile
            for _ in range(20):
                dx = random.randint(-3, 3)
                dy = random.randint(-3, 3)
                x, y = rx + dx, ry + dy
                if world.is_walkable(x, y):
                    world.place_entity(m, (x, y))
                    break

# -----------------------------
# Entry Point
# -----------------------------

if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\nGoodbye.")
