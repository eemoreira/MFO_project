// -*- mode: Bluespec; -*-
module battle {
  type CreatureType = Mage | Priest | Warrior | Monster
  type Option[a] = Some(a) | None

  type Creature = {
    hp: int,
    initiative: int,
    is_paralyzed: bool,
    is_imune: bool,
    is_taunted: bool,
    creature_type: CreatureType
  }

  type Effect = Unparalyzed | Paralyzed | Taunted
  type TurnDescription = 
  | Attack({attacker: Creature, receiver: Creature, damage: int})
  | Buff({caster: Creature, receiver: Creature, effect: Effect})
  | Imunity({caster: Creature})

  pure def sort(l: List[Creature]): List[Creature] = {
    pure val list_d20 = range(1, 21)
    list_d20.foldl([], (acc, i) => acc.concat(l.select(x => x.initiative == i)))
  }
  
  pure def damage(receiver: Creature, D: int): Creature = {
    {...receiver, hp: receiver.hp - if (receiver.is_imune) 0 else D}
  }
  pure def paralyze(receiver: Creature): Creature = {
    {...receiver, is_paralyzed: true}
  }
  pure def taunt(receiver: Creature): Creature = {
    {...receiver, is_taunted: true}
  }
  pure def make_imune(receiver: Creature): Creature = {
    {...receiver, is_imune: true}
  }
  pure def unmake_imune(receiver: Creature): Creature = {
    {...receiver, is_imune: false}
  }
  pure def unparalyze(receiver: Creature): Creature = {
    {...receiver, is_paralyzed: false}
  }
  pure def untaunt(receiver: Creature): Creature = {
    {...receiver, is_taunted: false}
  }

  var order: List[Creature]
  var round: int
  var start: bool
  var last_attack: Option[List[TurnDescription]]

  pure def different_team(c1: Creature, c2: Creature): bool = {
    or {
      c1.creature_type == Monster and c2.creature_type != Monster,
      c1.creature_type != Monster and c2.creature_type == Monster,
    }
  }

  action damage_attack(attacker: Creature, receiver: Creature, nxt: List[Creature]): bool = {
    val dmg = match attacker.creature_type {
      | Monster => if (start) 10 else 20
      | Mage => 10
      | Priest => 10
      | Warrior => 10
    }
    val attacker_next = match attacker.creature_type {
      | Monster => untaunt(attacker)
      | Mage => attacker
      | Warrior => attacker
      | Priest => attacker
    }
    all {
      different_team(attacker, receiver),
      attacker.is_paralyzed == false,
      or {
        attacker.creature_type == Monster and receiver.creature_type == Warrior,
        attacker.is_taunted == false,
      },
      attacker.hp > 0,
      receiver.hp > 0,
      order' = nxt.foldl([], (acc, i) => acc.append(if (i == receiver) damage(i, dmg) else 
        if (i == attacker) attacker_next else i)),
      last_attack' = Some([Attack({attacker: attacker, receiver: receiver, damage: dmg})])
    }
  }

  action paralyze_attack(attacker: Creature, receiver: Creature, nxt: List[Creature]): bool = {
    all {
      different_team(attacker, receiver),
      attacker.is_paralyzed == false,
      attacker.is_taunted == false,
      or {
        attacker.creature_type == Monster,
        attacker.creature_type == Mage
      },
      attacker.hp > 0,
      receiver.hp > 0,
      order' = nxt.foldl([], (acc, i) => acc.append(
        if (i == receiver) paralyze(i) else i)
      ),
      last_attack' = Some([Buff({caster: attacker, receiver: receiver, effect: Paralyzed})])
    }
  }

  action unparalyze_attack(attacker: Creature, receiver: Creature, nxt: List[Creature]): bool = {
    all {
      attacker != receiver,
      attacker.creature_type != Monster,
      receiver.creature_type != Monster,
      
      attacker.hp > 0,
      receiver.hp > 0,
      attacker.is_paralyzed == false,
      receiver.is_paralyzed == true,

      order' = nxt.foldl([], (acc, i) => acc.append(if (i == receiver) unparalyze(i) else i)),
      last_attack' = Some([Buff({caster: attacker, receiver: receiver, effect: Unparalyzed})])
    }
  }

  action cast_imunity(caster: Creature, nxt: List[Creature]): bool = all {
    caster.creature_type == Priest,
    caster.hp > 0,
    caster.is_paralyzed == false,
    order' = nxt.foldl([], (acc, i) => acc.append(if (i.creature_type == Monster) i else make_imune(i))),
    last_attack' = Some([Imunity({caster: caster})])
  }

  action cast_taunt(caster: Creature, receiver: Creature, nxt: List[Creature]): bool = all {
    caster.creature_type == Warrior,
    receiver.creature_type == Monster,
    caster.hp > 0,
    receiver.hp > 0,
    caster.is_paralyzed == false,
    order' = nxt.foldl([], (acc, i) => acc.append(if (i.creature_type == Monster) taunt(i) else i)),
    last_attack' = Some([Buff({caster: caster, receiver: receiver, effect: Taunted})])
  }

  action skip_turn(attacker: Creature, nxt: List[Creature]): bool = all {
    attacker.is_paralyzed or attacker.hp <= 0,
    attacker.is_taunted == false,
    val attacker_next = match attacker.creature_type {
      | Monster => unparalyze(untaunt(attacker))
      | Mage => attacker
      | Warrior => attacker
      | Priest => attacker
    }
    order' = nxt.foldl([], (acc, i) => acc.append(if (i == attacker) attacker_next else i)),
    last_attack' = None
  }

  def lose_buffs(attacker: Creature): List[Creature] = {
    match attacker.creature_type {
      | Priest => order.foldl([], (acc, i) => acc.append( if (i.creature_type == Monster) i else unmake_imune(i)))
      | _ => order
    }
  }
  
  action init = {
    pure val d20 = 1.to(20) 
    nondet mage_initiative = d20.oneOf()
    nondet priest_initiative = d20.oneOf()
    nondet warrior_initiative = d20.oneOf()
    nondet monster_initiative = d20.oneOf()
    all {
      order' = sort([
        {hp: 20, initiative: mage_initiative, is_paralyzed: false, is_imune: false, is_taunted: false, creature_type: Mage},
        {hp: 20, initiative: priest_initiative, is_paralyzed: false, is_imune: false, is_taunted: false, creature_type: Priest},
        {hp: 150, initiative: warrior_initiative, is_paralyzed: false, is_imune: false, is_taunted: false, creature_type: Warrior},
        {hp: 100, initiative: monster_initiative, is_paralyzed: false, is_imune: false, is_taunted: false, creature_type: Monster},
      ]),
      round' = 0,
      start' = true,
      last_attack' = None
    }
  }

  action step = all {
    val attacker = order[round]
    val everyone = order.indices().map(i => order[i])
    val enemies = everyone.filter(x => different_team(attacker, x))
    val allies = everyone.filter(x => not(different_team(attacker, x)))
    nondet enemy = enemies.oneOf()
    nondet ally = allies.oneOf()
    val now_order = lose_buffs(attacker)
    any {
      damage_attack(attacker, enemy, now_order),
      paralyze_attack(attacker, enemy, now_order),
      unparalyze_attack(attacker, ally, now_order),
      cast_imunity(attacker, now_order),
      cast_taunt(attacker, enemy, now_order),
      skip_turn(attacker, now_order),
    },
    start' = false,
    round' = (round + 1) % order.length(),
  }

  val no_deaths = order.foldl(true, (acc, i) => if (i.hp <= 0 or acc == false) false else true)
  val monster_alive = order.foldl(true, (acc, i) => 
    if (acc == false or (i.creature_type == Monster and i.hp <= 0)) false else true)

}
