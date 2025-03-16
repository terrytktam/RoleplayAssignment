% Parameters
int: n; % Number of persons
int: r; % Number of rounds
int: s = 4; % Number of scenes per round
int: roles = 3; % Number of roles per scene (Prosecution, Observer, Public)

set of int: PERSONS = 1..n;
set of int: ROUNDS = 1..r;
set of int: SCENES = 1..s;
set of int: ROLES = 1..roles;

% Decision Variables
array[ROUNDS, SCENES, ROLES] of var set of PERSONS: assignments;
array[ROUNDS, SCENES] of var PERSONS: leaders =
    array2d(ROUNDS, SCENES, [(round - 1) * s + scene | round in ROUNDS, scene in SCENES]);        % with symmetry breaking

% Derived Variables
array[ROUNDS, SCENES, ROLES] of var int: role_counts; % Number of persons in each role

% Constraints

% 1. Each person must be assigned to only one (scene, role) in each round.
constraint forall(round in ROUNDS, person in PERSONS) (
    sum(scene in SCENES, role in ROLES) (person in assignments[round, scene, role]) == 1
);

% 2. Each person must appear in each scene at least once in a day.
constraint forall(person in PERSONS, scene in SCENES) (
    sum(round in ROUNDS, role in ROLES) (person in assignments[round, scene, role]) >= 1
);

% 3. Each person must be assigned to each (scene, role) at most once in a day.
constraint forall(person in PERSONS, scene in SCENES, role in ROLES) (
    sum(round in ROUNDS) (person in assignments[round, scene, role]) <= 1
);

% 4. One person should be assigned as a leader at most once in a day.
constraint forall(person in PERSONS) (
    sum(round in ROUNDS, scene in SCENES) (leaders[round, scene] == person) <= 1
);

% 5. The leader must be in the prosecution role.
constraint forall(round in ROUNDS, scene in SCENES) (
    leaders[round, scene] in assignments[round, scene, 1]
);

% 6. The number of persons assigned to each scene/role should be evenly distributed.
constraint forall(round in ROUNDS, scene in SCENES, role in ROLES) (
    role_counts[round, scene, role] = card(assignments[round, scene, role])
);

% Ensure even distribution of roles
constraint forall(round in ROUNDS, scene in SCENES, role in ROLES) (
    role_counts[round, scene, role] >= floor(n / (s * roles)) /\
    role_counts[round, scene, role] <= ceil(n / (s * roles))
);

% Solve and Output
solve satisfy;

% Helper function to format a set of persons with optional leader marking
function string: format_role(set of PERSONS: people, var PERSONS: leader, bool: is_prosecution) =
    "[" ++ join(", ", [show(person) ++ if is_prosecution /\ fix(person) == fix(leader) then "*" else "" endif | person in people]) ++ "]";

output [
    "Round, Scene, Prosecution, Observer, Public\n" ++
    join("\n", [
        "R" ++ show(round) ++ ", S" ++ show(scene) ++ ", " ++
        format_role(fix(assignments[round, scene, 1]), fix(leaders[round, scene]), true) ++ ", " ++
        format_role(fix(assignments[round, scene, 2]), 1, false) ++ ", " ++
        format_role(fix(assignments[round, scene, 3]), 1, false)
        | round in ROUNDS, scene in SCENES
    ])
];
