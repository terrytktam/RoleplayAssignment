include "globals.mzn";

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
array[PERSONS, ROUNDS, SCENES, ROLES] of var 0..1: assignments_bin;

% Derived Variables
int: role_counts_min = floor(n / (s * roles));
int: role_counts_max = ceil(n / (s * roles));
array[ROUNDS, SCENES] of PERSONS: leaders = array2d(ROUNDS, SCENES, 1..(r*s));        % with symmetry breaking
array[ROUNDS, SCENES, ROLES] of var int: role_counts; % Number of persons in each role

% Constraints

% Channeling Constraints
constraint forall(person in PERSONS, round in ROUNDS, scene in SCENES, role in ROLES) (
    (person in assignments[round, scene, role]) <-> (assignments_bin[person, round, scene, role] == 1)
);

% 1. Each person must be assigned to only one (scene, role) in each round.
constraint forall(person in PERSONS, round in ROUNDS) (
    count([assignments_bin[person, round, scene, role] | scene in SCENES, role in ROLES], 1, 1)
);

constraint redundant_constraint(
    forall(round in ROUNDS) (
        partition_set(
            [assignments[round, scene, role] | scene in SCENES, role in ROLES],
            PERSONS
        )
    )
);

% 2. Each person must appear in each scene at least once in a day.
constraint forall(person in PERSONS, scene in SCENES) (
    count_leq([assignments_bin[person, round, scene, role] | round in ROUNDS, role in ROLES], 1, 1)
);

% 3. Each person must be assigned to each (scene, role) at most once in a day.
constraint forall(person in PERSONS, scene in SCENES, role in ROLES) (
    count_geq([assignments_bin[person, round, scene, role] | round in ROUNDS], 1, 1)
);

% 4. The leader must be in the prosecution role.
constraint forall(round in ROUNDS, scene in SCENES) (
    leaders[round, scene] in assignments[round, scene, 1]
);

% 5. The number of persons assigned to each scene/role should be evenly distributed.
constraint forall(round in ROUNDS, scene in SCENES, role in ROLES) (
    let {
        array[PERSONS] of var int: temp = [assignments_bin[person, round, scene, role] | person in PERSONS]
    } in 
    global_cardinality(temp, [1], [role_counts_min], [role_counts_max])
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
