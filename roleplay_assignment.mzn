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
set of int: ASSIGNMENTS = 1..(s * roles);

% Decision Variables
array[ROUNDS, ASSIGNMENTS] of var set of PERSONS: assignments; % 2D array of set

% Derived Parameters
array[ASSIGNMENTS] of int: assignment_counts_min = [floor(n / (s * roles)) | _ in ASSIGNMENTS];
array[ASSIGNMENTS] of int: assignment_counts_max = [ceil(n / (s * roles)) | _ in ASSIGNMENTS];
array[ROUNDS, SCENES] of PERSONS: leaders = array2d(ROUNDS, SCENES, 1..(r * s));        % with symmetry breaking

% Channeling Variables
array[PERSONS, ROUNDS] of var ASSIGNMENTS: person_assignments; % 2D array of assignment index

% Helper Functions
function var int: get_role(var int: index) = (index - 1) div s + 1;
function var int: get_scene(var int: index) = (index - 1) mod s + 1;

% Constraints

% Channeling Constraints
constraint forall(round in ROUNDS) (
    int_set_channel(col(person_assignments, round), row(assignments, round))
);

% 1. Each person must be assigned to only one (scene, role) in each round.
constraint forall(round in ROUNDS) (
    partition_set(
        row(assignments, round),
        PERSONS
    )
);

% 2. Each person must appear in each scene at least once in a day.
constraint forall(person in PERSONS, scene in SCENES) (
    exists(round in ROUNDS) (
        get_scene(person_assignments[person, round]) == scene
    )
);

% 3. Each person must appear in each role at least once in a day.
constraint forall(person in PERSONS, role in ROLES) (
    exists(round in ROUNDS) (
        get_role(person_assignments[person, round]) == role
    )
);

% 4. Each person must be assigned to each (scene, role) at most once in a day.
constraint forall(person in PERSONS) (
    alldifferent(row(person_assignments, person))
);

% 5. The leader must be in the prosecution role.
constraint forall(round in ROUNDS, scene in SCENES) (
    leaders[round, scene] in assignments[round, (scene - 1) * roles + 1]
);

% 6. The number of persons assigned to each scene/role should be evenly distributed.
constraint forall(round in ROUNDS) (
    global_cardinality(col(person_assignments, round), set2array(ASSIGNMENTS), assignment_counts_min, assignment_counts_max)
);

% 7. Prioritize assigning extra persons to public role first, then observer, then prosecution.
constraint forall(round in ROUNDS) (
    forall(scene in SCENES) (
        let {
            int: prosecution_index = (scene - 1) * roles + 1,
            int: observer_index = (scene - 1) * roles + 2,
            int: public_index = (scene - 1) * roles + 3,
            var int: prosecution_count = card(assignments[round, prosecution_index]),
            var int: observer_count = card(assignments[round, observer_index]),
            var int: public_count = card(assignments[round, public_index])
        } in
        public_count >= observer_count /\ observer_count >= prosecution_count
    )
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
        format_role(fix(assignments[round, (scene - 1) * roles + 1]), fix(leaders[round, scene]), true) ++ ", " ++
        format_role(fix(assignments[round, (scene - 1) * roles + 2]), 1, false) ++ ", " ++
        format_role(fix(assignments[round, (scene - 1) * roles + 3]), 1, false)
        | round in ROUNDS, scene in SCENES
    ])
];
