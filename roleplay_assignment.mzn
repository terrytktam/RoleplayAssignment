include "globals.mzn";

% Constants
int: FEMALE = 0;
int: MALE = 1;

% Parameters
int: n; % Number of persons (assumed n >= r * s)
int: r; % Number of rounds (assumed r <= s * roles)
int: s = 4; % Number of scenes per round
int: roles = 3; % Number of roles per scene (Prosecution, Observer, Public)

set of int: PERSONS = 1..n;
set of int: PERSONS_0 = 0..n; % only used for printing
set of int: ROUNDS = 1..r;
set of int: SCENES = 0..(s - 1); % 0-indexing to make div easy
set of int: ROLES = 0..(roles - 1); % 0-indexing to make mod easy
set of int: SCENES_1 = 1..s;
set of int: ROLES_1 = 1..roles;
set of int: ASSIGNMENTS = 1..(s * roles); % 1-indexing to let int_set_channel work
set of int: GENDERS = FEMALE..MALE;
set of int: ALL_ASSIGNMENTS = 1..(r * s * roles);

% Decision Variables
array[ROUNDS, ASSIGNMENTS] of var set of PERSONS: assignments; % 2D array of set

% Derived Parameters
int: group_size_min = floor((n - 1) / (r * s));
array[ASSIGNMENTS] of int: assignment_counts_min = [floor(n / (s * roles)) | _ in ASSIGNMENTS];
array[ASSIGNMENTS] of int: assignment_counts_max = [ceil(n / (s * roles)) | _ in ASSIGNMENTS];
array[ROUNDS, SCENES] of PERSONS: leaders = array2d(ROUNDS, SCENES, 1..(r * s));        % with symmetry breaking

% Channeling Variables
array[PERSONS, ROUNDS] of var ASSIGNMENTS: person_assignments; % 2D array of assignment index

% Helper Functions
function bool: is_male(int: person) = person mod 2 == MALE; % Odd-numbered participants are male
function bool: is_female(int: person) = person mod 2 == FEMALE; % Even-numbered participants are female

% Constraints

% Channeling Constraints
constraint forall(round in ROUNDS) (
    int_set_channel(col(person_assignments, round), row(assignments, round))
);

% 1. Each person must be assigned to only one (scene, role) in each round.
constraint forall(round in ROUNDS) (
    partition_set(row(assignments, round), PERSONS)
);

% 2. Each person must appear in each scene at least once in a day.
%constraint forall(person in PERSONS, scene in SCENES) (
%    exists(round in ROUNDS) (
%        (person_assignments[person, round] - 1) div roles == scene
%    )
%);

% 3. Each person must appear in each role at least once in a day.
%constraint forall(person in PERSONS, role in ROLES) (
%    exists(round in ROUNDS) (
%        (person_assignments[person, round] - 1) mod roles == role
%    )
%);

% 4. Each person must be assigned to each (scene, role) at most once in a day.
constraint forall(person in PERSONS) (
    alldifferent(row(person_assignments, person))
);

% 5. The leader must be in the prosecution role.
constraint forall(round in ROUNDS, scene in SCENES) (
    leaders[round, scene] in assignments[round, scene * roles + 1]
);

% 6. The number of persons assigned to each scene/role should be evenly distributed.
constraint forall(round in ROUNDS) (
    global_cardinality(col(person_assignments, round), set2array(ASSIGNMENTS), 
                       assignment_counts_min, assignment_counts_max)
);

% 7. Prioritize assigning extra persons to public role first, then observer, then prosecution.
constraint forall(round in ROUNDS) (
    let {
        array[SCENES_1, ROLES_1] of var int: counts = array2d(SCENES_1, ROLES_1, 
                        [card(assignments[round, index]) | index in ASSIGNMENTS])
    } in 
    forall(scene in SCENES_1) (
        increasing(row(counts, scene))
    )
);

% 8. Ensure even gender distribution in each (scene, role) pair.
constraint forall(round in ROUNDS, index in ASSIGNMENTS) (
    let {
        var set of PERSONS: assigned_persons = assignments[round, index],
        var int: male_count = sum([is_male(person) | person in assigned_persons]),
        var int: female_count = sum([is_female(person) | person in assigned_persons])
    } in
    abs(male_count - female_count) <= 1
);

% 9. Ensure same group of persons not appeared in another group
constraint (
    let {
        array[ALL_ASSIGNMENTS] of var set of PERSONS: temp = array1d(ALL_ASSIGNMENTS, assignments)
    } in 
    not exists (i in ALL_ASSIGNMENTS, j in ALL_ASSIGNMENTS where i != j /\ 
        card(temp[i]) > group_size_min /\ card(temp[j]) > group_size_min) (
         temp[i] subset temp[j]
    )
);

% Solve and Output
solve satisfy;

% Helper function to format a set of persons with optional leader marking
function string: format_role(set of PERSONS: people, PERSONS_0: leader) =
    "[" ++ join(", ", [show(person) ++ if fix(person) == leader then "*" else "" endif | person in people]) ++ "]";

output [
    "Round, Scene, Prosecution, Observer, Public\n" ++
    join("\n", [
        "R" ++ show(round) ++ ", S" ++ show(scene + 1) ++ ", " ++
        format_role(fix(assignments[round, scene * roles + 1]), fix(leaders[round, scene])) ++ ", " ++
        format_role(fix(assignments[round, scene * roles + 2]), 0) ++ ", " ++
        format_role(fix(assignments[round, scene * roles + 3]), 0)
        | round in ROUNDS, scene in SCENES
    ])
];
