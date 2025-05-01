include "globals.mzn";

% Constants
int: FEMALE = 0;
int: MALE = 1;

% Parameters
int: n; % Number of persons (assumed n >= r * s)
int: r; % Number of rounds (assumed r <= s * roles)
enum Scenes = {S1, S2, S3, S4};
enum Roles = {Prosecution, Observer, Public};
type Assignment = tuple(Scenes, Roles);
int: s = card(Scenes); % Number of scenes per round
int: roles = card(Roles); % Number of roles per scene

set of int: SCENES = enum2int(Scenes);
set of int: ROLES = enum2int(Roles);
array[int] of Assignment: allAssignments = [ (scene, role) | scene in Scenes, role in Roles ];
set of int: PERSONS = 1..n;
set of int: PERSONS_0 = 0..n; % only used for printing
set of int: ROUNDS = 1..r;
set of int: ASSIGNMENTS = 1..length(allAssignments);
set of int: GENDERS = FEMALE..MALE;
set of int: ALL_ASSIGNMENTS = 1..(r * s * roles);

% Decision Variables
array[ROUNDS, ASSIGNMENTS] of var set of PERSONS: assignments; % 2D array of set

% Derived Parameters
int: group_size_min = floor((n - 1) / (r * s));
array[SCENES] of int: scene_counts_min = [floor(r / s) | _ in SCENES];
array[ROLES] of int: role_counts_min = [floor(r / roles) | _ in ROLES];
array[ASSIGNMENTS] of int: assignment_counts_min = [floor(n / (s * roles)) | _ in ASSIGNMENTS];
array[ASSIGNMENTS] of int: assignment_counts_max = [ceil(n / (s * roles)) | _ in ASSIGNMENTS];
array[ROUNDS, SCENES] of PERSONS: leaders = array2d(ROUNDS, SCENES, 1..(r * s));        % with symmetry breaking
set of PERSONS: non_leaders = PERSONS diff 1..(r * s);

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

% 2. Each person must appear in each scene/role at least once in a day.
constraint forall(person in PERSONS) (
    let {
        array[SCENES, ROLES] of var 0..1: temp = array2d(SCENES, ROLES, 
            global_cardinality(row(person_assignments, person), ASSIGNMENTS))
    } in
    [count(row(temp, scene), 1) | scene in SCENES] >= scene_counts_min /\ 
    [count(col(temp, role), 1) | role in ROLES] >= role_counts_min 
);

% 4. Each person must be assigned to each (scene, role) at most once in a day.
constraint forall(person in PERSONS) (
    alldifferent(row(person_assignments, person))
);

% 5. The leader must be in the prosecution role.
constraint forall(round in ROUNDS, scene in SCENES) (
    leaders[round, scene] in assignments[round, arg_val(allAssignments, (to_enum(Scenes, scene), Prosecution))]
);

% 6. The number of persons assigned to each scene/role should be evenly distributed.
constraint forall(round in ROUNDS) (
    global_cardinality(col(person_assignments, round), set2array(ASSIGNMENTS), 
                       assignment_counts_min, assignment_counts_max)
);

% 7. Prioritize assigning extra persons to public role first, then observer, then prosecution.
constraint forall(round in ROUNDS) (
    let {
        array[SCENES, ROLES] of var int: counts = array2d(SCENES, ROLES, 
                        [card(assignments[round, index]) | index in ASSIGNMENTS])
    } in 
    forall(scene in SCENES) (
        increasing(row(counts, scene))
    )
);

% 9. Ensure same group of persons not appeared in another group (nice to have)
%constraint (
%    let {
%        array[ALL_ASSIGNMENTS] of var set of PERSONS: temp = array1d(ALL_ASSIGNMENTS, assignments)
%    } in 
%    not exists (i in ALL_ASSIGNMENTS, j in ALL_ASSIGNMENTS where i != j /\ 
%        card(temp[i]) > group_size_min /\ card(temp[j]) > group_size_min) (
%         temp[i] subset temp[j]
%    )
%);

% 10. Assign same-gender non-leaders in ascending order for the first round
constraint symmetry_breaking_constraint(
    let {
        array[PERSONS] of var ASSIGNMENTS: round1_assignments = col(person_assignments, 1)
    } in
    increasing([round1_assignments[person] | person in non_leaders where is_male(person)]) /\
    increasing([round1_assignments[person] | person in non_leaders where is_female(person)])
);

var int: gender_imbalance = 
    sum(round in ROUNDS, index in ASSIGNMENTS) (
        let {
            var set of PERSONS: assigned_persons = assignments[round, index],
            var int: male_count = sum([is_male(person) | person in assigned_persons]),
            var int: female_count = sum([is_female(person) | person in assigned_persons]),
            var int: diff_count = abs(male_count - female_count),
            var int: total_count = male_count + female_count
        } in
        (diff_count > 1 \/ total_count mod 2 == 0) * diff_count
    );

% Solve and Output
solve minimize gender_imbalance;

% Helper function to format a set of persons with optional leader marking
function string: format_role(set of PERSONS: people, PERSONS_0: leader) =
    "[" ++ join(", ", [show(person) ++ if fix(person) == leader then "*" else "" endif | person in people]) ++ "]";

output [
    "Round, Scene, Prosecution, Observer, Public\n" ++
    join("\n", [
        "R" ++ show(round) ++ ", " ++ show(scene) ++ ", " ++
        format_role(fix(assignments[round, arg_val(allAssignments, (scene, Prosecution))]), fix(leaders[round, enum2int(scene)])) ++ ", " ++
        format_role(fix(assignments[round, arg_val(allAssignments, (scene, Observer))]), 0) ++ ", " ++
        format_role(fix(assignments[round, arg_val(allAssignments, (scene, Public))]), 0)
        | round in ROUNDS, scene in Scenes
    ]) ++ "\nGender imbalance: " ++ show(gender_imbalance)
];
