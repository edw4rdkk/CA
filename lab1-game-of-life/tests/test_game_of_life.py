import pytest

from game_of_life import (
    count_neighbors,
    format_field,
    main,
    next_cell_state,
    next_generation,
    parse_input,
    simulate,
)


def field_from(*rows):
    return [[ch == "x" for ch in row] for row in rows]


# ---------- parse_input ----------

def test_parse_input_reads_generations_and_field():
    generations, field = parse_input("3\n3 2\n.x.\nx..\n")
    assert generations == 3
    assert field == field_from(".x.", "x..")


def test_parse_input_width_and_height_order():
    # "8 5" -> ширина 8, висота 5
    _, field = parse_input("0\n8 5\n" + "........\n" * 5)
    assert len(field) == 5
    assert len(field[0]) == 8


def test_parse_input_wrong_row_count_raises():
    with pytest.raises(ValueError):
        parse_input("1\n3 3\n...\n...\n")


def test_parse_input_wrong_row_length_raises():
    with pytest.raises(ValueError):
        parse_input("1\n3 2\n...\n....\n")


def test_parse_input_invalid_symbol_raises():
    with pytest.raises(ValueError):
        parse_input("1\n3 1\n.o.\n")


# ---------- count_neighbors (замкнене поле) ----------

def test_neighbors_in_center():
    field = field_from(
        "xxx",
        "xxx",
        "xxx",
    )
    assert count_neighbors(field, 1, 1) == 8


def test_neighbors_do_not_include_cell_itself():
    field = field_from("...", ".x.", "...")
    assert count_neighbors(field, 1, 1) == 0


def test_neighbors_wrap_left_right():
    # клітина c (лівий край) - правий сусід клітини d (правий край)
    field = field_from(
        ".....",
        ".....",
        "x....",
        ".....",
        ".....",
    )
    assert count_neighbors(field, 2, 4) == 1


def test_neighbors_wrap_top_bottom():
    # клітина a (верх) - нижній сусід клітини b (низ)
    field = field_from(
        "..x..",
        ".....",
        ".....",
        ".....",
        ".....",
    )
    assert count_neighbors(field, 4, 2) == 1


def test_neighbors_wrap_corner():
    # для кутової клітини сусіди в протилежних кутах
    field = field_from(
        "x...x",
        ".....",
        ".....",
        "x...x",
    )
    assert count_neighbors(field, 0, 0) == 3


# ---------- next_cell_state (правила) ----------

@pytest.mark.parametrize("neighbors, expected", [
    (0, False), (1, False), (2, True), (3, True), (4, False), (8, False),
])
def test_alive_cell_rules(neighbors, expected):
    positions = [(0, 0), (0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1), (2, 2)]
    field = [[False] * 5 for _ in range(5)]
    field[1][1] = True
    for r, c in positions[:neighbors]:
        field[r][c] = True
    assert next_cell_state(field, 1, 1) is expected


@pytest.mark.parametrize("neighbors, expected", [
    (0, False), (2, False), (3, True), (4, False),
])
def test_dead_cell_rules(neighbors, expected):
    positions = [(0, 0), (0, 1), (0, 2), (1, 0)]
    field = [[False] * 5 for _ in range(5)]
    for r, c in positions[:neighbors]:
        field[r][c] = True
    assert next_cell_state(field, 1, 1) is expected


# ---------- next_generation / simulate ----------

def test_block_is_still_life():
    block = field_from("....", ".xx.", ".xx.", "....")
    assert next_generation(block) == block


def test_blinker_oscillates():
    vertical = field_from(".....", "..x..", "..x..", "..x..", ".....")
    horizontal = field_from(".....", ".....", ".xxx.", ".....", ".....")
    assert next_generation(vertical) == horizontal
    assert next_generation(horizontal) == vertical


def test_next_generation_does_not_modify_input():
    field = field_from(".....", "..x..", "..x..", "..x..", ".....")
    copy = [row[:] for row in field]
    next_generation(field)
    assert field == copy


def test_blinker_across_border():
    # мигалка, що перетинає верхній/нижній край
    field = field_from("..x..", "..x..", ".....", ".....", "..x..")
    expected = field_from(".xxx.", ".....", ".....", ".....", ".....")
    assert next_generation(field) == expected


def test_glider_returns_to_shape_after_full_torus_cycle():
    # на полі 5x5 планер повертається в початковий стан через 20 поколінь
    glider = field_from(".x...", "..x..", "xxx..", ".....", ".....")
    assert simulate(glider, 20) == glider


def test_simulate_zero_generations_returns_same_field():
    field = field_from("x.", ".x")
    assert simulate(field, 0) == field


def test_empty_field_stays_empty():
    field = field_from("...", "...")
    assert simulate(field, 5) == field


# ---------- format_field / main ----------

def test_format_field():
    assert format_field(field_from("x.", ".x")) == "x.\n.x\n"


def test_main_example_from_task(tmp_path):
    input_file = tmp_path / "input.txt"
    output_file = tmp_path / "output.txt"
    input_file.write_text(
        "3\n8 5\n........\n..x.....\n..x.....\n..x.....\n........\n"
    )
    main(str(input_file), str(output_file))
    assert output_file.read_text() == (
        "........\n........\n.xxx....\n........\n........\n"
    )
