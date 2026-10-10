"""Conway's Game of Life на замкненому (тороїдальному) полі."""
import sys

ALIVE = "x"
DEAD = "."


def parse_input(text):
    """Повертає (кількість поколінь, поле) з тексту вхідного файлу."""
    lines = [line.strip() for line in text.strip().splitlines()]
    generations = int(lines[0])
    width, height = map(int, lines[1].split())
    rows = lines[2:2 + height]
    if len(rows) != height:
        raise ValueError(f"Очікувалось {height} рядків поля, отримано {len(rows)}")
    field = []
    for row in rows:
        if len(row) != width or any(ch not in (ALIVE, DEAD) for ch in row):
            raise ValueError(f"Некоректний рядок поля: {row!r}")
        field.append([ch == ALIVE for ch in row])
    return generations, field


def count_neighbors(field, row, col):
    """Кількість живих сусідів клітини з урахуванням замкненості поля."""
    height, width = len(field), len(field[0])
    count = 0
    for dr in (-1, 0, 1):
        for dc in (-1, 0, 1):
            if dr == 0 and dc == 0:
                continue
            if field[(row + dr) % height][(col + dc) % width]:
                count += 1
    return count


def next_cell_state(field, row, col):
    """Стан клітини (True - жива) у наступному поколінні."""
    neighbors = count_neighbors(field, row, col)
    if field[row][col]:
        return neighbors in (2, 3)
    return neighbors == 3


def next_generation(field):
    """Нове поле - наступне покоління."""
    return [
        [next_cell_state(field, r, c) for c in range(len(field[0]))]
        for r in range(len(field))
    ]


def simulate(field, generations):
    """Стан поля після заданої кількості поколінь."""
    for _ in range(generations):
        field = next_generation(field)
    return field


def format_field(field):
    return "\n".join("".join(ALIVE if cell else DEAD for cell in row) for row in field) + "\n"


def main(input_path, output_path):
    with open(input_path, encoding="utf-8") as f:
        generations, field = parse_input(f.read())
    with open(output_path, "w", encoding="utf-8") as f:
        f.write(format_field(simulate(field, generations)))


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("Використання: python game_of_life.py <input.txt> <output.txt>")
        sys.exit(1)
    main(sys.argv[1], sys.argv[2])
