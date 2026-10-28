"""Emit separate, reviewable Magma data modules from an integral seed fixture."""
from __future__ import annotations
from pathlib import Path

NAMES = {
    'distinct': 'FFCSeedDistinct',
    'square_other': 'FFCSeedSquareOther',
    'difference': 'FFCSeedDifference',
    'square_diagonal': 'FFCSeedSquareDiagonal',
}

def data_modules(data: dict) -> dict[str, str]:
    modules = {}
    lines = ['// Lexicographic edge/minor labels; generated offline.',
             'FFCResolventEdges := [']
    lines += ['    <' + ','.join(str(x+1) for x in e) + '>, '
              for e in data['edges']]
    lines[-1] = lines[-1].rstrip(', ')
    lines += ['];', '', 'FFCResolventMinorIndices := [']
    lines += ['    <' + ','.join(str(x+1) for x in e) + '>, '
              for e in data['minors']]
    lines[-1] = lines[-1].rstrip(', ')
    lines += ['];']
    modules['resolvent_indices.m'] = '\n'.join(lines)+'\n'
    for key, identifier in NAMES.items():
        lines = [f'// Integral Bhargava sextic seed: {key}.',
                 '// Generated data: <coefficient,minor1,minor2,minor3>.',
                 '// Minor labels are one-based. Do not edit by hand.',
                 f'{identifier} := [']
        terms = ['<' + ','.join(map(str, [c, a+1, b+1, d+1])) + '>'
                 for c, a, b, d in data['forms'][key]]
        for i in range(0, len(terms), 5):
            lines.append('    '+', '.join(terms[i:i+5])
                         + (',' if i+5 < len(terms) else ''))
        lines.append('];')
        modules[f'seed_{key}.m'] = '\n'.join(lines)+'\n'
    return modules

def write_data(data: dict, directory: Path) -> None:
    directory.mkdir(parents=True, exist_ok=True)
    for name, text in data_modules(data).items():
        assert len(text.splitlines()) <= 500
        (directory/name).write_text(text)

if __name__ == '__main__':
    import json
    root = Path(__file__).resolve().parents[1]
    data = json.loads((root/'tests/fixtures/resolvent_integral_minors.json').read_text())
    write_data(data, root/'src/data')
