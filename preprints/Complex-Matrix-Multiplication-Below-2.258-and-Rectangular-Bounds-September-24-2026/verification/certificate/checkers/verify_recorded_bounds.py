"""Check the report's decimal inequalities using integers only."""
import json
from pathlib import Path
v=json.loads((Path(__file__).parent/'qP780_gmp.certificate.json').read_text())
U=int(v['difference_denominator']);a=list(map(int,v['difference_jet_upper']))
assert a[0]*10**20 < 3517*U
assert a[1]*25*10**17 < 1233*31*U
assert a[2]*625*10**15 < 4327*961*U
assert int(v['difference_degree236_upper'])*10**14 < 1902*U
n=int(v['residual_numerator_upper']);d=int(v['residual_denominator'])
assert n*10**25 < 3329*d
assert n*3*10**21 < d  # 6 epsilon/(2e-9) < 1e-12
print('All reported chart bounds and residual/inset inequalities PASS exactly')
