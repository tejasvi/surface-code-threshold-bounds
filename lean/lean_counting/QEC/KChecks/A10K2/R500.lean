import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2000 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2000 = true := by
  decide +kernel

theorem tot2000 : totK PA10K2 A10K2.t2000 = [0, 0, 0, 488620151044, 1859201762140, 1894296230802, 485622173010, 23500939800, 0, 0] := by
  decide +kernel

theorem rows2001 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2001 = true := by
  decide +kernel

theorem tot2001 : totK PA10K2 A10K2.t2001 = [0, 0, 0, 535651322330, 1970348585846, 2107160259998, 564213609197, 19145700860, 0, 0] := by
  decide +kernel

theorem rows2002 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2002 = true := by
  decide +kernel

theorem tot2002 : totK PA10K2 A10K2.t2002 = [0, 0, 483357255508, 1649191134061, 1669372909904, 729521283434, 258634132360, 37674914273, 0, 0] := by
  decide +kernel

theorem rows2003 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2003 = true := by
  decide +kernel

theorem tot2003 : totK PA10K2 A10K2.t2003 = [0, 0, 297281370121, 1517303165580, 2249335089321, 919402800164, 77750351646, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
