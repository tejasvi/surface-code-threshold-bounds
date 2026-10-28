import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1076 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1076 = true := by
  decide +kernel

theorem tot1076 : totK PA10K2 A10K2.t1076 = [0, 610252771174, 1994517776027, 1869449653618, 489251548080, 27861475975, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1077 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1077 = true := by
  decide +kernel

theorem tot1077 : totK PA10K2 A10K2.t1077 = [0, 0, 825953017880, 2281312888466, 1675068233681, 293103732139, 6851704726, 0, 0, 0] := by
  decide +kernel

theorem rows1078 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1078 = true := by
  decide +kernel

theorem tot1078 : totK PA10K2 A10K2.t1078 = [0, 0, 414608699574, 1735270007780, 2159606093550, 752226243149, 56126783694, 0, 0, 0] := by
  decide +kernel

theorem rows1079 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1079 = true := by
  decide +kernel

theorem tot1079 : totK PA10K2 A10K2.t1079 = [0, 0, 504614257669, 1835882868141, 1894891783979, 522767952242, 32070512872, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
