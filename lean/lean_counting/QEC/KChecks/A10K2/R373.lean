import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1492 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1492 = true := by
  decide +kernel

theorem tot1492 : totK PA10K2 A10K2.t1492 = [0, 0, 0, 761544880626, 2246087089669, 1745967334574, 303878906736, 6853348008, 0, 0] := by
  decide +kernel

theorem rows1493 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1493 = true := by
  decide +kernel

theorem tot1493 : totK PA10K2 A10K2.t1493 = [0, 0, 0, 501917368618, 1881418876116, 2022299261799, 646285862655, 41407999670, 0, 0] := by
  decide +kernel

theorem rows1494 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1494 = true := by
  decide +kernel

theorem tot1494 : totK PA10K2 A10K2.t1494 = [0, 0, 0, 484822608914, 1769125139635, 1872928597884, 500317357238, 31222411477, 0, 0] := by
  decide +kernel

theorem rows1495 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1495 = true := by
  decide +kernel

theorem tot1495 : totK PA10K2 A10K2.t1495 = [0, 0, 0, 228291545225, 1305613345238, 2090503882759, 1094099502828, 221258620777, 14945844243, 0] := by
  decide +kernel

end QECKChecks.A10K2
