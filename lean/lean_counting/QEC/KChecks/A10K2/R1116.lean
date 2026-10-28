import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4464 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4464 = true := by
  decide +kernel

theorem tot4464 : totK PA10K2 A10K2.t4464 = [0, 50726977509, 774196744125, 2072125066447, 1410577279071, 212986111769, 6121173289, 0, 0, 0] := by
  decide +kernel

theorem rows4465 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4465 = true := by
  decide +kernel

theorem tot4465 : totK PA10K2 A10K2.t4465 = [0, 570823472187, 1948886399055, 1904468595454, 504548041183, 25852139541, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4466 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4466 = true := by
  decide +kernel

theorem tot4466 : totK PA10K2 A10K2.t4466 = [288971484021, 1029811506616, 1559411014207, 1397769689164, 543559527793, 49730410605, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4467 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4467 = true := by
  decide +kernel

theorem tot4467 : totK PA10K2 A10K2.t4467 = [179565788182, 1146804975327, 1891008483100, 1138284701483, 311989085054, 25371180993, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
