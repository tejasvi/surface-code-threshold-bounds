import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1872 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1872 = true := by
  decide +kernel

theorem tot1872 : totK PA10K2 A10K2.t1872 = [0, 0, 0, 571718256217, 2057220365034, 2015797749450, 434537590567, 12746179907, 0, 0] := by
  decide +kernel

theorem rows1873 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1873 = true := by
  decide +kernel

theorem tot1873 : totK PA10K2 A10K2.t1873 = [0, 0, 0, 558661061888, 1797596620404, 1792705819493, 571088476987, 47952069846, 0, 0] := by
  decide +kernel

theorem rows1874 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1874 = true := by
  decide +kernel

theorem tot1874 : totK PA10K2 A10K2.t1874 = [0, 0, 0, 286915412457, 1529807182508, 2136715461676, 745759326522, 54728465214, 0, 0] := by
  decide +kernel

theorem rows1875 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1875 = true := by
  decide +kernel

theorem tot1875 : totK PA10K2 A10K2.t1875 = [0, 0, 0, 0, 536143204509, 1757170365527, 1744665920649, 472419820155, 30605747850, 0] := by
  decide +kernel

end QECKChecks.A10K2
