import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7200 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7200 = true := by
  decide +kernel

theorem tot7200 : totK PA10K2 A10K2.t7200 = [0, 0, 0, 778571077668, 2327660324147, 1680181171704, 268579680534, 6853348008, 0, 0] := by
  decide +kernel

theorem rows7201 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7201 = true := by
  decide +kernel

theorem tot7201 : totK PA10K2 A10K2.t7201 = [0, 0, 578505617916, 1874338849654, 1746894521455, 536087772707, 58148402154, 0, 0, 0] := by
  decide +kernel

theorem rows7202 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7202 = true := by
  decide +kernel

theorem tot7202 : totK PA10K2 A10K2.t7202 = [0, 0, 185282364397, 1188635671283, 2125557180933, 1084820293013, 184422205915, 19313972475, 0, 0] := by
  decide +kernel

theorem rows7203 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7203 = true := by
  decide +kernel

theorem tot7203 : totK PA10K2 A10K2.t7203 = [0, 0, 196485835502, 869717656207, 1874161738656, 1453298654948, 282894203957, 10760911071, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
