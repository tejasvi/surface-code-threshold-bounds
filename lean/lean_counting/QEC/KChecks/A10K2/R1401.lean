import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5604 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5604 = true := by
  decide +kernel

theorem tot5604 : totK PA10K2 A10K2.t5604 = [0, 0, 0, 479738933771, 1838455934812, 1807835338686, 483248983145, 30831673886, 0, 0] := by
  decide +kernel

theorem rows5605 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5605 = true := by
  decide +kernel

theorem tot5605 : totK PA10K2 A10K2.t5605 = [0, 0, 461371995414, 1743208525455, 1914461392376, 619248396236, 50957229202, 0, 0, 0] := by
  decide +kernel

theorem rows5606 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5606 = true := by
  decide +kernel

theorem tot5606 : totK PA10K2 A10K2.t5606 = [0, 0, 285265752648, 1433521228555, 2109009273538, 804746425740, 45801667654, 0, 0, 0] := by
  decide +kernel

theorem rows5607 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5607 = true := by
  decide +kernel

theorem tot5607 : totK PA10K2 A10K2.t5607 = [0, 0, 292796036164, 1245797438706, 1883737981705, 1035532535076, 166256483150, 5705019915, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
