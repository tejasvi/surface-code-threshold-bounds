import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3596 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3596 = true := by
  decide +kernel

theorem tot3596 : totK PA10K2 A10K2.t3596 = [0, 0, 561822984708, 1885368239845, 1864188479396, 546126658079, 33273707513, 0, 0, 0] := by
  decide +kernel

theorem rows3597 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3597 = true := by
  decide +kernel

theorem tot3597 : totK PA10K2 A10K2.t3597 = [0, 0, 0, 800496797059, 2241961730838, 1431239403101, 208161877181, 6034215561, 0, 0] := by
  decide +kernel

theorem rows3598 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3598 = true := by
  decide +kernel

theorem tot3598 : totK PA10K2 A10K2.t3598 = [0, 0, 498427024817, 1792436571832, 1812992517393, 530048798265, 45563051070, 0, 0, 0] := by
  decide +kernel

theorem rows3599 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3599 = true := by
  decide +kernel

theorem tot3599 : totK PA10K2 A10K2.t3599 = [0, 0, 303792748393, 1524841867545, 2125513963959, 739597193613, 45913727628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
