import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5652 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5652 = true := by
  decide +kernel

theorem tot5652 : totK PA10K2 A10K2.t5652 = [0, 202906917944, 956577667641, 1855558470908, 1454286568940, 278907601054, 11427838733, 0, 0, 0] := by
  decide +kernel

theorem rows5653 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5653 = true := by
  decide +kernel

theorem tot5653 : totK PA10K2 A10K2.t5653 = [0, 405287277353, 1626404031384, 1985926928747, 679030433217, 52232171148, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5654 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5654 = true := by
  decide +kernel

theorem tot5654 : totK PA10K2 A10K2.t5654 = [0, 196962003141, 1375145621215, 2206587981791, 921287004430, 67328593344, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5655 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5655 = true := by
  decide +kernel

theorem tot5655 : totK PA10K2 A10K2.t5655 = [0, 0, 576040402367, 1961740232086, 1715905699985, 388177195855, 21329223247, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
