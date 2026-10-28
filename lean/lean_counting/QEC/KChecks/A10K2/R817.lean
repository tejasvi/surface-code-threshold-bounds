import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3268 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3268 = true := by
  decide +kernel

theorem tot3268 : totK PA10K2 A10K2.t3268 = [0, 0, 967617012463, 2414797360749, 1216124034479, 107167286853, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3269 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3269 = true := by
  decide +kernel

theorem tot3269 : totK PA10K2 A10K2.t3269 = [0, 474944754325, 1541162900511, 1768844524630, 965472571467, 194707687906, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows3270 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3270 = true := by
  decide +kernel

theorem tot3270 : totK PA10K2 A10K2.t3270 = [0, 117338935714, 965619970232, 2140946540836, 1573870544789, 289146031163, 6962742351, 0, 0, 0] := by
  decide +kernel

theorem rows3271 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3271 = true := by
  decide +kernel

theorem tot3271 : totK PA10K2 A10K2.t3271 = [0, 0, 579993560193, 1966012354199, 1873532539675, 576177884231, 41386495076, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
