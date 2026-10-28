import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3292 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3292 = true := by
  decide +kernel

theorem tot3292 : totK PA10K2 A10K2.t3292 = [0, 0, 294439331526, 1597312740434, 2162526544740, 693394945979, 52575686575, 0, 0, 0] := by
  decide +kernel

theorem rows3293 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3293 = true := by
  decide +kernel

theorem tot3293 : totK PA10K2 A10K2.t3293 = [0, 0, 241745644269, 1089842333151, 1926580873620, 1180789348198, 187835277573, 5447185874, 0, 0] := by
  decide +kernel

theorem rows3294 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3294 = true := by
  decide +kernel

theorem tot3294 : totK PA10K2 A10K2.t3294 = [0, 0, 495048406196, 1816058118077, 1881973331199, 509393994160, 31174170042, 0, 0, 0] := by
  decide +kernel

theorem rows3295 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3295 = true := by
  decide +kernel

theorem tot3295 : totK PA10K2 A10K2.t3295 = [0, 0, 0, 828315550692, 2336229650432, 1324663810455, 141119893840, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
