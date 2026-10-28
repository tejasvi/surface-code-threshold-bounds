import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3512 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3512 = true := by
  decide +kernel

theorem tot3512 : totK PA10K2 A10K2.t3512 = [0, 0, 0, 291413414767, 1453574747204, 2239639494755, 1004196592636, 96790837658, 0, 0] := by
  decide +kernel

theorem rows3513 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3513 = true := by
  decide +kernel

theorem tot3513 : totK PA10K2 A10K2.t3513 = [0, 0, 0, 336095379087, 1359934153145, 1911796589938, 1001864704474, 186824536531, 6962742351, 0] := by
  decide +kernel

theorem rows3514 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3514 = true := by
  decide +kernel

theorem tot3514 : totK PA10K2 A10K2.t3514 = [0, 0, 0, 246086659826, 1487461121964, 2181918129068, 690879524532, 34209726918, 0, 0] := by
  decide +kernel

theorem rows3515 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3515 = true := by
  decide +kernel

theorem tot3515 : totK PA10K2 A10K2.t3515 = [0, 0, 0, 433796549788, 1417586436409, 1754927974519, 929522415919, 140528652703, 5460492893, 0] := by
  decide +kernel

end QECKChecks.A10K2
