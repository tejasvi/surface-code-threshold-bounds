import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3348 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3348 = true := by
  decide +kernel

theorem tot3348 : totK PA10K2 A10K2.t3348 = [0, 0, 412935230681, 1653293305450, 2119029297577, 783179718336, 62559603274, 0, 0, 0] := by
  decide +kernel

theorem rows3349 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3349 = true := by
  decide +kernel

theorem tot3349 : totK PA10K2 A10K2.t3349 = [0, 0, 333592969070, 1569105579712, 2176418017934, 898948755849, 70829758956, 0, 0, 0] := by
  decide +kernel

theorem rows3350 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3350 = true := by
  decide +kernel

theorem tot3350 : totK PA10K2 A10K2.t3350 = [0, 0, 302214352193, 1292027113526, 1974716096743, 1183241322226, 210934141075, 6904928264, 0, 0] := by
  decide +kernel

theorem rows3351 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3351 = true := by
  decide +kernel

theorem tot3351 : totK PA10K2 A10K2.t3351 = [0, 0, 481950764876, 1821411041099, 1981843957262, 616015331664, 37890983068, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
