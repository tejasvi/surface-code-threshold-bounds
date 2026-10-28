import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6204 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6204 = true := by
  decide +kernel

theorem tot6204 : totK PA10K2 A10K2.t6204 = [0, 0, 537294396730, 1802600840560, 1829336309154, 513289029229, 31987755669, 0, 0, 0] := by
  decide +kernel

theorem rows6205 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6205 = true := by
  decide +kernel

theorem tot6205 : totK PA10K2 A10K2.t6205 = [0, 0, 489932137708, 1973406141254, 2017613738235, 445096180402, 13149912228, 0, 0, 0] := by
  decide +kernel

theorem rows6206 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6206 = true := by
  decide +kernel

theorem tot6206 : totK PA10K2 A10K2.t6206 = [0, 0, 552283864504, 1874631786615, 1808808325882, 475577543079, 32035881770, 0, 0, 0] := by
  decide +kernel

theorem rows6207 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6207 = true := by
  decide +kernel

theorem tot6207 : totK PA10K2 A10K2.t6207 = [0, 0, 432295944633, 1636629436452, 1897587089326, 587107373130, 50267370225, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
