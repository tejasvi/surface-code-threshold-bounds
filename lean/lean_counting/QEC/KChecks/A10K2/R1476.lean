import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5904 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5904 = true := by
  decide +kernel

theorem tot5904 : totK PA10K2 A10K2.t5904 = [482777079011, 1721414907032, 1765632016665, 550355145074, 37026429097, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5905 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5905 = true := by
  decide +kernel

theorem tot5905 : totK PA10K2 A10K2.t5905 = [0, 1026606339643, 2306668095570, 1080893741102, 90875893153, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5906 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5906 = true := by
  decide +kernel

theorem tot5906 : totK PA10K2 A10K2.t5906 = [477186847112, 1517078362649, 1775661948572, 954725971819, 192987727109, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5907 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5907 = true := by
  decide +kernel

theorem tot5907 : totK PA10K2 A10K2.t5907 = [309893393367, 1528154658498, 2191452587345, 920294476993, 80435464270, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
