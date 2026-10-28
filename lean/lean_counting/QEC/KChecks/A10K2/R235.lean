import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows940 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t940 = true := by
  decide +kernel

theorem tot940 : totK PA10K2 A10K2.t940 = [0, 0, 461906264153, 1837642546250, 1878016637585, 489405576670, 30831673886, 0, 0, 0] := by
  decide +kernel

theorem rows941 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t941 = true := by
  decide +kernel

theorem tot941 : totK PA10K2 A10K2.t941 = [0, 479736365516, 1694668276801, 1913779300835, 708618523037, 70155440251, 0, 0, 0, 0] := by
  decide +kernel

theorem rows942 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t942 = true := by
  decide +kernel

theorem tot942 : totK PA10K2 A10K2.t942 = [0, 162060387465, 1274728344208, 2208070273619, 982955607068, 71898826477, 0, 0, 0, 0] := by
  decide +kernel

theorem rows943 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t943 = true := by
  decide +kernel

theorem tot943 : totK PA10K2 A10K2.t943 = [0, 441258413222, 1469402244643, 1819364152056, 942461500205, 155270589051, 5976421810, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
