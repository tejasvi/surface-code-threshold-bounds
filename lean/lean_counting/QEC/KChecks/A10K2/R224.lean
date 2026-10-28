import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows896 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t896 = true := by
  decide +kernel

theorem tot896 : totK PA10K2 A10K2.t896 = [0, 522523874245, 1690572230755, 1590692183138, 694426793054, 253635873707, 37310410385, 0, 0, 0] := by
  decide +kernel

theorem rows897 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t897 = true := by
  decide +kernel

theorem tot897 : totK PA10K2 A10K2.t897 = [0, 296752361392, 1504114845515, 2209023319697, 898342066901, 76765372953, 0, 0, 0, 0] := by
  decide +kernel

theorem rows898 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t898 = true := by
  decide +kernel

theorem tot898 : totK PA10K2 A10K2.t898 = [0, 0, 498391571909, 1855978117890, 1814494179346, 484594783991, 30780440178, 0, 0, 0] := by
  decide +kernel

theorem rows899 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t899 = true := by
  decide +kernel

theorem tot899 : totK PA10K2 A10K2.t899 = [0, 478610618287, 1757005624220, 1903329993686, 687040103047, 70696076066, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
