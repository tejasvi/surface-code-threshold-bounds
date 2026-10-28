import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows968 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t968 = true := by
  decide +kernel

theorem tot968 : totK PA10K2 A10K2.t968 = [0, 576020245237, 1915310087194, 1895800983468, 508363181945, 22578272449, 0, 0, 0, 0] := by
  decide +kernel

theorem rows969 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t969 = true := by
  decide +kernel

theorem tot969 : totK PA10K2 A10K2.t969 = [0, 0, 754648591002, 2212755695123, 1681070796050, 303891196395, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows970 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t970 = true := by
  decide +kernel

theorem tot970 : totK PA10K2 A10K2.t970 = [0, 0, 442038747095, 1695940857407, 2073400140842, 737295461977, 56143165367, 0, 0, 0] := by
  decide +kernel

theorem rows971 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t971 = true := by
  decide +kernel

theorem tot971 : totK PA10K2 A10K2.t971 = [0, 0, 489568046664, 1858065999080, 1953037910153, 528740220052, 31080743953, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
