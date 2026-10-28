import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3164 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3164 = true := by
  decide +kernel

theorem tot3164 : totK PA10K2 A10K2.t3164 = [0, 0, 260755658891, 1023832254257, 1794194292126, 1450214829862, 286142500834, 11918539728, 0, 0] := by
  decide +kernel

theorem rows3165 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3165 = true := by
  decide +kernel

theorem tot3165 : totK PA10K2 A10K2.t3165 = [0, 0, 401322630837, 1753277263758, 2099489663494, 637834087198, 33055448423, 0, 0, 0] := by
  decide +kernel

theorem rows3166 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3166 = true := by
  decide +kernel

theorem tot3166 : totK PA10K2 A10K2.t3166 = [0, 0, 211927423510, 1217411242191, 2132475823871, 1253121212025, 186921985071, 6772895877, 0, 0] := by
  decide +kernel

theorem rows3167 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3167 = true := by
  decide +kernel

theorem tot3167 : totK PA10K2 A10K2.t3167 = [0, 0, 0, 608964449560, 2095370285475, 1924546987927, 356988780052, 6880363793, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
