import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4244 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4244 = true := by
  decide +kernel

theorem tot4244 : totK PA10K2 A10K2.t4244 = [462833872393, 1790358383166, 2048719754656, 629102731156, 43330261039, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4245 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4245 = true := by
  decide +kernel

theorem tot4245 : totK PA10K2 A10K2.t4245 = [122956571035, 1026423085242, 2163761078036, 1424143339732, 251264141579, 6853348008, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4246 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4246 = true := by
  decide +kernel

theorem tot4246 : totK PA10K2 A10K2.t4246 = [0, 583342381484, 2054374106188, 1972041094485, 457888144101, 12855574250, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4247 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4247 = true := by
  decide +kernel

theorem tot4247 : totK PA10K2 A10K2.t4247 = [0, 474272902674, 1666172031558, 1920082477405, 731662044967, 68750515780, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
