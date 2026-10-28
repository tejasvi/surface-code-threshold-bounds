import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows88 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t88 = true := by
  decide +kernel

theorem tot88 : totK PA10K2 A10K2.t88 = [0, 257156802630, 1454455516419, 2223617520644, 832386495941, 60544467592, 0, 0, 0, 0] := by
  decide +kernel

theorem rows89 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t89 = true := by
  decide +kernel

theorem tot89 : totK PA10K2 A10K2.t89 = [0, 0, 511248783411, 1850846804960, 1768236396161, 471858129123, 30650496230, 0, 0, 0] := by
  decide +kernel

theorem rows90 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t90 = true := by
  decide +kernel

theorem tot90 : totK PA10K2 A10K2.t90 = [0, 465490222232, 1741307654390, 1887468075261, 584906621723, 48666249715, 0, 0, 0, 0] := by
  decide +kernel

theorem rows91 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t91 = true := by
  decide +kernel

theorem tot91 : totK PA10K2 A10K2.t91 = [0, 292657876421, 1482787282711, 2113048539754, 754335260303, 45543540946, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
