import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3704 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3704 = true := by
  decide +kernel

theorem tot3704 : totK PA10K2 A10K2.t3704 = [0, 0, 455336079951, 1432258186964, 1807631172339, 977937520521, 167861161288, 6121173289, 0, 0] := by
  decide +kernel

theorem rows3705 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3705 = true := by
  decide +kernel

theorem tot3705 : totK PA10K2 A10K2.t3705 = [0, 385220696395, 1259620514905, 1611486843629, 1143476302817, 413576485043, 37002215526, 0, 0, 0] := by
  decide +kernel

theorem rows3706 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3706 = true := by
  decide +kernel

theorem tot3706 : totK PA10K2 A10K2.t3706 = [0, 311403322303, 1518938667514, 2074895219388, 729135247893, 45038217099, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3707 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3707 = true := by
  decide +kernel

theorem tot3707 : totK PA10K2 A10K2.t3707 = [0, 0, 466958533566, 1777777266756, 1802210865403, 459229978478, 30831673886, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
