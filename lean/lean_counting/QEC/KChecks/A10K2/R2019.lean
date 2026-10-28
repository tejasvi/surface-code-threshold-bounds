import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8076 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8076 = true := by
  decide +kernel

theorem tot8076 : totK PA10K2 A10K2.t8076 = [0, 0, 0, 395161753973, 1722144365375, 2167047812010, 751373081616, 42174205061, 0, 0] := by
  decide +kernel

theorem rows8077 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8077 = true := by
  decide +kernel

theorem tot8077 : totK PA10K2 A10K2.t8077 = [0, 0, 0, 587703598815, 1989465295290, 1918162930760, 502941002564, 19269616899, 0, 0] := by
  decide +kernel

theorem rows8078 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8078 = true := by
  decide +kernel

theorem tot8078 : totK PA10K2 A10K2.t8078 = [0, 0, 0, 0, 747049541375, 2288041465365, 1670763039790, 243032274023, 6632180018, 0] := by
  decide +kernel

theorem rows8079 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8079 = true := by
  decide +kernel

theorem tot8079 : totK PA10K2 A10K2.t8079 = [0, 0, 0, 568700286610, 1929436942794, 1847897360594, 506013478343, 38823112937, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
