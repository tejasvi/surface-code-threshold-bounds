import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3916 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3916 = true := by
  decide +kernel

theorem tot3916 : totK PA10K2 A10K2.t3916 = [0, 0, 480247428435, 1864887159149, 2052499583009, 610072153467, 24715723405, 0, 0, 0] := by
  decide +kernel

theorem rows3917 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3917 = true := by
  decide +kernel

theorem tot3917 : totK PA10K2 A10K2.t3917 = [0, 0, 0, 702783002813, 2123606615770, 1675141490133, 361599733511, 13360781053, 0, 0] := by
  decide +kernel

theorem rows3918 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3918 = true := by
  decide +kernel

theorem tot3918 : totK PA10K2 A10K2.t3918 = [0, 0, 594293228886, 1958845819117, 1893672987736, 597702471197, 52591586694, 0, 0, 0] := by
  decide +kernel

theorem rows3919 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3919 = true := by
  decide +kernel

theorem tot3919 : totK PA10K2 A10K2.t3919 = [0, 0, 0, 778717704027, 2325085765526, 1699131745024, 278472250094, 7151180950, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
