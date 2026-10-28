import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows32 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t32 = true := by
  decide +kernel

theorem tot32 : totK PA10K2 A10K2.t32 = [0, 823975201789, 2347556566359, 1681180827079, 267412014981, 14654565803, 0, 0, 0, 0] := by
  decide +kernel

theorem rows33 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t33 = true := by
  decide +kernel

theorem tot33 : totK PA10K2 A10K2.t33 = [512637402434, 1854412427110, 1947629527035, 571973330888, 50760932925, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows34 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t34 = true := by
  decide +kernel

theorem tot34 : totK PA10K2 A10K2.t34 = [323642880550, 1507717476769, 2170768484767, 923577666341, 76896540718, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows35 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t35 = true := by
  decide +kernel

theorem tot35 : totK PA10K2 A10K2.t35 = [0, 546179801325, 1975722220101, 1990892334367, 448902824912, 13816090359, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
