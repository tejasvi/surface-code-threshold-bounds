import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6584 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6584 = true := by
  decide +kernel

theorem tot6584 : totK PA10K2 A10K2.t6584 = [0, 0, 464869552687, 1730438686199, 1878132181087, 583910389680, 37254374173, 0, 0, 0] := by
  decide +kernel

theorem rows6585 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6585 = true := by
  decide +kernel

theorem tot6585 : totK PA10K2 A10K2.t6585 = [0, 0, 212249636950, 1384328340474, 2233032713683, 866008948677, 52270131726, 0, 0, 0] := by
  decide +kernel

theorem rows6586 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6586 = true := by
  decide +kernel

theorem tot6586 : totK PA10K2 A10K2.t6586 = [0, 0, 298812713684, 1205784467817, 1868210542467, 1146650627758, 203437793984, 6354482628, 0, 0] := by
  decide +kernel

theorem rows6587 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6587 = true := by
  decide +kernel

theorem tot6587 : totK PA10K2 A10K2.t6587 = [0, 0, 296343083234, 1494887322658, 2260902232636, 969417881370, 74425195231, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
