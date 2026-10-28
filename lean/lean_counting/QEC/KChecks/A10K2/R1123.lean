import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4492 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4492 = true := by
  decide +kernel

theorem tot4492 : totK PA10K2 A10K2.t4492 = [0, 0, 426060174196, 1739494675980, 2061024603398, 652531382240, 29031327120, 0, 0, 0] := by
  decide +kernel

theorem rows4493 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4493 = true := by
  decide +kernel

theorem tot4493 : totK PA10K2 A10K2.t4493 = [0, 582386665861, 1946893078427, 1777020004452, 443624308689, 67575646421, 26011840508, 0, 0, 0] := by
  decide +kernel

theorem rows4494 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4494 = true := by
  decide +kernel

theorem tot4494 : totK PA10K2 A10K2.t4494 = [0, 287423613328, 1447862023625, 2209126258039, 904134679804, 68612353862, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4495 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4495 = true := by
  decide +kernel

theorem tot4495 : totK PA10K2 A10K2.t4495 = [0, 0, 484955328744, 1807772063849, 1882191085354, 502520341662, 31768748853, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
