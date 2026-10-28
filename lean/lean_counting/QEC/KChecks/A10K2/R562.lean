import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2248 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2248 = true := by
  decide +kernel

theorem tot2248 : totK PA10K2 A10K2.t2248 = [0, 0, 0, 876264156494, 2287204589899, 1525969446762, 227307512961, 6439430839, 0, 0] := by
  decide +kernel

theorem rows2249 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2249 = true := by
  decide +kernel

theorem tot2249 : totK PA10K2 A10K2.t2249 = [0, 0, 539714045080, 1779663171610, 1802752441025, 665077199449, 60790496763, 0, 0, 0] := by
  decide +kernel

theorem rows2250 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2250 = true := by
  decide +kernel

theorem tot2250 : totK PA10K2 A10K2.t2250 = [0, 0, 328041330167, 1553111735224, 2181868528348, 837754007112, 62210555275, 0, 0, 0] := by
  decide +kernel

theorem rows2251 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2251 = true := by
  decide +kernel

theorem tot2251 : totK PA10K2 A10K2.t2251 = [0, 0, 0, 578673729128, 1965963281523, 1817713838064, 388129396822, 12132367858, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
