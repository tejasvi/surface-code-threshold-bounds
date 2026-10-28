import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4692 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4692 = true := by
  decide +kernel

theorem tot4692 : totK PA10K2 A10K2.t4692 = [0, 0, 64583550128, 770790724042, 2118599004185, 1669220265847, 274854224891, 7047025452, 0, 0] := by
  decide +kernel

theorem rows4693 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4693 = true := by
  decide +kernel

theorem tot4693 : totK PA10K2 A10K2.t4693 = [0, 0, 530811383570, 1974668328562, 2004701655258, 528848025295, 18791677882, 0, 0, 0] := by
  decide +kernel

theorem rows4694 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4694 = true := by
  decide +kernel

theorem tot4694 : totK PA10K2 A10K2.t4694 = [0, 0, 187219251666, 1179798150782, 2190221804042, 1297877286139, 154649353069, 0, 0, 0] := by
  decide +kernel

theorem rows4695 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4695 = true := by
  decide +kernel

theorem tot4695 : totK PA10K2 A10K2.t4695 = [0, 0, 0, 489871401428, 1871003131265, 2019161725111, 524533214347, 11979448558, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
