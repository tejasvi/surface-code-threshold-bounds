import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1136 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1136 = true := by
  decide +kernel

theorem tot1136 : totK PA10K2 A10K2.t1136 = [0, 0, 0, 289071339824, 1293285235892, 1956647377948, 1068304352470, 185422661592, 6318667960, 0] := by
  decide +kernel

theorem rows1137 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1137 = true := by
  decide +kernel

theorem tot1137 : totK PA10K2 A10K2.t1137 = [0, 0, 0, 434779930692, 1768062996076, 2093440750434, 604606020102, 24692530783, 0, 0] := by
  decide +kernel

theorem rows1138 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1138 = true := by
  decide +kernel

theorem tot1138 : totK PA10K2 A10K2.t1138 = [0, 0, 0, 57125207890, 793493010573, 2114095534464, 1596359922024, 262824506706, 6439430839, 0] := by
  decide +kernel

theorem rows1139 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1139 = true := by
  decide +kernel

theorem tot1139 : totK PA10K2 A10K2.t1139 = [0, 0, 0, 483279304589, 1838824725103, 1928908072216, 512594946997, 22108643497, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
