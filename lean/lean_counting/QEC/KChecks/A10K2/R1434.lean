import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5736 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5736 = true := by
  decide +kernel

theorem tot5736 : totK PA10K2 A10K2.t5736 = [0, 311053418201, 1507263717577, 2092699408104, 808867102375, 60970094597, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5737 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5737 = true := by
  decide +kernel

theorem tot5737 : totK PA10K2 A10K2.t5737 = [0, 0, 746667734421, 2190636505261, 1541688392157, 248335805736, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows5738 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5738 = true := by
  decide +kernel

theorem tot5738 : totK PA10K2 A10K2.t5738 = [0, 0, 425876323216, 1719349841064, 1986273312022, 550012017933, 31987876949, 0, 0, 0] := by
  decide +kernel

theorem rows5739 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5739 = true := by
  decide +kernel

theorem tot5739 : totK PA10K2 A10K2.t5739 = [0, 0, 496754798690, 1802717362488, 1890379701196, 553548440466, 32911643181, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
