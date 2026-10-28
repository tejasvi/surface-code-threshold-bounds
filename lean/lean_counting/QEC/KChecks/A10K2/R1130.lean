import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4520 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4520 = true := by
  decide +kernel

theorem tot4520 : totK PA10K2 A10K2.t4520 = [0, 280546762594, 838303179229, 1048849963196, 1435927047324, 945206130244, 176749557325, 6239673734, 0, 0] := by
  decide +kernel

theorem rows4521 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4521 = true := by
  decide +kernel

theorem tot4521 : totK PA10K2 A10K2.t4521 = [0, 310258670533, 1420695346298, 2122597344533, 1084653823544, 121974831022, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4522 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4522 = true := by
  decide +kernel

theorem tot4522 : totK PA10K2 A10K2.t4522 = [0, 498968294647, 1903503114186, 1986257583700, 488260617374, 16719492270, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4523 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4523 = true := by
  decide +kernel

theorem tot4523 : totK PA10K2 A10K2.t4523 = [0, 0, 628649813381, 2099070331359, 1767624461238, 411295755103, 25660650750, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
