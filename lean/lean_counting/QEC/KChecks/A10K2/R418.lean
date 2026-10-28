import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1672 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1672 = true := by
  decide +kernel

theorem tot1672 : totK PA10K2 A10K2.t1672 = [0, 0, 845635952346, 2336179636723, 1393241547466, 134770169396, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1673 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1673 = true := by
  decide +kernel

theorem tot1673 : totK PA10K2 A10K2.t1673 = [0, 0, 532080823061, 1772722843286, 1849006403244, 528046353731, 31987755669, 0, 0, 0] := by
  decide +kernel

theorem rows1674 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1674 = true := by
  decide +kernel

theorem tot1674 : totK PA10K2 A10K2.t1674 = [0, 0, 495246187473, 1928087867803, 1908596837689, 443646623403, 13149912228, 0, 0, 0] := by
  decide +kernel

theorem rows1675 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1675 = true := by
  decide +kernel

theorem tot1675 : totK PA10K2 A10K2.t1675 = [0, 0, 414552127861, 1674738558392, 1979931644006, 570427162515, 32470943963, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
