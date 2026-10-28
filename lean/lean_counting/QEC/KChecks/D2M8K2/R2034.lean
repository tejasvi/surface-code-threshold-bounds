import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8136 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8136 = true := by
  decide +kernel

theorem tot8136 : totK PD2M8K2 D2M8K2.t8136 = [0, 0, 177779237885, 462335191848, 232120061010, 15857123079, 0, 0] := by
  decide +kernel

theorem rows8137 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8137 = true := by
  decide +kernel

theorem tot8137 : totK PD2M8K2 D2M8K2.t8137 = [0, 0, 175301511421, 462531895137, 209225347676, 12297600962, 0, 0] := by
  decide +kernel

theorem rows8138 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8138 = true := by
  decide +kernel

theorem tot8138 : totK PD2M8K2 D2M8K2.t8138 = [0, 0, 53965485891, 335214243662, 399592554372, 74956773512, 1206465782, 0] := by
  decide +kernel

theorem rows8139 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8139 = true := by
  decide +kernel

theorem tot8139 : totK PD2M8K2 D2M8K2.t8139 = [0, 0, 92939194676, 425594575819, 345350278871, 37486711032, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
