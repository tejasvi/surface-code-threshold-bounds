import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6152 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6152 = true := by
  decide +kernel

theorem tot6152 : totK PA10K2 A10K2.t6152 = [0, 0, 113566876963, 769742721834, 1899822054575, 1553045045544, 313591536099, 10760911071, 0, 0] := by
  decide +kernel

theorem rows6153 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6153 = true := by
  decide +kernel

theorem tot6153 : totK PA10K2 A10K2.t6153 = [0, 0, 495706338982, 1743970320666, 1772603811660, 478718240652, 31235808944, 0, 0, 0] := by
  decide +kernel

theorem rows6154 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6154 = true := by
  decide +kernel

theorem tot6154 : totK PA10K2 A10K2.t6154 = [0, 0, 71150330834, 1106947268207, 2219092126073, 979357749269, 76853360318, 0, 0, 0] := by
  decide +kernel

theorem rows6155 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6155 = true := by
  decide +kernel

theorem tot6155 : totK PA10K2 A10K2.t6155 = [0, 0, 473786384371, 1488736624418, 1787508286850, 905810070684, 154481227852, 5705019915, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
