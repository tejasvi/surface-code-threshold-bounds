import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14124 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14124 = true := by
  decide +kernel

theorem tot14124 : totK PD2M8K2 D2M8K2.t14124 = [87704378323, 395630975905, 380590853493, 43220078729, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14125 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14125 = true := by
  decide +kernel

theorem tot14125 : totK PD2M8K2 D2M8K2.t14125 = [172133193736, 444775321511, 266104198928, 27374447968, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14126 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14126 = true := by
  decide +kernel

theorem tot14126 : totK PD2M8K2 D2M8K2.t14126 = [160040357605, 451871284106, 258305850074, 18887441571, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14127 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14127 = true := by
  decide +kernel

theorem tot14127 : totK PD2M8K2 D2M8K2.t14127 = [0, 231173088603, 496243850553, 159951239681, 7166294683, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
