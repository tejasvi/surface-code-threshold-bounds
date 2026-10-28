import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14332 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14332 = true := by
  decide +kernel

theorem tot14332 : totK PD2M8K2 D2M8K2.t14332 = [0, 177723450739, 439672542647, 277768991141, 35245646968, 0, 0, 0] := by
  decide +kernel

theorem rows14333 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14333 = true := by
  decide +kernel

theorem tot14333 : totK PD2M8K2 D2M8K2.t14333 = [0, 153719786022, 452938976088, 288489349115, 29648602324, 0, 0, 0] := by
  decide +kernel

theorem rows14334 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14334 = true := by
  decide +kernel

theorem tot14334 : totK PD2M8K2 D2M8K2.t14334 = [0, 0, 232321045473, 497372565436, 158609890047, 5439011083, 0, 0] := by
  decide +kernel

theorem rows14335 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14335 = true := by
  decide +kernel

theorem tot14335 : totK PD2M8K2 D2M8K2.t14335 = [0, 140943570440, 421523941177, 315272644167, 43056159370, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
