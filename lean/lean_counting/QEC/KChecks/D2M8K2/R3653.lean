import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14612 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14612 = true := by
  decide +kernel

theorem tot14612 : totK PD2M8K2 D2M8K2.t14612 = [0, 87415767316, 315430046521, 381343447974, 100385059919, 3821179711, 0, 0] := by
  decide +kernel

theorem rows14613 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14613 = true := by
  decide +kernel

theorem tot14613 : totK PD2M8K2 D2M8K2.t14613 = [0, 159704940053, 457024800528, 267872742016, 22456801898, 0, 0, 0] := by
  decide +kernel

theorem rows14614 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14614 = true := by
  decide +kernel

theorem tot14614 : totK PD2M8K2 D2M8K2.t14614 = [0, 169143655275, 458303654485, 261257791320, 22160825840, 0, 0, 0] := by
  decide +kernel

theorem rows14615 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14615 = true := by
  decide +kernel

theorem tot14615 : totK PD2M8K2 D2M8K2.t14615 = [0, 0, 273426933886, 507368541457, 115664763833, 1268739303, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
