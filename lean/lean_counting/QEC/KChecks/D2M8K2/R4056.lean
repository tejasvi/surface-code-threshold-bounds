import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16224 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16224 = true := by
  decide +kernel

theorem tot16224 : totK PD2M8K2 D2M8K2.t16224 = [0, 0, 212326855199, 498088193832, 205546860610, 6422285974, 0, 0] := by
  decide +kernel

theorem rows16225 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16225 = true := by
  decide +kernel

theorem tot16225 : totK PD2M8K2 D2M8K2.t16225 = [0, 0, 172248240994, 458443673847, 248545542044, 24612453605, 0, 0] := by
  decide +kernel

theorem rows16226 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16226 = true := by
  decide +kernel

theorem tot16226 : totK PD2M8K2 D2M8K2.t16226 = [0, 0, 158267468247, 444687899770, 266522405487, 18539915812, 0, 0] := by
  decide +kernel

theorem rows16227 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16227 = true := by
  decide +kernel

theorem tot16227 : totK PD2M8K2 D2M8K2.t16227 = [0, 0, 89481634255, 345742641785, 383025348384, 67079339717, 1075657031, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
