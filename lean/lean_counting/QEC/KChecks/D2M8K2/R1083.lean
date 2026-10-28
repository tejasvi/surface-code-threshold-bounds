import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4332 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4332 = true := by
  decide +kernel

theorem tot4332 : totK PD2M8K2 D2M8K2.t4332 = [0, 0, 0, 0, 322828090224, 483571163273, 71294782351, 0] := by
  decide +kernel

theorem rows4333 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4333 = true := by
  decide +kernel

theorem tot4333 : totK PD2M8K2 D2M8K2.t4333 = [0, 0, 233978599543, 451420361553, 119891422022, 55806749448, 39583725195, 1429815836] := by
  decide +kernel

theorem rows4334 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4334 = true := by
  decide +kernel

theorem tot4334 : totK PD2M8K2 D2M8K2.t4334 = [0, 0, 88786514364, 447284747605, 347493544166, 28059743675, 0, 0] := by
  decide +kernel

theorem rows4335 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4335 = true := by
  decide +kernel

theorem tot4335 : totK PD2M8K2 D2M8K2.t4335 = [0, 0, 93610018881, 385127110955, 394124507470, 55356358628, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
