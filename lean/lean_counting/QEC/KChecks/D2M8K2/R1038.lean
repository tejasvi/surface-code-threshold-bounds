import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4152 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4152 = true := by
  decide +kernel

theorem tot4152 : totK PD2M8K2 D2M8K2.t4152 = [0, 0, 180071406952, 465972316039, 253335554971, 18246066036, 0, 0] := by
  decide +kernel

theorem rows4153 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4153 = true := by
  decide +kernel

theorem tot4153 : totK PD2M8K2 D2M8K2.t4153 = [0, 0, 215031688852, 481412650987, 194011175702, 6291577785, 0, 0] := by
  decide +kernel

theorem rows4154 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4154 = true := by
  decide +kernel

theorem tot4154 : totK PD2M8K2 D2M8K2.t4154 = [0, 0, 193483475576, 488461376717, 217225838532, 11066126582, 0, 0] := by
  decide +kernel

theorem rows4155 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4155 = true := by
  decide +kernel

theorem tot4155 : totK PD2M8K2 D2M8K2.t4155 = [0, 0, 156578928508, 461624281452, 263365864532, 14845323044, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
