import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3004 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3004 = true := by
  decide +kernel

theorem tot3004 : totK PD2M8K2 D2M8K2.t3004 = [0, 64763393292, 272344168492, 397718999925, 140714001100, 5439011083, 0, 0] := by
  decide +kernel

theorem rows3005 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3005 = true := by
  decide +kernel

theorem tot3005 : totK PD2M8K2 D2M8K2.t3005 = [0, 176392400141, 453830159753, 263362117966, 24499106852, 0, 0, 0] := by
  decide +kernel

theorem rows3006 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3006 = true := by
  decide +kernel

theorem tot3006 : totK PD2M8K2 D2M8K2.t3006 = [0, 170108921497, 474859876653, 238805840324, 15781195759, 0, 0, 0] := by
  decide +kernel

theorem rows3007 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3007 = true := by
  decide +kernel

theorem tot3007 : totK PD2M8K2 D2M8K2.t3007 = [0, 0, 333266593760, 511925150071, 69188619365, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
