import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14976 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14976 = true := by
  decide +kernel

theorem tot14976 : totK PD2M8K2 D2M8K2.t14976 = [0, 172418535940, 475655463680, 252069016893, 13556425441, 0, 0, 0] := by
  decide +kernel

theorem rows14977 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14977 = true := by
  decide +kernel

theorem tot14977 : totK PD2M8K2 D2M8K2.t14977 = [0, 71815945053, 344783507379, 381074861246, 70506364828, 1062926506, 0, 0] := by
  decide +kernel

theorem rows14978 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14978 = true := by
  decide +kernel

theorem tot14978 : totK PD2M8K2 D2M8K2.t14978 = [0, 84824948312, 316747535280, 384633282340, 93990218143, 3720136285, 0, 0] := by
  decide +kernel

theorem rows14979 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14979 = true := by
  decide +kernel

theorem tot14979 : totK PD2M8K2 D2M8K2.t14979 = [0, 177936335313, 465877348084, 256374328338, 22739313779, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
