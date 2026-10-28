import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8564 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8564 = true := by
  decide +kernel

theorem tot8564 : totK PD2M8K2 D2M8K2.t8564 = [162263604823, 447851454785, 282312595883, 23870560419, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8565 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8565 = true := by
  decide +kernel

theorem tot8565 : totK PD2M8K2 D2M8K2.t8565 = [174706502236, 467738890430, 248084684787, 17102514199, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8566 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8566 = true := by
  decide +kernel

theorem tot8566 : totK PD2M8K2 D2M8K2.t8566 = [0, 180141548772, 444411074445, 256637885816, 25364689049, 0, 0, 0] := by
  decide +kernel

theorem rows8567 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8567 = true := by
  decide +kernel

theorem tot8567 : totK PD2M8K2 D2M8K2.t8567 = [0, 203885776303, 493512061420, 198063501562, 5430665091, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
