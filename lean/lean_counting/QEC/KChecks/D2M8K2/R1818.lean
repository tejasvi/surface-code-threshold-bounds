import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7272 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7272 = true := by
  decide +kernel

theorem tot7272 : totK PD2M8K2 D2M8K2.t7272 = [0, 0, 123153304415, 420416674973, 304364876858, 26092683800, 0, 0] := by
  decide +kernel

theorem rows7273 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7273 = true := by
  decide +kernel

theorem tot7273 : totK PD2M8K2 D2M8K2.t7273 = [0, 0, 0, 280393228027, 495136272931, 101721330800, 1369150432, 0] := by
  decide +kernel

theorem rows7274 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7274 = true := by
  decide +kernel

theorem tot7274 : totK PD2M8K2 D2M8K2.t7274 = [0, 0, 172607797586, 446383294272, 277495778327, 21911296632, 0, 0] := by
  decide +kernel

theorem rows7275 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7275 = true := by
  decide +kernel

theorem tot7275 : totK PD2M8K2 D2M8K2.t7275 = [0, 0, 155296912568, 468601882166, 255716673848, 17676788847, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
