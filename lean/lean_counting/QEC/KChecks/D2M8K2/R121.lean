import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows484 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t484 = true := by
  decide +kernel

theorem tot484 : totK PD2M8K2 D2M8K2.t484 = [0, 93978096042, 319742732838, 367932845718, 135275102863, 8859721110, 0, 0] := by
  decide +kernel

theorem rows485 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t485 = true := by
  decide +kernel

theorem tot485 : totK PD2M8K2 D2M8K2.t485 = [0, 162246501886, 456278630102, 283558503015, 22319531278, 0, 0, 0] := by
  decide +kernel

theorem rows486 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t486 = true := by
  decide +kernel

theorem tot486 : totK PD2M8K2 D2M8K2.t486 = [0, 173852723837, 461470511903, 243621292799, 13641067407, 0, 0, 0] := by
  decide +kernel

theorem rows487 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t487 = true := by
  decide +kernel

theorem tot487 : totK PD2M8K2 D2M8K2.t487 = [0, 0, 201214437242, 460628022720, 235967890203, 23166508062, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
