import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8944 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8944 = true := by
  decide +kernel

theorem tot8944 : totK PD2M8K2 D2M8K2.t8944 = [198379150902, 473735221413, 201814245953, 9852138406, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8945 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8945 = true := by
  decide +kernel

theorem tot8945 : totK PD2M8K2 D2M8K2.t8945 = [167686836636, 461960517734, 245173427038, 13795945806, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8946 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8946 = true := by
  decide +kernel

theorem tot8946 : totK PD2M8K2 D2M8K2.t8946 = [0, 271428532848, 492608528627, 112859475277, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows8947 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8947 = true := by
  decide +kernel

theorem tot8947 : totK PD2M8K2 D2M8K2.t8947 = [92925902623, 376374085349, 392348380596, 53375909707, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
