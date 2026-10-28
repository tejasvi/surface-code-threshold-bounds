import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13188 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13188 = true := by
  decide +kernel

theorem tot13188 : totK PD2M8K2 D2M8K2.t13188 = [0, 212711231556, 498936464875, 177867781636, 5616011243, 0, 0, 0] := by
  decide +kernel

theorem rows13189 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13189 = true := by
  decide +kernel

theorem tot13189 : totK PD2M8K2 D2M8K2.t13189 = [0, 172283609800, 459496002364, 242282492397, 13787972337, 0, 0, 0] := by
  decide +kernel

theorem rows13190 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13190 = true := by
  decide +kernel

theorem tot13190 : totK PD2M8K2 D2M8K2.t13190 = [0, 0, 272368584523, 502118894073, 106329014915, 1369150432, 0, 0] := by
  decide +kernel

theorem rows13191 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13191 = true := by
  decide +kernel

theorem tot13191 : totK PD2M8K2 D2M8K2.t13191 = [0, 92635576531, 381068031067, 393958017991, 50210377413, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
