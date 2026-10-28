import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8884 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8884 = true := by
  decide +kernel

theorem tot8884 : totK PD2M8K2 D2M8K2.t8884 = [179724476225, 468183101042, 246488138410, 16383212755, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8885 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8885 = true := by
  decide +kernel

theorem tot8885 : totK PD2M8K2 D2M8K2.t8885 = [0, 288013628759, 499276672198, 117096062464, 1267860612, 0, 0, 0] := by
  decide +kernel

theorem rows8886 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8886 = true := by
  decide +kernel

theorem tot8886 : totK PD2M8K2 D2M8K2.t8886 = [0, 182994377864, 481546495197, 204458547318, 8505135016, 0, 0, 0] := by
  decide +kernel

theorem rows8887 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8887 = true := by
  decide +kernel

theorem tot8887 : totK PD2M8K2 D2M8K2.t8887 = [0, 178156049487, 435156685080, 274373828691, 34167921589, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
