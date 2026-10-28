import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5296 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5296 = true := by
  decide +kernel

theorem tot5296 : totK PD2M8K2 D2M8K2.t5296 = [0, 0, 0, 306941993559, 465535590389, 80390858867, 1206465782, 0] := by
  decide +kernel

theorem rows5297 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5297 = true := by
  decide +kernel

theorem tot5297 : totK PD2M8K2 D2M8K2.t5297 = [0, 0, 118886349465, 400479416973, 356630314125, 41260980931, 0, 0] := by
  decide +kernel

theorem rows5298 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5298 = true := by
  decide +kernel

theorem tot5298 : totK PD2M8K2 D2M8K2.t5298 = [0, 0, 208938962855, 486912143182, 214305398142, 11153422415, 0, 0] := by
  decide +kernel

theorem rows5299 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5299 = true := by
  decide +kernel

theorem tot5299 : totK PD2M8K2 D2M8K2.t5299 = [0, 0, 172046126118, 470156862360, 235653202409, 15381949982, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
