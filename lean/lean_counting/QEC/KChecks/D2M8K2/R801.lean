import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3204 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3204 = true := by
  decide +kernel

theorem tot3204 : totK PD2M8K2 D2M8K2.t3204 = [18192396302, 296167306241, 463830672058, 101605977654, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows3205 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3205 = true := by
  decide +kernel

theorem tot3205 : totK PD2M8K2 D2M8K2.t3205 = [92925902623, 376215700986, 392885597669, 54424790802, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3206 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3206 = true := by
  decide +kernel

theorem tot3206 : totK PD2M8K2 D2M8K2.t3206 = [167775465357, 449778985262, 267641885790, 21074251253, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3207 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3207 = true := by
  decide +kernel

theorem tot3207 : totK PD2M8K2 D2M8K2.t3207 = [158964227490, 464926718032, 273236278887, 27867321612, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
