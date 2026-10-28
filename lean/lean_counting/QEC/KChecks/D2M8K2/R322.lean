import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1288 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1288 = true := by
  decide +kernel

theorem tot1288 : totK PD2M8K2 D2M8K2.t1288 = [190336416222, 482499862016, 223921250782, 12523541424, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1289 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1289 = true := by
  decide +kernel

theorem tot1289 : totK PD2M8K2 D2M8K2.t1289 = [0, 292636859817, 496255305149, 103277626596, 1198073392, 0, 0, 0] := by
  decide +kernel

theorem rows1290 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1290 = true := by
  decide +kernel

theorem tot1290 : totK PD2M8K2 D2M8K2.t1290 = [0, 187889486319, 474728432370, 200037961956, 12052611869, 0, 0, 0] := by
  decide +kernel

theorem rows1291 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1291 = true := by
  decide +kernel

theorem tot1291 : totK PD2M8K2 D2M8K2.t1291 = [168980700029, 437457828465, 274643385062, 32369844838, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
