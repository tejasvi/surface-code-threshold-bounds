import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1536 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1536 = true := by
  decide +kernel

theorem tot1536 : totK PD2M8K2 D2M8K2.t1536 = [0, 64832901093, 211906693706, 384041511685, 224280345697, 17433533548, 0, 0] := by
  decide +kernel

theorem rows1537 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1537 = true := by
  decide +kernel

theorem tot1537 : totK PD2M8K2 D2M8K2.t1537 = [0, 182236284650, 495059275889, 217353451484, 9852138406, 0, 0, 0] := by
  decide +kernel

theorem rows1538 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1538 = true := by
  decide +kernel

theorem tot1538 : totK PD2M8K2 D2M8K2.t1538 = [0, 171699112667, 457111749955, 245731603674, 14848442203, 0, 0, 0] := by
  decide +kernel

theorem rows1539 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1539 = true := by
  decide +kernel

theorem tot1539 : totK PD2M8K2 D2M8K2.t1539 = [0, 0, 278619097311, 500289760337, 112226421103, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
