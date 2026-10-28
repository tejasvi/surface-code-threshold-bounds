import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9252 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9252 = true := by
  decide +kernel

theorem tot9252 : totK PD2M8K2 D2M8K2.t9252 = [57740418758, 84449106946, 232695697899, 386890429509, 93166853631, 3552795014, 0, 0] := by
  decide +kernel

theorem rows9253 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9253 = true := by
  decide +kernel

theorem tot9253 : totK PD2M8K2 D2M8K2.t9253 = [182349689255, 472041799219, 217108256238, 11034354488, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9254 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9254 = true := by
  decide +kernel

theorem tot9254 : totK PD2M8K2 D2M8K2.t9254 = [164210109155, 463638396776, 248609957789, 15069461764, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9255 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9255 = true := by
  decide +kernel

theorem tot9255 : totK PD2M8K2 D2M8K2.t9255 = [0, 269429643394, 498163104276, 115462232409, 1369150432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
