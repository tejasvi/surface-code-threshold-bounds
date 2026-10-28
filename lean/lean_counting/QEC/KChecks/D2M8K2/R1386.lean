import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5544 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5544 = true := by
  decide +kernel

theorem tot5544 : totK PD2M8K2 D2M8K2.t5544 = [0, 172660554935, 456137553575, 256480629687, 25223755281, 0, 0, 0] := by
  decide +kernel

theorem rows5545 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5545 = true := by
  decide +kernel

theorem tot5545 : totK PD2M8K2 D2M8K2.t5545 = [57586079575, 231789558762, 415253389088, 191216964217, 8094277083, 0, 0, 0] := by
  decide +kernel

theorem rows5546 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5546 = true := by
  decide +kernel

theorem tot5546 : totK PD2M8K2 D2M8K2.t5546 = [185547573039, 476540606066, 247292846766, 21488144658, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5547 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5547 = true := by
  decide +kernel

theorem tot5547 : totK PD2M8K2 D2M8K2.t5547 = [193959156159, 475280888844, 223743678105, 12373752831, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
