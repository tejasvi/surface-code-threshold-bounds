import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10472 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10472 = true := by
  decide +kernel

theorem tot10472 : totK PD2M8K2 D2M8K2.t10472 = [0, 0, 0, 58900643742, 360881547006, 347425426673, 54889839319, 1138244013] := by
  decide +kernel

theorem rows10473 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10473 = true := by
  decide +kernel

theorem tot10473 : totK PD2M8K2 D2M8K2.t10473 = [0, 0, 0, 118902716356, 430288593525, 304840983846, 25139995699, 0] := by
  decide +kernel

theorem rows10474 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10474 = true := by
  decide +kernel

theorem tot10474 : totK PD2M8K2 D2M8K2.t10474 = [0, 0, 0, 233796450580, 477731429773, 179470375904, 5868607260, 0] := by
  decide +kernel

theorem rows10475 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10475 = true := by
  decide +kernel

theorem tot10475 : totK PD2M8K2 D2M8K2.t10475 = [0, 0, 0, 320305502407, 473448924962, 79555120827, 1184435618, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
