import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9388 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9388 = true := by
  decide +kernel

theorem tot9388 : totK PD2M8K2 D2M8K2.t9388 = [0, 192306165371, 479457686244, 223688818082, 12534051746, 0, 0, 0] := by
  decide +kernel

theorem rows9389 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9389 = true := by
  decide +kernel

theorem tot9389 : totK PD2M8K2 D2M8K2.t9389 = [0, 49201925218, 310288726733, 419718743216, 86075082919, 1310517177, 0, 0] := by
  decide +kernel

theorem rows9390 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9390 = true := by
  decide +kernel

theorem tot9390 : totK PD2M8K2 D2M8K2.t9390 = [0, 92870497502, 375793556014, 408165855231, 44005989047, 0, 0, 0] := by
  decide +kernel

theorem rows9391 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9391 = true := by
  decide +kernel

theorem tot9391 : totK PD2M8K2 D2M8K2.t9391 = [0, 157432360224, 450950129744, 288100052267, 28252641472, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
