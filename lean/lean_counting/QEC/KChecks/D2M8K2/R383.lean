import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1532 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1532 = true := by
  decide +kernel

theorem tot1532 : totK PD2M8K2 D2M8K2.t1532 = [0, 0, 177728464871, 488565270300, 215205323834, 10178307621, 0, 0] := by
  decide +kernel

theorem rows1533 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1533 = true := by
  decide +kernel

theorem tot1533 : totK PD2M8K2 D2M8K2.t1533 = [0, 0, 171545747030, 454609685678, 224810976921, 15723602574, 0, 0] := by
  decide +kernel

theorem rows1534 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1534 = true := by
  decide +kernel

theorem tot1534 : totK PD2M8K2 D2M8K2.t1534 = [0, 0, 194117219353, 487339122728, 207507191857, 7807117139, 0, 0] := by
  decide +kernel

theorem rows1535 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1535 = true := by
  decide +kernel

theorem tot1535 : totK PD2M8K2 D2M8K2.t1535 = [0, 0, 193530037044, 465917171029, 212254932778, 10929898537, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
