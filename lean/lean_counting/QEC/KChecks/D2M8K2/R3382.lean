import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13528 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13528 = true := by
  decide +kernel

theorem tot13528 : totK PD2M8K2 D2M8K2.t13528 = [0, 183461092008, 460527007946, 215215195639, 12243442891, 0, 0, 0] := by
  decide +kernel

theorem rows13529 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13529 = true := by
  decide +kernel

theorem tot13529 : totK PD2M8K2 D2M8K2.t13529 = [0, 202301000768, 478456307005, 209828514257, 10177609099, 0, 0, 0] := by
  decide +kernel

theorem rows13530 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13530 = true := by
  decide +kernel

theorem tot13530 : totK PD2M8K2 D2M8K2.t13530 = [0, 178812348239, 464719492912, 229968844763, 12679943201, 0, 0, 0] := by
  decide +kernel

theorem rows13531 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13531 = true := by
  decide +kernel

theorem tot13531 : totK PD2M8K2 D2M8K2.t13531 = [0, 174270531570, 464177374442, 235061373913, 12886908819, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
