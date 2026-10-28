import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15928 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15928 = true := by
  decide +kernel

theorem tot15928 : totK PD2M8K2 D2M8K2.t15928 = [0, 114411566433, 434268862665, 327551194244, 29088687382, 0, 0, 0] := by
  decide +kernel

theorem rows15929 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15929 = true := by
  decide +kernel

theorem tot15929 : totK PD2M8K2 D2M8K2.t15929 = [0, 0, 199897173745, 489077279366, 189799255393, 9664716404, 0, 0] := by
  decide +kernel

theorem rows15930 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15930 = true := by
  decide +kernel

theorem tot15930 : totK PD2M8K2 D2M8K2.t15930 = [0, 86458299975, 343859986506, 362195846351, 95718465958, 3579068459, 0, 0] := by
  decide +kernel

theorem rows15931 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15931 = true := by
  decide +kernel

theorem tot15931 : totK PD2M8K2 D2M8K2.t15931 = [0, 174144596183, 449829151493, 274756262954, 28476205713, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
