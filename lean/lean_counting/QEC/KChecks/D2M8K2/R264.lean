import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1056 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1056 = true := by
  decide +kernel

theorem tot1056 : totK PD2M8K2 D2M8K2.t1056 = [0, 193782683275, 480482630803, 215065340690, 11066126582, 0, 0, 0] := by
  decide +kernel

theorem rows1057 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1057 = true := by
  decide +kernel

theorem tot1057 : totK PD2M8K2 D2M8K2.t1057 = [0, 154370352667, 462219761623, 255284273701, 13597322258, 0, 0, 0] := by
  decide +kernel

theorem rows1058 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1058 = true := by
  decide +kernel

theorem tot1058 : totK PD2M8K2 D2M8K2.t1058 = [0, 173975553048, 462006024388, 243227065495, 18484640963, 0, 0, 0] := by
  decide +kernel

theorem rows1059 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1059 = true := by
  decide +kernel

theorem tot1059 : totK PD2M8K2 D2M8K2.t1059 = [0, 190032291817, 454577338241, 223975786379, 16702988424, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
