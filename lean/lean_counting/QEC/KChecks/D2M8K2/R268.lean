import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1072 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1072 = true := by
  decide +kernel

theorem tot1072 : totK PD2M8K2 D2M8K2.t1072 = [0, 0, 271611267678, 512518125835, 106739661214, 1198073392, 0, 0] := by
  decide +kernel

theorem rows1073 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1073 = true := by
  decide +kernel

theorem tot1073 : totK PD2M8K2 D2M8K2.t1073 = [0, 54618809271, 227456167610, 410214362949, 165912662944, 11986244008, 0, 0] := by
  decide +kernel

theorem rows1074 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1074 = true := by
  decide +kernel

theorem tot1074 : totK PD2M8K2 D2M8K2.t1074 = [0, 189448271826, 466752749698, 225609838706, 16192212756, 0, 0, 0] := by
  decide +kernel

theorem rows1075 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1075 = true := by
  decide +kernel

theorem tot1075 : totK PD2M8K2 D2M8K2.t1075 = [0, 177086745037, 455418607044, 239636553086, 17104814242, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
