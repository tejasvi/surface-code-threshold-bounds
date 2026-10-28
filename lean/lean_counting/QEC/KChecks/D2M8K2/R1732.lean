import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6928 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6928 = true := by
  decide +kernel

theorem tot6928 : totK PD2M8K2 D2M8K2.t6928 = [0, 0, 204861342978, 489775221997, 172561298562, 3630826045, 0, 0] := by
  decide +kernel

theorem rows6929 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6929 = true := by
  decide +kernel

theorem tot6929 : totK PD2M8K2 D2M8K2.t6929 = [0, 0, 169980131769, 465540549856, 230198713962, 10816184264, 0, 0] := by
  decide +kernel

theorem rows6930 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6930 = true := by
  decide +kernel

theorem tot6930 : totK PD2M8K2 D2M8K2.t6930 = [0, 15960351544, 177544335288, 446679861995, 235877312445, 17376665387, 0, 0] := by
  decide +kernel

theorem rows6931 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6931 = true := by
  decide +kernel

theorem tot6931 : totK PD2M8K2 D2M8K2.t6931 = [0, 162581909437, 448322513644, 282003632429, 29995732368, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
