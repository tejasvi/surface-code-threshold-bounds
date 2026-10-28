import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1040 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1040 = true := by
  decide +kernel

theorem tot1040 : totK PD2M8K2 D2M8K2.t1040 = [177993988983, 458173556347, 250154205594, 22314117634, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1041 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1041 = true := by
  decide +kernel

theorem tot1041 : totK PD2M8K2 D2M8K2.t1041 = [155164265377, 463140211636, 262407293265, 16525034018, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1042 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1042 = true := by
  decide +kernel

theorem tot1042 : totK PD2M8K2 D2M8K2.t1042 = [0, 260184823658, 501366530181, 122420364457, 1198073392, 0, 0, 0] := by
  decide +kernel

theorem rows1043 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1043 = true := by
  decide +kernel

theorem tot1043 : totK PD2M8K2 D2M8K2.t1043 = [54502128254, 230984742191, 401519576583, 180574931482, 12052611869, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
