import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6100 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6100 = true := by
  decide +kernel

theorem tot6100 : totK PD2M8K2 D2M8K2.t6100 = [0, 134351819522, 373684514608, 325468093945, 73063319732, 1189515370, 0, 0] := by
  decide +kernel

theorem rows6101 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6101 = true := by
  decide +kernel

theorem tot6101 : totK PD2M8K2 D2M8K2.t6101 = [0, 162376008722, 433165505197, 281299144906, 30328071326, 0, 0, 0] := by
  decide +kernel

theorem rows6102 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6102 = true := by
  decide +kernel

theorem tot6102 : totK PD2M8K2 D2M8K2.t6102 = [0, 88845658477, 370281732418, 373166536933, 73306313864, 1162515529, 0, 0] := by
  decide +kernel

theorem rows6103 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6103 = true := by
  decide +kernel

theorem tot6103 : totK PD2M8K2 D2M8K2.t6103 = [0, 0, 221897057541, 477109753313, 175359490551, 8017271805, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
