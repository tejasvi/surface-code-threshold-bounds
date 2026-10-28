import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11832 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11832 = true := by
  decide +kernel

theorem tot11832 : totK PD2M8K2 D2M8K2.t11832 = [0, 111279211669, 439173240010, 316285957588, 27539121806, 0, 0, 0] := by
  decide +kernel

theorem rows11833 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11833 = true := by
  decide +kernel

theorem tot11833 : totK PD2M8K2 D2M8K2.t11833 = [0, 0, 293696975309, 522801610246, 95622383492, 1096505104, 0, 0] := by
  decide +kernel

theorem rows11834 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11834 = true := by
  decide +kernel

theorem tot11834 : totK PD2M8K2 D2M8K2.t11834 = [0, 0, 206217694967, 492913477329, 177012558315, 5253830308, 0, 0] := by
  decide +kernel

theorem rows11835 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11835 = true := by
  decide +kernel

theorem tot11835 : totK PD2M8K2 D2M8K2.t11835 = [0, 0, 182066631306, 472457672141, 188941405243, 10545640975, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
