import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6104 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6104 = true := by
  decide +kernel

theorem tot6104 : totK PD2M8K2 D2M8K2.t6104 = [0, 172672358213, 448525462799, 268678171891, 37759535903, 0, 0, 0] := by
  decide +kernel

theorem rows6105 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6105 = true := by
  decide +kernel

theorem tot6105 : totK PD2M8K2 D2M8K2.t6105 = [0, 174320997028, 445007124158, 263845224174, 20425878116, 0, 0, 0] := by
  decide +kernel

theorem rows6106 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6106 = true := by
  decide +kernel

theorem tot6106 : totK PD2M8K2 D2M8K2.t6106 = [0, 93768764846, 391510658139, 360853438184, 59067752983, 1249641317, 0, 0] := by
  decide +kernel

theorem rows6107 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6107 = true := by
  decide +kernel

theorem tot6107 : totK PD2M8K2 D2M8K2.t6107 = [0, 0, 231410585145, 499655732783, 159209065657, 3660139582, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
