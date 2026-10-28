import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8172 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8172 = true := by
  decide +kernel

theorem tot8172 : totK PD2M8K2 D2M8K2.t8172 = [0, 0, 194776440659, 470948227425, 216512250082, 12900833004, 0, 0] := by
  decide +kernel

theorem rows8173 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8173 = true := by
  decide +kernel

theorem tot8173 : totK PD2M8K2 D2M8K2.t8173 = [0, 0, 175275824996, 443499256784, 269657857784, 26123542864, 0, 0] := by
  decide +kernel

theorem rows8174 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8174 = true := by
  decide +kernel

theorem tot8174 : totK PD2M8K2 D2M8K2.t8174 = [0, 0, 107070054535, 421503778305, 322397804484, 28152892144, 0, 0] := by
  decide +kernel

theorem rows8175 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8175 = true := by
  decide +kernel

theorem tot8175 : totK PD2M8K2 D2M8K2.t8175 = [0, 0, 0, 260193092489, 472934149528, 139352549248, 5425831197, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
