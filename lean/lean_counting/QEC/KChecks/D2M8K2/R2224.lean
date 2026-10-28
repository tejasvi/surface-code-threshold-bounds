import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8896 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8896 = true := by
  decide +kernel

theorem tot8896 : totK PD2M8K2 D2M8K2.t8896 = [0, 193776490591, 462928093971, 227949501465, 15697450534, 0, 0, 0] := by
  decide +kernel

theorem rows8897 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8897 = true := by
  decide +kernel

theorem tot8897 : totK PD2M8K2 D2M8K2.t8897 = [0, 71212928085, 404293669864, 390264868214, 47059465908, 0, 0, 0] := by
  decide +kernel

theorem rows8898 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8898 = true := by
  decide +kernel

theorem tot8898 : totK PD2M8K2 D2M8K2.t8898 = [0, 0, 222621866857, 488712244948, 161457232928, 5218872685, 0, 0] := by
  decide +kernel

theorem rows8899 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8899 = true := by
  decide +kernel

theorem tot8899 : totK PD2M8K2 D2M8K2.t8899 = [0, 186604081136, 439182695497, 250873186723, 29793696015, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
