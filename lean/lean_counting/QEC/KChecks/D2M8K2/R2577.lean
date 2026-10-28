import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10308 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10308 = true := by
  decide +kernel

theorem tot10308 : totK PD2M8K2 D2M8K2.t10308 = [0, 163690086331, 387561241653, 243894022966, 96103294124, 5355925179, 0, 0] := by
  decide +kernel

theorem rows10309 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10309 = true := by
  decide +kernel

theorem tot10309 : totK PD2M8K2 D2M8K2.t10309 = [0, 159843008701, 473622323890, 253585910374, 14891561056, 0, 0, 0] := by
  decide +kernel

theorem rows10310 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10310 = true := by
  decide +kernel

theorem tot10310 : totK PD2M8K2 D2M8K2.t10310 = [0, 0, 280272349520, 506662921210, 100194650799, 1164319620, 0, 0] := by
  decide +kernel

theorem rows10311 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10311 = true := by
  decide +kernel

theorem tot10311 : totK PD2M8K2 D2M8K2.t10311 = [0, 173099396876, 386179821009, 253144522164, 67845869708, 3462014130, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
