import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10212 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10212 = true := by
  decide +kernel

theorem tot10212 : totK PD2M8K2 D2M8K2.t10212 = [0, 0, 186593726651, 467693960987, 204406156561, 11934039657, 0, 0] := by
  decide +kernel

theorem rows10213 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10213 = true := by
  decide +kernel

theorem tot10213 : totK PD2M8K2 D2M8K2.t10213 = [0, 0, 152307593598, 447257958809, 254206648606, 17876681237, 0, 0] := by
  decide +kernel

theorem rows10214 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10214 = true := by
  decide +kernel

theorem tot10214 : totK PD2M8K2 D2M8K2.t10214 = [0, 0, 0, 284256295986, 458487933187, 98101729240, 1369150432, 0] := by
  decide +kernel

theorem rows10215 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10215 = true := by
  decide +kernel

theorem tot10215 : totK PD2M8K2 D2M8K2.t10215 = [0, 0, 157887881646, 452069150307, 256700373201, 17215838196, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
