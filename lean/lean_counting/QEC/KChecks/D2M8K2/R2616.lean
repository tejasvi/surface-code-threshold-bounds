import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10464 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10464 = true := by
  decide +kernel

theorem tot10464 : totK PD2M8K2 D2M8K2.t10464 = [0, 0, 71500428704, 319025460987, 404634785703, 89319831625, 1198073392, 0] := by
  decide +kernel

theorem rows10465 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10465 = true := by
  decide +kernel

theorem tot10465 : totK PD2M8K2 D2M8K2.t10465 = [0, 0, 0, 213451967146, 486809057311, 174405137257, 9482920370, 0] := by
  decide +kernel

theorem rows10466 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10466 = true := by
  decide +kernel

theorem tot10466 : totK PD2M8K2 D2M8K2.t10466 = [0, 0, 173802357275, 443580823769, 238799783750, 42136969919, 2569691499, 0] := by
  decide +kernel

theorem rows10467 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10467 = true := by
  decide +kernel

theorem tot10467 : totK PD2M8K2 D2M8K2.t10467 = [0, 0, 170504954424, 431675415497, 266721853706, 23402992943, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
