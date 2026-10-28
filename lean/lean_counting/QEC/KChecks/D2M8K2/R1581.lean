import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6324 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6324 = true := by
  decide +kernel

theorem tot6324 : totK PD2M8K2 D2M8K2.t6324 = [0, 0, 72120773498, 404705876270, 337059095598, 33594265350, 0, 0] := by
  decide +kernel

theorem rows6325 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6325 = true := by
  decide +kernel

theorem tot6325 : totK PD2M8K2 D2M8K2.t6325 = [0, 0, 175279026168, 494279060895, 219828937271, 6614204793, 0, 0] := by
  decide +kernel

theorem rows6326 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6326 = true := by
  decide +kernel

theorem tot6326 : totK PD2M8K2 D2M8K2.t6326 = [0, 0, 170607923356, 457320208997, 220899339867, 13649623890, 0, 0] := by
  decide +kernel

theorem rows6327 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6327 = true := by
  decide +kernel

theorem tot6327 : totK PD2M8K2 D2M8K2.t6327 = [0, 0, 236142734968, 474245951998, 144867619729, 7350263764, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
