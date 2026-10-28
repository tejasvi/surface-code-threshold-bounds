import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1600 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1600 = true := by
  decide +kernel

theorem tot1600 : totK PD2M8K2 D2M8K2.t1600 = [0, 0, 84175368157, 315184229307, 361730389674, 89236921704, 3472187823, 0] := by
  decide +kernel

theorem rows1601 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1601 = true := by
  decide +kernel

theorem tot1601 : totK PD2M8K2 D2M8K2.t1601 = [0, 0, 180070635327, 475777963394, 201304120776, 7752365546, 0, 0] := by
  decide +kernel

theorem rows1602 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1602 = true := by
  decide +kernel

theorem tot1602 : totK PD2M8K2 D2M8K2.t1602 = [0, 0, 143123251625, 459397601099, 269875948744, 14924766657, 0, 0] := by
  decide +kernel

theorem rows1603 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1603 = true := by
  decide +kernel

theorem tot1603 : totK PD2M8K2 D2M8K2.t1603 = [0, 0, 0, 303525170141, 456684921794, 74665361765, 1053411165, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
