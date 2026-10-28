import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10540 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10540 = true := by
  decide +kernel

theorem tot10540 : totK PD2M8K2 D2M8K2.t10540 = [0, 166907483503, 465938713594, 256568066122, 18356672802, 0, 0, 0] := by
  decide +kernel

theorem rows10541 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10541 = true := by
  decide +kernel

theorem tot10541 : totK PD2M8K2 D2M8K2.t10541 = [0, 0, 230141414580, 498464549360, 165038305854, 7229436959, 0, 0] := by
  decide +kernel

theorem rows10542 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10542 = true := by
  decide +kernel

theorem tot10542 : totK PD2M8K2 D2M8K2.t10542 = [0, 69879160141, 284203807104, 391992914388, 129645294462, 6008233017, 0, 0] := by
  decide +kernel

theorem rows10543 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10543 = true := by
  decide +kernel

theorem tot10543 : totK PD2M8K2 D2M8K2.t10543 = [0, 174614809441, 448895971954, 265501777671, 24556113835, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
