import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1580 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1580 = true := by
  decide +kernel

theorem tot1580 : totK PD2M8K2 D2M8K2.t1580 = [0, 194016927859, 477853888531, 226377775862, 12523541424, 0, 0, 0] := by
  decide +kernel

theorem rows1581 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1581 = true := by
  decide +kernel

theorem tot1581 : totK PD2M8K2 D2M8K2.t1581 = [0, 0, 296923817369, 494694071436, 101663165099, 1198073392, 0, 0] := by
  decide +kernel

theorem rows1582 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1582 = true := by
  decide +kernel

theorem tot1582 : totK PD2M8K2 D2M8K2.t1582 = [0, 0, 195651305861, 471249341836, 198953851589, 12052611869, 0, 0] := by
  decide +kernel

theorem rows1583 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1583 = true := by
  decide +kernel

theorem tot1583 : totK PD2M8K2 D2M8K2.t1583 = [0, 162822319824, 434289699958, 262524601260, 31489855617, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
