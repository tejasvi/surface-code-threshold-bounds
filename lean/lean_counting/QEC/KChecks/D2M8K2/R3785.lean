import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15140 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15140 = true := by
  decide +kernel

theorem tot15140 : totK PD2M8K2 D2M8K2.t15140 = [0, 195263139662, 464419838797, 245185019275, 21251455811, 0, 0, 0] := by
  decide +kernel

theorem rows15141 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15141 = true := by
  decide +kernel

theorem tot15141 : totK PD2M8K2 D2M8K2.t15141 = [0, 190671902078, 471438063500, 222982317873, 12523541424, 0, 0, 0] := by
  decide +kernel

theorem rows15142 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15142 = true := by
  decide +kernel

theorem tot15142 : totK PD2M8K2 D2M8K2.t15142 = [0, 19434652667, 308892529496, 470129354558, 100932172605, 1198073392, 0, 0] := by
  decide +kernel

theorem rows15143 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15143 = true := by
  decide +kernel

theorem tot15143 : totK PD2M8K2 D2M8K2.t15143 = [0, 0, 205661651786, 468693167103, 188853807214, 12052611869, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
