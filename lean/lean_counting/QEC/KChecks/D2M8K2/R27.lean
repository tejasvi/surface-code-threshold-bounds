import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows108 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t108 = true := by
  decide +kernel

theorem tot108 : totK PD2M8K2 D2M8K2.t108 = [164881106172, 445086079548, 267569650263, 21620926349, 0, 0, 0, 0] := by
  decide +kernel

theorem rows109 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t109 = true := by
  decide +kernel

theorem tot109 : totK PD2M8K2 D2M8K2.t109 = [87930784875, 335385831694, 330627600613, 135172632779, 17131709587, 0, 0, 0] := by
  decide +kernel

theorem rows110 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t110 = true := by
  decide +kernel

theorem tot110 : totK PD2M8K2 D2M8K2.t110 = [0, 205715399153, 474242651570, 204272296374, 7994456143, 0, 0, 0] := by
  decide +kernel

theorem rows111 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t111 = true := by
  decide +kernel

theorem tot111 : totK PD2M8K2 D2M8K2.t111 = [163400894771, 381528548668, 270532259300, 77257722722, 1409560813, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
