import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11536 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11536 = true := by
  decide +kernel

theorem tot11536 : totK PD2M8K2 D2M8K2.t11536 = [0, 0, 216337054222, 479184886567, 172759667991, 7938575017, 0, 0] := by
  decide +kernel

theorem rows11537 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11537 = true := by
  decide +kernel

theorem tot11537 : totK PD2M8K2 D2M8K2.t11537 = [0, 156180567191, 437782454030, 292549595552, 39195961150, 0, 0, 0] := by
  decide +kernel

theorem rows11538 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11538 = true := by
  decide +kernel

theorem tot11538 : totK PD2M8K2 D2M8K2.t11538 = [0, 175658625522, 451174355073, 250462564593, 18357554413, 0, 0, 0] := by
  decide +kernel

theorem rows11539 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11539 = true := by
  decide +kernel

theorem tot11539 : totK PD2M8K2 D2M8K2.t11539 = [0, 71878583259, 347520420514, 398475012482, 87217601436, 1162515529, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
