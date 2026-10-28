import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7328 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7328 = true := by
  decide +kernel

theorem tot7328 : totK PD2M8K2 D2M8K2.t7328 = [0, 0, 0, 173377352853, 491933223468, 212031718868, 7658844075, 0] := by
  decide +kernel

theorem rows7329 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7329 = true := by
  decide +kernel

theorem tot7329 : totK PD2M8K2 D2M8K2.t7329 = [0, 0, 120817755924, 336530931526, 301089731823, 131559553663, 7877424857, 0] := by
  decide +kernel

theorem rows7330 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7330 = true := by
  decide +kernel

theorem tot7330 : totK PD2M8K2 D2M8K2.t7330 = [0, 0, 162272056024, 442096491757, 279958108626, 30347518258, 0, 0] := by
  decide +kernel

theorem rows7331 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7331 = true := by
  decide +kernel

theorem tot7331 : totK PD2M8K2 D2M8K2.t7331 = [0, 0, 138425588715, 442786091897, 288698001154, 18901662784, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
