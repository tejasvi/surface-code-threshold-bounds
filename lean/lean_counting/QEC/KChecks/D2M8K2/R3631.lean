import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14524 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14524 = true := by
  decide +kernel

theorem tot14524 : totK PD2M8K2 D2M8K2.t14524 = [0, 174878768978, 468502844226, 241065231825, 14962356622, 0, 0, 0] := by
  decide +kernel

theorem rows14525 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14525 = true := by
  decide +kernel

theorem tot14525 : totK PD2M8K2 D2M8K2.t14525 = [0, 0, 242970884391, 493757701194, 139237614762, 2318623666, 0, 0] := by
  decide +kernel

theorem rows14526 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14526 = true := by
  decide +kernel

theorem tot14526 : totK PD2M8K2 D2M8K2.t14526 = [0, 72042212179, 276703993215, 360407946744, 131560056102, 10786826731, 0, 0] := by
  decide +kernel

theorem rows14527 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14527 = true := by
  decide +kernel

theorem tot14527 : totK PD2M8K2 D2M8K2.t14527 = [0, 151051061993, 457718595600, 251469961118, 14539407580, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
