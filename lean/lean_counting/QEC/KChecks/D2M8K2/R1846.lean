import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7384 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7384 = true := by
  decide +kernel

theorem tot7384 : totK PD2M8K2 D2M8K2.t7384 = [0, 198869836666, 460749101819, 245495422193, 23178887848, 0, 0, 0] := by
  decide +kernel

theorem rows7385 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7385 = true := by
  decide +kernel

theorem tot7385 : totK PD2M8K2 D2M8K2.t7385 = [0, 191422625772, 472330699211, 222676355166, 12523541424, 0, 0, 0] := by
  decide +kernel

theorem rows7386 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7386 = true := by
  decide +kernel

theorem tot7386 : totK PD2M8K2 D2M8K2.t7386 = [0, 0, 301171611761, 489575345289, 108020463030, 1198073392, 0, 0] := by
  decide +kernel

theorem rows7387 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7387 = true := by
  decide +kernel

theorem tot7387 : totK PD2M8K2 D2M8K2.t7387 = [0, 0, 204712689649, 467260057692, 189302537561, 12052611869, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
