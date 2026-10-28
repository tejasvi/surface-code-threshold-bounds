import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7828 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7828 = true := by
  decide +kernel

theorem tot7828 : totK PD2M8K2 D2M8K2.t7828 = [0, 158212545565, 462430834311, 283920947950, 27331646493, 0, 0, 0] := by
  decide +kernel

theorem rows7829 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7829 = true := by
  decide +kernel

theorem tot7829 : totK PD2M8K2 D2M8K2.t7829 = [0, 0, 231770175653, 510136612858, 158352001674, 4050001513, 0, 0] := by
  decide +kernel

theorem rows7830 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7830 = true := by
  decide +kernel

theorem tot7830 : totK PD2M8K2 D2M8K2.t7830 = [0, 0, 153155228561, 436827848449, 292034313637, 31799082203, 0, 0] := by
  decide +kernel

theorem rows7831 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7831 = true := by
  decide +kernel

theorem tot7831 : totK PD2M8K2 D2M8K2.t7831 = [0, 0, 192221513852, 466157576273, 229710229335, 15051565756, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
