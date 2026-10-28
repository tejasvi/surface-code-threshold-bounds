import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5616 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5616 = true := by
  decide +kernel

theorem tot5616 : totK PD2M8K2 D2M8K2.t5616 = [140433394095, 441536538228, 289423491655, 23872819054, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5617 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5617 = true := by
  decide +kernel

theorem tot5617 : totK PD2M8K2 D2M8K2.t5617 = [0, 194191395369, 476047183993, 187416465405, 9668735432, 0, 0, 0] := by
  decide +kernel

theorem rows5618 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5618 = true := by
  decide +kernel

theorem tot5618 : totK PD2M8K2 D2M8K2.t5618 = [102556995953, 340438471194, 346253017324, 91320659145, 3581949829, 0, 0, 0] := by
  decide +kernel

theorem rows5619 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5619 = true := by
  decide +kernel

theorem tot5619 : totK PD2M8K2 D2M8K2.t5619 = [168754580085, 437214248515, 270842534153, 28078561287, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
