import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows892 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t892 = true := by
  decide +kernel

theorem tot892 : totK PD2M8K2 D2M8K2.t892 = [0, 0, 181091003179, 478866865228, 219842951674, 10003724324, 0, 0] := by
  decide +kernel

theorem rows893 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t893 = true := by
  decide +kernel

theorem tot893 : totK PD2M8K2 D2M8K2.t893 = [196979962980, 472052670349, 202765909825, 9852138406, 13653922804, 7077058802, 0, 0] := by
  decide +kernel

theorem rows894 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t894 = true := by
  decide +kernel

theorem tot894 : totK PD2M8K2 D2M8K2.t894 = [196342636656, 473220660151, 221170724367, 12534051746, 0, 0, 0, 0] := by
  decide +kernel

theorem rows895 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t895 = true := by
  decide +kernel

theorem tot895 : totK PD2M8K2 D2M8K2.t895 = [43868459350, 317957508010, 436489954826, 97721069935, 1369150432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
