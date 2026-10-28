import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1992 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1992 = true := by
  decide +kernel

theorem tot1992 : totK PD2M8K2 D2M8K2.t1992 = [0, 0, 158419668946, 471550672311, 250162669102, 13569089951, 0, 0] := by
  decide +kernel

theorem rows1993 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1993 = true := by
  decide +kernel

theorem tot1993 : totK PD2M8K2 D2M8K2.t1993 = [0, 0, 182177750161, 453671625181, 267660785147, 26667239743, 0, 0] := by
  decide +kernel

theorem rows1994 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1994 = true := by
  decide +kernel

theorem tot1994 : totK PD2M8K2 D2M8K2.t1994 = [0, 0, 171714689483, 457203767390, 245928646488, 15534055262, 0, 0] := by
  decide +kernel

theorem rows1995 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1995 = true := by
  decide +kernel

theorem tot1995 : totK PD2M8K2 D2M8K2.t1995 = [0, 0, 0, 287579741705, 476424945466, 118845542540, 4031931762, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
