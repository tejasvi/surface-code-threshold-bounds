import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2704 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2704 = true := by
  decide +kernel

theorem tot2704 : totK PD2M8K2 D2M8K2.t2704 = [0, 88383717769, 359199877620, 366447205405, 72171938702, 1178750802, 0, 0] := by
  decide +kernel

theorem rows2705 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2705 = true := by
  decide +kernel

theorem tot2705 : totK PD2M8K2 D2M8K2.t2705 = [0, 0, 256714531167, 489447979433, 156886130179, 8470662040, 0, 0] := by
  decide +kernel

theorem rows2706 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2706 = true := by
  decide +kernel

theorem tot2706 : totK PD2M8K2 D2M8K2.t2706 = [0, 111928164580, 337760429383, 327150974932, 89072763789, 3546687146, 0, 0] := by
  decide +kernel

theorem rows2707 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2707 = true := by
  decide +kernel

theorem tot2707 : totK PD2M8K2 D2M8K2.t2707 = [0, 188917697825, 442198251701, 252852912081, 29189528148, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
