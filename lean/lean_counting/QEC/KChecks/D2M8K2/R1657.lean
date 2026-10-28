import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6628 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6628 = true := by
  decide +kernel

theorem tot6628 : totK PD2M8K2 D2M8K2.t6628 = [0, 0, 229156405063, 493622118569, 165110559106, 7163174326, 0, 0] := by
  decide +kernel

theorem rows6629 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6629 = true := by
  decide +kernel

theorem tot6629 : totK PD2M8K2 D2M8K2.t6629 = [0, 0, 171556667099, 448975388945, 211468297731, 14537497624, 0, 0] := by
  decide +kernel

theorem rows6630 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6630 = true := by
  decide +kernel

theorem tot6630 : totK PD2M8K2 D2M8K2.t6630 = [0, 0, 74846639311, 358979619281, 344233679356, 64287653492, 1209030869, 0] := by
  decide +kernel

theorem rows6631 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6631 = true := by
  decide +kernel

theorem tot6631 : totK PD2M8K2 D2M8K2.t6631 = [0, 0, 85305807607, 436784118321, 304175781018, 24904534848, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
