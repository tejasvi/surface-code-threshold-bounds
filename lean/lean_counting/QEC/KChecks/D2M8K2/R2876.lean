import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11504 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11504 = true := by
  decide +kernel

theorem tot11504 : totK PD2M8K2 D2M8K2.t11504 = [0, 166517582303, 396893380184, 235808337997, 90528899455, 6690617053, 0, 0] := by
  decide +kernel

theorem rows11505 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11505 = true := by
  decide +kernel

theorem tot11505 : totK PD2M8K2 D2M8K2.t11505 = [0, 179637077310, 467035107962, 241317144647, 15265226342, 0, 0, 0] := by
  decide +kernel

theorem rows11506 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11506 = true := by
  decide +kernel

theorem tot11506 : totK PD2M8K2 D2M8K2.t11506 = [0, 67666276829, 322470383602, 401770842130, 86835170398, 1164319620, 0, 0] := by
  decide +kernel

theorem rows11507 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11507 = true := by
  decide +kernel

theorem tot11507 : totK PD2M8K2 D2M8K2.t11507 = [0, 0, 210009958009, 485862403855, 173469920218, 9404247146, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
