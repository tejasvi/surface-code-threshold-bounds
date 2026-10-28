import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2440 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2440 = true := by
  decide +kernel

theorem tot2440 : totK PD2M8K2 D2M8K2.t2440 = [0, 198548062595, 490337265333, 210323696330, 6543040663, 0, 0, 0] := by
  decide +kernel

theorem rows2441 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2441 = true := by
  decide +kernel

theorem tot2441 : totK PD2M8K2 D2M8K2.t2441 = [149668319793, 357650440434, 282391063551, 114830985014, 6804944647, 0, 0, 0] := by
  decide +kernel

theorem rows2442 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2442 = true := by
  decide +kernel

theorem tot2442 : totK PD2M8K2 D2M8K2.t2442 = [166806487989, 438202095438, 284410870142, 30503186154, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2443 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2443 = true := by
  decide +kernel

theorem tot2443 : totK PD2M8K2 D2M8K2.t2443 = [106283859189, 418649253893, 330610380863, 36143772961, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
